use std::{collections::HashSet, sync::Arc};

use bitvec::{order::Msb0, slice::BitSlice};
use bytes::Bytes;
use dashmap::DashMap;

use crate::{
    hash::hash_node, key_to_path, singleton_smt_root, BackendDB, BackendNode, FullProof, Hashed,
};

/// A sparse Merkle tree mapping from keys to values.
///
/// Because SMTs are inherently content-addressed and persistent, the [Clone] implementation is cheap.
#[derive(Clone)]
pub struct Tree {
    /// Guards the root of the on-disk tree that this tree is based off of, so that it is not prematurely deleted.
    _guard: Arc<KeyGuard>,
    rcmap: RefcountMap,
    backend: Arc<dyn BackendDB>,
    /// *New* nodes that this tree has
    delta: im::HashMap<Hashed, BackendNode>,
    my_root: Hashed,

    gc_watermark: usize,
}

impl Tree {
    /// Gets the node with the given hash.
    fn get_bnode(&self, hash: Hashed) -> Option<BackendNode> {
        self.delta
            .get(&hash)
            .cloned()
            .or_else(|| self.backend.get(hash))
    }

    /// Inserts a bnode.
    fn insert_bnode(&mut self, hash: Hashed, bnode: BackendNode) {
        if hash == [0; 32] {
            return;
        }
        self.delta.insert(hash, bnode);
    }

    /// Get the root hash.
    pub fn root_hash(&self) -> Hashed {
        self.my_root
    }

    /// Obtains the value bound to this key, along with the proof.
    pub fn get_with_proof(&self, needle: Hashed) -> (Bytes, FullProof) {
        let mut current_hash = self.my_root;
        let mut proof_hashes = Vec::with_capacity(256);
        for bit in key_to_path(&needle) {
            match self.get_bnode(current_hash) {
                None => {
                    // the remainder of the proof is all zeros
                    while proof_hashes.len() < 256 {
                        proof_hashes.push([0; 32]);
                    }
                    return (Bytes::new(), FullProof(proof_hashes));
                }
                Some(BackendNode::Internal(left, right)) => {
                    if bit {
                        current_hash = right;
                        proof_hashes.push(left);
                    } else {
                        current_hash = left;
                        proof_hashes.push(right);
                    }
                }
                Some(BackendNode::Leaf(key, val)) => {
                    // if this is the correct key/value, return it
                    if key == needle {
                        // the remainder of the proof is all zeros
                        while proof_hashes.len() < 256 {
                            proof_hashes.push([0; 32]);
                        }
                        return (val, FullProof(proof_hashes));
                    } else {
                        // then we find the first *diverging* bit in the key
                        let diverging_bit_idx = {
                            let leaf_key_bits = BitSlice::<Msb0, _>::from_slice(&key).unwrap();
                            let needle_bits = BitSlice::<Msb0, _>::from_slice(&needle).unwrap();
                            (0usize..)
                                .find(|i| leaf_key_bits[*i] != needle_bits[*i])
                                .unwrap()
                        };
                        // first fill with zeros
                        while proof_hashes.len() < 256 {
                            proof_hashes.push([0; 32]);
                        }
                        // at the divergence point, we *don't* have a zero. Instead, we have what would be the hash of a one-element SMT at that height
                        proof_hashes[diverging_bit_idx] =
                            singleton_smt_root(255 - diverging_bit_idx, key, &val);
                        return (Bytes::new(), FullProof(proof_hashes));
                    }
                }
            }
        }
        panic!("reached bottom of tree without finding a leaf or None")
    }

    /// Sets a key/value pair.
    pub fn insert(&mut self, key: Hashed, value: Bytes) {
        // special case: we are the empty tree
        if self.my_root == [0; 32] {
            let root = singleton_smt_root(256, key, &value);
            let leaf = BackendNode::Leaf(key, value);
            self.insert_bnode(root, leaf);
            self.my_root = root;
            return;
        }
        // the path we took, consisting entirely of contiguous Internals
        let mut path_to_rewrite: Vec<BackendNode> = vec![self.get_bnode(self.my_root).unwrap()];
        // the leaf hash. we use this to "fix" the path after the loop.
        let mut leaf_hash = [0; 32];
        for (idx, bit) in key_to_path(&key).enumerate() {
            let popped = path_to_rewrite.pop().unwrap();
            match popped.clone() {
                BackendNode::Internal(left, right) => {
                    if bit && right != [0; 32] {
                        path_to_rewrite.push(popped);
                        path_to_rewrite.push(self.get_bnode(right).unwrap())
                    } else if !bit && left != [0; 32] {
                        path_to_rewrite.push(popped);
                        path_to_rewrite.push(self.get_bnode(left).unwrap())
                    } else {
                        // create new Leaf
                        let new_bnode_hash = singleton_smt_root(255 - idx, key, &value);
                        let new_bnode = BackendNode::Leaf(key, value);
                        self.insert_bnode(new_bnode_hash, new_bnode);
                        leaf_hash = new_bnode_hash;
                        path_to_rewrite.push(popped);
                        break;
                    }
                }
                BackendNode::Leaf(leaf_key, leaf_value) => {
                    if leaf_key == key && leaf_value == value {
                        return;
                    }
                    if leaf_key == key {
                        let new_leaf_hash = singleton_smt_root(256 - idx, key, &value);
                        self.insert_bnode(new_leaf_hash, BackendNode::Leaf(leaf_key, value));
                        break;
                    }
                    // this case is rather subtle.
                    // if we're not at the "fork" yet, the current bit will match that of the leaf key.
                    // in that case, we don't break immediately. instead, we synthesize an internal node and keep on rolling.
                    // this is a rare case (chance halves every round, so it's okay if this case is expensive)
                    let diverging_bit_idx = {
                        let leaf_key_bits = BitSlice::<Msb0, _>::from_slice(&leaf_key).unwrap();
                        let key = BitSlice::<Msb0, _>::from_slice(&key).unwrap();
                        (0usize..).find(|i| leaf_key_bits[*i] != key[*i]).unwrap()
                    };
                    if idx == diverging_bit_idx {
                        // we are at the fork. this means that we can safely make a 2-SMT, knowing that the root will have two nonzero children.
                        // this 2-SMT is then put in the path to rewrite.
                        let existing_leaf_new_hash =
                            singleton_smt_root(255 - idx, leaf_key, &leaf_value);
                        self.insert_bnode(
                            existing_leaf_new_hash,
                            BackendNode::Leaf(leaf_key, leaf_value),
                        );
                        let new_leaf_hash = singleton_smt_root(255 - idx, key, &value);
                        self.insert_bnode(new_leaf_hash, BackendNode::Leaf(key, value));
                        if bit {
                            path_to_rewrite
                                .push(BackendNode::Internal(existing_leaf_new_hash, new_leaf_hash));
                        } else {
                            path_to_rewrite
                                .push(BackendNode::Internal(new_leaf_hash, existing_leaf_new_hash));
                        }
                        leaf_hash = new_leaf_hash;
                        break;
                    } else {
                        // not at the fork yet.
                        // we can push a completely dummy internal node because the next step will fix it.
                        path_to_rewrite.push(BackendNode::Internal([0; 32], [0; 32]));
                        path_to_rewrite.push(popped);
                    }
                }
            }
        }

        // at this point, path_to_rewrite has at most 1 wrong child at each level. we go through it in reverse to correct it.
        for (bit, to_rewrite) in key_to_path(&key).zip(path_to_rewrite.iter_mut()).rev() {
            match to_rewrite {
                BackendNode::Internal(left, right) => {
                    if bit {
                        *right = leaf_hash;
                    } else {
                        *left = leaf_hash;
                    }
                    leaf_hash = hash_node(*left, *right);
                    self.insert_bnode(leaf_hash, BackendNode::Internal(*left, *right));
                }
                _ => panic!("rewriting encountered non-Internal node"),
            }
        }

        // we rewrite the root
        self.my_root = leaf_hash;
        // garbage collect
        self.garbage_collect();
    }

    /// Saves this tree to disk.
    pub fn save(&mut self) {
        self.gc_watermark = 0;
        self.garbage_collect();
        let pairs = self
            .delta
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect::<Vec<_>>();
        log::trace!("saving {} pairs to disk", pairs.len());
        self.backend.set_batch(&pairs);
        self.delta.clear();
        self._guard = Arc::new(self.rcmap.get_guard(self.my_root));
    }

    /// Garbage-collect the tree if needs be.
    fn garbage_collect(&mut self) {
        if self.delta.len() > self.gc_watermark {
            let old_len = self.delta.len();
            let mut marked = HashSet::new();
            let mut dfs_stack: Vec<Hashed> = vec![self.my_root];
            while let Some(top) = dfs_stack.pop() {
                marked.insert(top);
                if let Some(BackendNode::Internal(left, right)) = self.delta.get(&top) {
                    dfs_stack.push(*left);
                    dfs_stack.push(*right);
                }
            }
            self.delta.retain(|k, _| marked.contains(k));
            log::trace!("garbage collected {} => {}", old_len, self.delta.len());
            self.gc_watermark = self.delta.len() * 2;
        }
    }
}

/// A forest that contains many trees. Can be thought of as a database full of trees. For ergonomics, internally contains an [Arc] and can be freely cloned around.
///
/// Note that the only supported methods are to open and delete trees. To *save* a tree, the [Tree::save] method should be called.
#[derive(Clone)]
pub struct Forest {
    backend: Arc<dyn BackendDB>,
    rcmap: RefcountMap,
}

impl Forest {
    /// Creates a new forest using the given backend DB.
    pub fn new(db: impl BackendDB) -> Self {
        let backend = Arc::new(db);
        Self {
            backend,
            rcmap: RefcountMap::default(),
        }
    }

    /// Opens a tree at the given root hash.
    pub fn open_tree(&self, root_hash: Hashed) -> Option<Tree> {
        if root_hash != [0; 32] {
            self.backend.get(root_hash)?;
        }
        Some(Tree {
            _guard: Arc::new(self.rcmap.get_guard(root_hash)),
            rcmap: self.rcmap.clone(),
            backend: self.backend.clone(),
            delta: Default::default(),
            my_root: root_hash,
            gc_watermark: 100,
        })
    }

    /// Deletes the tree at the given hash. If there are outstanding references to the tree, the deletion will not happen right away.
    pub fn delete_tree(&self, root_hash: Hashed) {
        match self.rcmap.mapping.get_mut(&root_hash) {
            None => {
                // safe to delete right away
                self.backend.delete_root(root_hash);
            }
            Some(mut inner) => {
                // we queue the root on the backend
                self.backend.delete_root_tomorrow(root_hash);
                let backend = self.backend.clone();
                // when no more refs, go ahead and delete
                inner.1.push(scopeguard::guard(
                    (),
                    Box::new(move |_| backend.delete_root(root_hash)),
                ));
            }
        }
    }
}

type Labooyah = Arc<
    DashMap<
        Hashed,
        (
            usize,
            Vec<scopeguard::ScopeGuard<(), Box<dyn FnOnce(()) + Send + Sync>>>,
        ),
    >,
>;

/// A structure that keeps track of hashes mapped to refcounts
#[derive(Default, Clone)]
struct RefcountMap {
    mapping: Labooyah,
}

impl RefcountMap {
    fn get_guard(&self, hash: Hashed) -> KeyGuard {
        let mut rc = self.mapping.entry(hash).or_default();
        rc.0 += 1;
        // when we are getting a new guard, we know that we don't want deletion to happen anymore.
        rc.1.clear();
        KeyGuard {
            hash,
            mapping: self.mapping.clone(),
        }
    }
}

struct KeyGuard {
    hash: Hashed,
    mapping: Labooyah,
}

impl Drop for KeyGuard {
    fn drop(&mut self) {
        let slot = self.mapping.entry(self.hash);
        match slot {
            dashmap::mapref::entry::Entry::Occupied(mut occupied) => {
                let refcount = occupied.get_mut();
                refcount.0 -= 1;
                if refcount.0 == 0 {
                    occupied.remove_entry();
                }
            }
            dashmap::mapref::entry::Entry::Vacant(_) => {
                panic!("refcountmap missing key when keyguard drops")
            }
        }
    }
}
