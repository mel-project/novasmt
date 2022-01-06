use std::{borrow::Cow, sync::Arc};

use dashmap::DashMap;
use ethnum::U256;
use genawaiter::rc::Gen;
use replace_with::replace_with_or_abort;

use crate::{
    lowlevel::{ExplodedHexary, RawNode},
    singleton_smt_root, FullProof, Hashed,
};

/// Trait that implements a thread-safe, concurrent low-level content addressed store.
pub trait ContentAddrStore: Send + Sync {
    /// Gets a block by hash.
    fn get<'a>(&'a self, key: &[u8]) -> Option<Cow<'a, [u8]>>;

    /// Inserts a block and its hash.
    fn insert(&self, key: &[u8], value: &[u8]);

    /// Helper function to realize a hash as a raw node. May override if caching, etc makes sense, but the default impl is reasonable in most cases.
    fn realize<'a>(&'a self, hash: Hashed) -> Option<RawNode<'a>> {
        if hash == [0; 32] {
            None
        } else {
            let gotten = self.get(&hash).expect("dangling pointer");
            let view = match gotten {
                Cow::Borrowed(gotten) => RawNode::try_from_slice(gotten).expect("corrupt node"),
                Cow::Owned(gotten) => RawNode::try_from_slice(&gotten)
                    .expect("corrupt node")
                    .into_owned(),
            };
            Some(view)
        }
    }
}

/// An in-memory ContentAddrStore.
#[derive(Default, Debug)]
pub struct InMemoryCas(DashMap<Vec<u8>, Vec<Vec<u8>>>);

impl ContentAddrStore for InMemoryCas {
    fn get(&self, key: &[u8]) -> Option<Cow<'_, [u8]>> {
        let r = self.0.get(key)?;
        let r: &[u8] = r.last()?.as_slice();
        // safety: because we never delete anything, r can never be a use-after-free.
        Some(Cow::Borrowed(unsafe { std::mem::transmute(r) }))
    }

    fn insert(&self, key: &[u8], value: &[u8]) {
        let mut r = self.0.entry(key.to_owned()).or_default();
        r.push(value.to_owned());
    }
}

/// A database full of SMTs. Generic over where the SMTs are actually stored.
#[derive(Debug)]
pub struct Database<C: ContentAddrStore> {
    cas: Arc<C>,
}

impl<C: ContentAddrStore> Database<C> {
    /// Create a new Database.
    pub fn new(cas: C) -> Self {
        Self { cas: cas.into() }
    }

    /// Obtain a new tree rooted at the given hash.
    pub fn get_tree(&self, hash: Hashed) -> Option<Tree<C>> {
        // self.cas.get(&hash)?;
        Some(Tree {
            cas: self.cas.clone(),
            ptr: hash,
        })
    }

    /// Obtains a reference to the backing store.
    pub fn storage(&self) -> &C {
        &self.cas
    }
}

/// A SMT tree stored in some database.
#[derive(Debug)]
pub struct Tree<C: ContentAddrStore> {
    cas: Arc<C>,
    ptr: Hashed,
}

impl<C: ContentAddrStore> Clone for Tree<C> {
    fn clone(&self) -> Self {
        Self {
            cas: self.cas.clone(),
            ptr: self.ptr,
        }
    }
}

impl<C: ContentAddrStore> Tree<C> {
    /// Clears the whole tree.
    pub fn clear(&mut self) {
        self.ptr = Hashed::default()
    }

    /// Obtains the value associated with the given key.
    pub fn get<'a>(&'a self, key: Hashed) -> Cow<'a, [u8]> {
        self.get_value(key, None)
    }

    /// Obtains the root hash.
    pub fn root_hash(&self) -> Hashed {
        self.ptr
    }

    /// Obtains the value associated with the given key, along with an associated proof.
    pub fn get_with_proof<'a>(&'a self, key: Hashed) -> (Cow<'a, [u8]>, FullProof) {
        let mut p = Vec::new();
        let res = self.get_value(key, Some(&mut |h| p.push(h)));
        log::trace!("proof: {:?}", p);
        p.resize(256, Default::default());
        let p = FullProof(p);
        assert!(p.verify(self.ptr, key, &res));
        (res, p)
    }

    /// Iterates over the elements of the SMT in an arbitrary order.
    pub fn iter(&'_ self) -> impl Iterator<Item = (Hashed, Cow<'_, [u8]>)> + '_ {
        let gen = Gen::new(|co| async move {
            let mut dfs_stack: Vec<Hashed> = vec![self.ptr];
            while let Some(top) = dfs_stack.pop() {
                if top == [0; 32] {
                    continue;
                }
                match self.cas.realize(top).unwrap() {
                    RawNode::Single(_, k, v) => co.yield_((k, v)).await,
                    RawNode::Hexary(_, _, gggc) => {
                        for gggc in gggc {
                            dfs_stack.push(*gggc)
                        }
                    }
                }
            }
        });
        gen.into_iter()
    }

    /// Low-level getting function.
    fn get_value<'a>(
        &'a self,
        key: Hashed,
        mut on_proof_frag: Option<&mut dyn FnMut(Hashed)>,
    ) -> Cow<'a, [u8]> {
        // Imperative style traversal, starting from the root
        let mut ptr = self.ptr;
        let mut ikey = U256::from_be_bytes(key);
        for depth in 0.. {
            log::trace!("get at depth {}", depth);
            match self.cas.realize(ptr) {
                Some(RawNode::Single(height, single_key, data)) => {
                    let mut single_ikey =
                        truncate_shl(U256::from_be_bytes(single_key), (64 - (height as u32)) * 4);
                    if ikey == single_ikey {
                        return data;
                    } else {
                        if let Some(opf) = on_proof_frag.as_mut() {
                            let mut diverging_height = (height as usize) * 4;
                            log::trace!("finding divergent at with single_ikey = {}, ikey = {}, single_key = {}, key = {}", single_ikey, ikey, hex::encode(&single_key), hex::encode(&key));
                            assert!(single_ikey != ikey);
                            while (single_ikey & (U256::ONE << 255)) == (ikey & (U256::ONE << 255))
                            {
                                single_ikey = truncate_shl(single_ikey, 1);
                                ikey = truncate_shl(ikey, 1);
                                diverging_height -= 1;
                                log::trace!(
                                    "diverging_height decreased to {}, single_ikey {}, ikey {}",
                                    diverging_height,
                                    single_ikey,
                                    ikey,
                                );
                                opf(Hashed::default());
                            }
                            assert!(high4(single_ikey) != high4(ikey));
                            opf(singleton_smt_root(diverging_height, single_key, &data));
                        }
                        return Cow::Owned(Vec::new());
                    }
                }
                Some(RawNode::Hexary(_, _, gggc)) => {
                    let key_frag = (ikey.wrapping_shr(252)).as_usize();
                    if let Some(opf) = on_proof_frag.as_mut() {
                        for frag in ExplodedHexary::new(&gggc).proof_frag(key_frag) {
                            opf(frag)
                        }
                    }
                    log::trace!("key frag {} for key {}", key_frag, hex::encode(key));
                    ptr = *gggc[key_frag];
                }
                None => return Cow::Owned(Vec::new()),
            }
            // zero top four bits
            ikey = rm4(ikey)
        }
        unreachable!()
    }

    /// Insert a key-value pair, mutating this value.
    pub fn insert(&mut self, key: Hashed, value: &[u8]) {
        replace_with_or_abort(self, |t| t.with(key, value))
    }

    /// Insert a key-value pair, returning a new value.
    #[must_use]
    pub fn with(self, key: Hashed, value: &[u8]) -> Self {
        self.with_binding(key, U256::from_be_bytes(key), value, 64)
    }

    /// Debug graphviz
    pub fn debug_graphviz(&self) {
        match self.cas.realize(self.ptr) {
            Some(RawNode::Single(_, single_key, _)) => {
                eprintln!(
                    "{:?} [label=\"key {}\"];",
                    hex::encode(&self.ptr),
                    hex::encode(&single_key[..10])
                );
            }
            Some(RawNode::Hexary(_, _, gggc)) => {
                for (i, child) in gggc.iter().enumerate() {
                    if **child != [0u8; 32] {
                        Self {
                            cas: self.cas.clone(),
                            ptr: **child,
                        }
                        .debug_graphviz();
                        eprintln!(
                            "{:?} -> {:?} [label=\"{}\"];",
                            hex::encode(&self.ptr),
                            hex::encode(&child.as_ref()),
                            i
                        );
                        eprintln!(
                            "{:?} [label=\"{}\"];",
                            hex::encode(&self.ptr),
                            hex::encode(&self.ptr[..10]),
                        );
                    }
                }
            }
            None => todo!(),
        }
    }

    /// Low-level insertion function
    fn with_binding(self, key: Hashed, ikey: U256, value: &[u8], rec_height: u8) -> Self {
        log::trace!(
            "RECURSE DOWN  {} {} {}",
            hex::encode(&key),
            hex::encode(ikey.to_be_bytes()),
            rec_height
        );
        // eprintln!(
        //     "with_binding(ptr = {:?}, ikey = {}, value = {:?}, rec_height = {})",
        //     hex::encode(self.ptr),
        //     ikey,
        //     value,
        //     rec_height
        // );
        // Recursive-style
        let new_node = match self.cas.realize(self.ptr) {
            Some(RawNode::Single(height, single_key, node_value)) => {
                assert!(height == rec_height);
                let single_ikey = truncate_shl(
                    U256::from_be_bytes(single_key),
                    (64 - (rec_height as u32)) * 4,
                );
                if ikey == single_ikey {
                    if value.len() == 0 {
                        return Self {
                            cas: self.cas,
                            ptr: Hashed::default(),
                        };
                    }
                    log::trace!(
                        "duplicate key, so simply creating a new single key {}",
                        hex::encode(key)
                    );
                    RawNode::Single(height, key, Cow::Borrowed(value))
                } else {
                    // see whether the two keys differ in their first 4 bits
                    let single_ifrag = single_ikey.wrapping_shr(252).as_usize();
                    let key_ifrag = ikey.wrapping_shr(252).as_usize();
                    if single_ifrag != key_ifrag {
                        // then it's relatively easy: we create two single-nodes then put them in the right GGGC.
                        let key_foo = Self {
                            cas: self.cas.clone(),
                            ptr: Hashed::default(),
                        }
                        .with_binding(
                            key,
                            rm4(ikey),
                            value,
                            rec_height - 1,
                        );
                        let single_foo = Self {
                            cas: self.cas.clone(),
                            ptr: Hashed::default(),
                        }
                        .with_binding(
                            single_key,
                            rm4(single_ikey),
                            &node_value,
                            rec_height - 1,
                        );
                        let mut gggc: [Cow<'static, Hashed>; 16] = Default::default();
                        gggc[single_ifrag] = Cow::Owned(single_foo.ptr);
                        gggc[key_ifrag] = Cow::Owned(key_foo.ptr);
                        RawNode::Hexary(height, 2, gggc)
                    } else {
                        // we need to recurse down a height
                        let lower = RawNode::Single(height - 1, single_key, node_value);
                        let lower_ptr = lower.hash();
                        self.cas.insert(&lower_ptr, &lower.to_bytes());
                        let lower = Self {
                            cas: self.cas.clone(),
                            ptr: lower_ptr,
                        }
                        .with_binding(
                            key,
                            rm4(ikey),
                            value,
                            rec_height - 1,
                        );
                        let mut gggc: [Cow<'static, Hashed>; 16] = Default::default();
                        gggc[single_ifrag] = Cow::Owned(lower.ptr);
                        RawNode::Hexary(height, 2, gggc)
                    }
                }
            }
            Some(RawNode::Hexary(height, count, mut gggc)) => {
                assert!(height == rec_height);
                // figure out which gggc to "mutate"
                let key_frag = (ikey.wrapping_shr(252)).as_usize();
                let to_change = &mut gggc[key_frag];
                let sub_tree = Self {
                    cas: self.cas.clone(),
                    ptr: **to_change,
                };
                let pre_count = sub_tree.count();
                let sub_tree = sub_tree.with_binding(key, rm4(ikey), value, rec_height - 1);
                *to_change = Cow::Owned(sub_tree.ptr);
                RawNode::Hexary(
                    height,
                    if sub_tree.count() > pre_count {
                        count + (sub_tree.count() - pre_count)
                    } else {
                        count - (pre_count - sub_tree.count())
                    },
                    gggc,
                )
            }
            None => RawNode::Single(rec_height, key, Cow::Owned(value.to_vec())),
        };
        let ptr = new_node.hash();
        self.cas.insert(&ptr, &new_node.to_bytes());
        Self { cas: self.cas, ptr }
    }

    /// Returns the number of elements in the mapping.
    pub fn count(&self) -> u64 {
        self.cas
            .realize(self.ptr)
            .map(|r| r.count())
            .unwrap_or_default()
    }

    /// Returns a reference o the underlying backing storage.
    pub fn storage(&self) -> &C {
        &self.cas
    }
}

fn rm4(i: U256) -> U256 {
    (i & !(U256::from(0b1111u32) << U256::from(252u32))) << 4
}

fn truncate_shl(i: U256, offset: u32) -> U256 {
    i.reverse_bits().wrapping_shr(offset).reverse_bits()
}

fn high4(i: U256) -> usize {
    i.wrapping_shr(252).as_usize()
}

#[cfg(test)]
mod tests {
    use dashmap::DashMap;
    use ethnum::U256;
    use quickcheck_macros::quickcheck;
    use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

    use crate::Hashed;

    use super::*;

    #[quickcheck]
    fn rmhigh(a: u128, b: u128) -> bool {
        let t = U256::from(a) * U256::from(b);
        (rm4(t) >> 4) | U256::from(high4(t) as u8) << 252 == t
    }

    #[quickcheck]
    fn trushl(a: u128, b: u128) -> bool {
        let t = U256::from(a) * U256::from(b);
        truncate_shl(t, 4) == rm4(t)
    }

    #[test]
    fn rmhigh_one() {
        let t = 1u8.into();
        assert_eq!((rm4(t) >> 4) | U256::from(high4(t) as u8) << 252, t);
    }

    #[test]
    fn trushl_one() {
        let t = 1u8.into();
        assert_eq!(truncate_shl(t, 4), rm4(t));
    }

    #[test]
    fn simple_insertion() {
        let count = 100u64;
        let bindings = (0..count)
            .map(|i| {
                (
                    *blake3::hash(format!("key-{}", i).as_bytes()).as_bytes(),
                    format!("key-{}", i).as_bytes().to_vec(),
                )
            })
            .collect::<Vec<_>>();
        let db = Database::new(InMemoryCas::default());
        let mut empty = db.get_tree(Hashed::default()).unwrap();
        for (k, v) in bindings.iter() {
            empty = empty.with(*k, &v);
        }
        assert_eq!(empty.count(), count);
        // empty.debug_graphviz();
        let _ = empty.get_with_proof([0; 32]);
        empty.insert([0; 32], b"hello world");
        let _ = empty.get_with_proof([0; 32]);
        eprintln!("{} elements in database", db.storage().0.len());
        bindings
            .par_iter()
            .for_each(|(k, v)| assert_eq!(empty.get_with_proof(*k).0, v.as_slice()));
        for (i, (k, _)) in bindings.into_iter().enumerate() {
            assert_eq!(empty.count(), count - (i as u64));
            empty = empty.with(k, &[]);
        }
    }
}
