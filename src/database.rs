use std::borrow::Cow;

use dashmap::DashMap;
use ethnum::U256;

use crate::{
    FullProof, Hashed,
    error::SmtError,
    gc::GcSnapshot,
    lowlevel::{ExplodedHexary, RawNode},
    singleton_smt_root,
};

/// Trait that implements a thread-safe, concurrent low-level content addressed store.
pub trait NodeStore: Send + Sync + 'static {
    /// Gets a block by hash.
    fn get(&self, key: &[u8]) -> Result<Option<Cow<'_, [u8]>>, SmtError>;

    /// Inserts a block and its hash.
    fn insert(&self, key: &[u8], value: &[u8]) -> Result<(), SmtError>;
}

/// An in-memory NodeStore.
#[derive(Default, Debug)]
pub struct InMemoryStore(DashMap<Vec<u8>, Vec<Vec<u8>>>);

impl NodeStore for InMemoryStore {
    fn get(&self, key: &[u8]) -> Result<Option<Cow<'_, [u8]>>, SmtError> {
        let val: Option<_> = (|| {
            let r = self.0.get(key)?;
            let r: &[u8] = r.last()?.as_slice();
            // safety: because we never delete anything, r can never be a use-after-free.
            Some(Cow::Borrowed(unsafe { std::mem::transmute(r) }))
        })();
        Ok(val)
    }

    fn insert(&self, key: &[u8], value: &[u8]) -> Result<(), SmtError> {
        let mut r = self.0.entry(key.to_owned()).or_default();
        r.push(value.to_owned());
        Ok(())
    }
}

/// A SMT tree stored in some database.
#[derive(Debug)]
pub struct Tree<'a, C: NodeStore> {
    snap: GcSnapshot<'a, C>,
    ptr: Hashed,
}

impl<'a, C: NodeStore> Clone for Tree<'a, C> {
    fn clone(&self) -> Self {
        Self {
            snap: self.snap.clone(),
            ptr: self.ptr.clone(),
        }
    }
}

impl<'a, C: NodeStore> Tree<'a, C> {
    /// Opens a tree pointing at a particular hash.
    pub fn open(store: &'a C, ptr: Hashed) -> Self {
        Self {
            snap: GcSnapshot::new(store),
            ptr,
        }
    }

    /// Opens an empty tree.
    pub fn empty(store: &'a C) -> Self {
        Self {
            snap: GcSnapshot::new(store),
            ptr: [0; 32],
        }
    }

    /// Commits the tree back to storage, returning the new root hash.
    pub fn commit(self) -> Result<Hashed, SmtError> {
        self.snap.gc_commit(self.ptr)?;
        Ok(self.ptr)
    }

    /// Obtains the value associated with the given key.
    pub fn get(&self, key: Hashed) -> Result<Cow<'_, [u8]>, SmtError> {
        self.get_value(key, None)
    }

    /// Obtains the root hash.
    pub fn root_hash(&self) -> Hashed {
        self.ptr
    }

    /// Obtains the value associated with the given key, along with an associated proof.
    pub fn get_with_proof(&self, key: Hashed) -> Result<(Cow<'_, [u8]>, FullProof), SmtError> {
        let mut p = Vec::new();
        let res = self.get_value(key, Some(&mut |h| p.push(h)))?;
        // log::trace!("proof: {:?}", p);
        p.resize(256, Default::default());
        let p = FullProof(p);
        assert!(p.verify(self.ptr, key, &res));
        Ok((res, p))
    }

    /// Low-level getting function.
    fn get_value(
        &self,
        key: Hashed,
        mut on_proof_frag: Option<&mut dyn FnMut(Hashed)>,
    ) -> Result<Cow<'_, [u8]>, SmtError> {
        // Imperative style traversal, starting from the root
        let mut ptr = self.ptr;
        let mut ikey = U256::from_be_bytes(key);
        for depth in 0.. {
            log::trace!("get at depth {}, ikey {}", depth, ikey);
            match self.snap.get_node(ptr)? {
                Some(RawNode::Single(height, single_key, data)) => {
                    let mut single_ikey =
                        truncate_shl(U256::from_be_bytes(single_key), (64 - (height as u32)) * 4);
                    if ikey == single_ikey {
                        return Ok(data);
                    } else {
                        if let Some(opf) = on_proof_frag.as_mut() {
                            let mut diverging_height = (height as usize) * 4;
                            log::trace!(
                                "finding divergent at with single_ikey = {}, ikey = {}, single_key = {}, key = {}",
                                single_ikey,
                                ikey,
                                hex::encode(&single_key),
                                hex::encode(&key)
                            );
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
                            opf(singleton_smt_root(diverging_height - 1, single_key, &data));
                        }
                        return Ok(Cow::Owned(Vec::new()));
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
                    ptr = gggc[key_frag];
                }
                None => return Ok(Cow::Owned(Vec::new())),
            }
            // zero top four bits
            ikey = rm4(ikey)
        }
        unreachable!()
    }

    /// Insert a key-value pair, returning a new value.
    #[must_use]
    pub fn with(self, key: Hashed, value: &[u8]) -> Result<Self, SmtError> {
        self.with_binding(key, U256::from_be_bytes(key), value, 64)
    }

    /// Debug graphviz
    pub fn debug_graphviz(&self) {
        todo!()
    }

    /// Low-level insertion function
    fn with_binding(
        self,
        key: Hashed,
        ikey: U256,
        value: &[u8],
        rec_height: u8,
    ) -> Result<Self, SmtError> {
        log::trace!(
            "RECURSE DOWN  {} {} {}",
            hex::encode(&key),
            hex::encode(ikey.to_be_bytes()),
            rec_height
        );

        // Recursive-style
        let new_node = match self.snap.get_node(self.ptr)? {
            Some(RawNode::Single(height, single_key, node_value)) => {
                assert!(height == rec_height);
                let single_ikey = truncate_shl(
                    U256::from_be_bytes(single_key),
                    (64 - (rec_height as u32)) * 4,
                );
                if ikey == single_ikey {
                    if value.is_empty() {
                        return Ok(Self {
                            snap: self.snap,
                            ptr: Hashed::default(),
                        });
                    }
                    log::trace!(
                        "duplicate key, so simply creating a new single key {}",
                        hex::encode(key)
                    );
                    RawNode::Single(height, key, Cow::Owned(value.to_vec()))
                } else {
                    // see whether the two keys differ in their first 4 bits
                    let single_ifrag = single_ikey.wrapping_shr(252).as_usize();
                    let key_ifrag = ikey.wrapping_shr(252).as_usize();
                    if single_ifrag != key_ifrag {
                        // then it's relatively easy: we create two single-nodes then put them in the right GGGC.
                        let key_foo = Self {
                            snap: self.snap.clone(),
                            ptr: Hashed::default(),
                        }
                        .with_binding(
                            key,
                            rm4(ikey),
                            value,
                            rec_height - 1,
                        )?;
                        let single_foo = Self {
                            snap: self.snap.clone(),
                            ptr: Hashed::default(),
                        }
                        .with_binding(
                            single_key,
                            rm4(single_ikey),
                            &node_value,
                            rec_height - 1,
                        )?;
                        let mut gggc: [Hashed; 16] = Default::default();
                        gggc[single_ifrag] = single_foo.ptr;
                        gggc[key_ifrag] = key_foo.ptr;
                        RawNode::Hexary(height, 2, gggc.into())
                    } else {
                        // we need to recurse down a height
                        let lower = RawNode::Single(height - 1, single_key, node_value);
                        let lower_ptr = lower.hash();
                        self.snap.insert(lower_ptr, lower);
                        let lower = Self {
                            snap: self.snap.clone(),
                            ptr: lower_ptr,
                        }
                        .with_binding(
                            key,
                            rm4(ikey),
                            value,
                            rec_height - 1,
                        )?;
                        let mut gggc: [Hashed; 16] = Default::default();
                        gggc[single_ifrag] = lower.ptr;
                        RawNode::Hexary(height, 2, gggc.into())
                    }
                }
            }
            Some(RawNode::Hexary(height, count, mut gggc)) => {
                assert!(height == rec_height);
                // figure out which gggc to "mutate"
                let key_frag = (ikey.wrapping_shr(252)).as_usize();
                let to_change = &mut gggc[key_frag];
                let sub_tree = Self {
                    snap: self.snap.clone(),
                    ptr: *to_change,
                };
                let pre_count = sub_tree.count()?;
                let sub_tree = sub_tree.with_binding(key, rm4(ikey), value, rec_height - 1)?;
                *to_change = sub_tree.ptr;
                RawNode::Hexary(
                    height,
                    if sub_tree.count()? > pre_count {
                        count + (sub_tree.count()? - pre_count)
                    } else {
                        count - (pre_count - sub_tree.count()?)
                    },
                    gggc,
                )
            }
            None => RawNode::Single(rec_height, key, Cow::Owned(value.to_vec())),
        };
        let ptr = new_node.hash();
        self.snap.insert(ptr, new_node);
        Ok(Self {
            snap: self.snap,
            ptr,
        })
    }

    /// Returns the number of elements in the mapping.
    pub fn count(&self) -> Result<u64, SmtError> {
        Ok(self
            .snap
            .get_node(self.ptr)?
            .map(|r| r.count())
            .unwrap_or_default())
    }
}

fn rm4(i: U256) -> U256 {
    (i & !(U256::from(0b1111u32) << U256::from(252u32))) << 4
}

fn truncate_shl(i: U256, offset: u32) -> U256 {
    if offset >= 256 {
        U256::ZERO
    } else {
        i.reverse_bits().wrapping_shr(offset).reverse_bits()
    }
}

fn high4(i: U256) -> usize {
    i.wrapping_shr(252).as_usize()
}

#[cfg(test)]
mod tests {
    use ethnum::U256;

    use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

    use super::*;

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
        let store = InMemoryStore::default();
        let mut empty = Tree::empty(&store);
        for (k, v) in bindings.iter() {
            empty = empty.with(*k, v).unwrap();
        }
        assert_eq!(empty.count().unwrap(), count);

        let _ = empty.get_with_proof([0; 32]);
        bindings
            .par_iter()
            .for_each(|(k, v)| assert_eq!(empty.get_with_proof(*k).unwrap().0, v.as_slice()));
        // for (i, (k, _)) in bindings.into_iter().enumerate() {
        //     assert_eq!(empty.count().unwrap(), count - (i as u64));
        //     empty = empty.with(k, &[]).unwrap();
        // }

        empty.commit().unwrap();
        eprintln!("{} elements in database", store.0.len());
    }
}
