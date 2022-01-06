use std::{borrow::Cow, sync::Arc};

use dashmap::DashMap;
use ethnum::U256;

use crate::{
    lowlevel::{ExplodedHexary, RawNode},
    Hashed,
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

impl ContentAddrStore for DashMap<Vec<u8>, Vec<u8>> {
    fn get(&self, key: &[u8]) -> Option<Cow<'_, [u8]>> {
        Some(Cow::Owned(self.get(key)?.clone()))
    }

    fn insert(&self, key: &[u8], value: &[u8]) {
        self.insert(key.to_owned(), value.to_owned());
    }
}

/// A database full of SMTs.
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
    pub fn backing_store(&self) -> &C {
        &self.cas
    }
}

/// A SMT tree stored in some database.
#[derive(Clone, Debug)]
pub struct Tree<C: ContentAddrStore> {
    cas: Arc<C>,
    ptr: Hashed,
}

impl<C: ContentAddrStore> Tree<C> {
    /// Low-level getting function.
    fn get_value<'a>(
        &'a self,
        key: Hashed,
        mut on_proof_frag: Option<&mut dyn FnMut(Hashed)>,
    ) -> Cow<'a, [u8]> {
        // Imperative style traversal, starting from the root
        let mut ptr = self.ptr;
        let mut ikey = U256::from_be_bytes(key);
        while ikey > 0 {
            match self.cas.realize(ptr) {
                Some(RawNode::Single(_, single_key, data)) => {
                    if key == single_key {
                        return data;
                    } else {
                        todo!("synthesize the correct proof here")
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
                None => todo!(),
            }
            // zero top four bits
            ikey = rm4(ikey)
        }
        Cow::Owned(Vec::new())
    }

    /// Insert a key-value pair, returning a new value.
    #[must_use]
    pub fn with(self, key: Hashed, value: &[u8]) -> Self {
        self.with_binding(key, U256::from_be_bytes(key), value, 64)
    }

    /// Debug graphviz
    fn debug_graphviz(&self) {
        match self.cas.realize(self.ptr) {
            Some(RawNode::Single(_, single_key, data)) => {
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
        log::trace!("RECURSE DOWN  {} {}", hex::encode(&key), ikey);
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
                if key == single_key {
                    RawNode::Single(height, key, node_value)
                } else {
                    // see whether the two keys differ in their first 4 bits
                    let single_ikey = truncate_shl(
                        U256::from_be_bytes(single_key),
                        (64 - (rec_height as u32)) * 4,
                    );
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
                }
                .with_binding(key, rm4(ikey), value, rec_height - 1);
                *to_change = Cow::Owned(sub_tree.ptr);
                RawNode::Hexary(height, count + 1, gggc)
            }
            None => RawNode::Single(rec_height, key, Cow::Owned(value.to_vec())),
        };
        let ptr = new_node.hash();
        self.cas.insert(&ptr, &new_node.to_bytes());
        Self { cas: self.cas, ptr }
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
        let bindings = (0..100)
            .map(|i| {
                (
                    *blake3::hash(format!("key-{}", i).as_bytes()).as_bytes(),
                    format!("key-{}", i).as_bytes().to_vec(),
                )
            })
            .collect::<Vec<_>>();
        let db = Database::new(DashMap::new());
        let mut empty = db.get_tree(Hashed::default()).unwrap();
        for (k, v) in bindings.iter() {
            empty = empty.with(*k, &v);
        }
        // empty.debug_graphviz();
        eprintln!("{} elements in database", db.backing_store().len());
        bindings
            .par_iter()
            .for_each(|(k, v)| assert_eq!(empty.get_value(*k, None), v.as_slice()));
    }
}
