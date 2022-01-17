use bitvec::prelude::*;
use lru::LruCache;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::io::Read;

use crate::{
    hash::{hash_data, hash_node},
    Hashed,
};

pub(crate) fn key_to_path(
    key: &'_ Hashed,
) -> impl Iterator<Item = bool> + ExactSizeIterator + DoubleEndedIterator + '_ {
    // let mut toret = [false; 256];
    // // enumerate each byte
    // for (i, k_i) in key.iter().enumerate() {
    //     // walk through the bits
    //     for j in 0..8 {
    //         toret[i * 8 + j] = k_i & (MSB_SET >> j) != 0;
    //     }
    // }
    // toret
    let bslice = BitSlice::<Msb0, _>::from_slice(key).unwrap();
    bslice.iter().by_val()
}

fn singleton_smt_roots(key: Hashed, val: &[u8], out: &mut [Hashed]) {
    let mut rpath = key_to_path(&key).collect::<Vec<_>>();
    rpath.reverse();
    out[0] = hash_data(val);
    for i in 0..rpath.len() {
        out[i + 1] = if rpath[i] {
            hash_node([0; 32], out[i])
        } else {
            hash_node(out[i], [0; 32])
        }
    }
}

/// Returns the root hash of a one-element SMT with the given key and value.
pub(crate) fn singleton_smt_root(height: usize, key: Hashed, val: &[u8]) -> Hashed {
    thread_local! {
        static CACHE: std::cell::RefCell<lru::LruCache<(Hashed,Vec<u8>), [Hashed; 258], std::hash::BuildHasherDefault<rustc_hash::FxHasher>>>   = std::cell::RefCell::new(LruCache::with_hasher(1024, Default::default()));
    }
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if let Some(val) = cache.get(&(key, val.to_vec())) {
            val[height]
        } else {
            let mut buf = [Hashed::default(); 258];
            singleton_smt_roots(key, val, &mut buf);
            cache.put((key, val.to_vec()), buf);
            buf[height]
        }
    })
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A full proof with 256 levels.
pub struct FullProof(pub Vec<Hashed>);

impl FullProof {
    /// Compresses the proof to a serializable form.
    pub fn compress(&self) -> CompressedProof {
        let FullProof(proof_nodes) = self;
        assert_eq!(proof_nodes.len(), 256);
        // build bitmap
        let mut bitmap = bitvec![Msb0, u8; 0; 256];
        for (i, pn) in proof_nodes.iter().enumerate() {
            if *pn == [0u8; 32] {
                bitmap.set(i, true);
            }
        }
        let mut bitmap_slice = bitmap.into_vec();
        for pn in proof_nodes.iter() {
            if *pn != [0u8; 32] {
                bitmap_slice.extend_from_slice(pn);
            }
        }
        CompressedProof(bitmap_slice)
    }

    /// Verifies that this merkle branch is a valid proof of inclusion or non-inclusion. To check proofs of non-inclusion, set val to the empty vector.
    pub fn verify(&self, root: Hashed, key: Hashed, val: &[u8]) -> bool {
        assert_eq!(self.0.len(), 256);
        self.verify_pure(root, key, val)
    }

    fn verify_pure(&self, root: Hashed, key: Hashed, val: &[u8]) -> bool {
        let path = key_to_path(&key).collect::<Vec<_>>();
        let mut my_root = hash_data(val);
        for (&level, &direction) in self.0.iter().zip(path.iter()).rev() {
            if direction {
                // log::trace!(
                //     "verify: my_root <- hash_node({}, {})",
                //     hex::encode(&level),
                //     hex::encode(&my_root)
                // );
                my_root = hash_node(level, my_root)
            } else {
                // log::trace!(
                //     "verify: my_root <- hash_node({}, {})",
                //     hex::encode(&my_root),
                //     hex::encode(&level)
                // );
                my_root = hash_node(my_root, level)
            }
        }
        root == my_root
    }
}

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Serialize, Deserialize)]
/// A compressed proof.
pub struct CompressedProof(pub Vec<u8>);

impl CompressedProof {
    /// Decompresses a compressed proof. Returns None if the format is invalid.
    pub fn decompress(&self) -> Option<FullProof> {
        let b = &self.0;
        if b.len() < 32 || b.len() % 32 != 0 {
            return None;
        }
        let bitmap = BitVec::<Msb0, u8>::from_vec(b[..32].to_vec());
        let mut b = &b[32..];
        let mut out = Vec::new();
        // go through the bitmap. if b is set, insert a zero. otherwise, take 32 bytes from b. if b runs out, we are dead.
        for is_zero in bitmap {
            if is_zero {
                out.push([0u8; 32])
            } else {
                let mut buf = [0; 32];
                b.read_exact(&mut buf).ok()?;
                out.push(buf);
            }
        }
        Some(FullProof(out))
    }
}
