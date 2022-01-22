use itertools::Itertools;

use crate::{
    hash::{hash_data, hash_node},
    Hashed,
};

/// A structure that holds an in-memory, dense Merkle tree.
pub struct DenseMerkleTree {
    bottom_to_top: Vec<Hashed>,
}

impl DenseMerkleTree {
    /// Creates a new DMT based off of the given slice.
    pub fn new<R: AsRef<[u8]>>(datablocks: &[R]) -> Self {
        let mut btt = vec![];
        // first level: just the hashes
        for blk in datablocks {
            let hash = hash_data(blk.as_ref());
            btt.push(hash);
        }
        // extend to the next power of two with zeroes
        let mut npp = btt.len().next_power_of_two();
        while btt.len() < npp {
            btt.push(Hashed::default())
        }
        // then fill in the other levels
        while npp > 1 {
            // each level is based on the last npp values
            let index_range = btt.len() - npp..btt.len();
            index_range.tuples().for_each(|(a, b)| {
                let a = btt[a];
                let b = btt[b];
                let combined_hash = hash_node(a, b);
                btt.push(combined_hash)
            });
            npp /= 2
        }
        Self { bottom_to_top: btt }
    }

    /// Root hash of the DMT.
    pub fn root_hash(&self) -> Hashed {
        *self.bottom_to_top.last().unwrap()
    }

    /// Obtain a proof for the ith element.
    pub fn proof(&self, mut idx: usize) -> Vec<Hashed> {
        let mut accum = Vec::new();
        // we slice and dice
        let mut ptr = &self.bottom_to_top[..];
        while ptr.len() > 1 {
            let (left_half, right_half) = ptr.split_at(ptr.len() / 2 + 1);
            accum.push(left_half[idx ^ 1]);
            idx >>= 1;
            ptr = right_half
        }
        accum
    }
}

/// Verifies a proof for a dense merkle-tree.
pub fn verify_dense(proof: &[Hashed], root: Hashed, mut idx: usize, leaf: Hashed) -> bool {
    // start from the leaf, go through the bits of idx
    let mut ptr = leaf;
    for elem in proof {
        let bit = idx & 1;
        idx >>= 1;
        if bit > 0 {
            ptr = hash_node(*elem, ptr)
        } else {
            ptr = hash_node(ptr, *elem)
        }
    }
    ptr == root
}

#[cfg(test)]
mod tests {
    use crate::{dense::verify_dense, hash::hash_data};

    use super::DenseMerkleTree;

    #[test]
    fn dense_simple() {
        let vals = [b"hello", b"world", b"fdfef"];
        let mt = DenseMerkleTree::new(&vals);
        dbg!(mt.proof(1));
        assert!(verify_dense(
            &mt.proof(1),
            mt.root_hash(),
            1,
            hash_data(b"world")
        ))
    }
}
