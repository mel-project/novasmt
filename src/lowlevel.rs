use std::{
    borrow::{Borrow, Cow},
    io::Write,
};

use arrayref::array_ref;

use crate::{hash::hash_node, singleton_smt_root, Hashed};

/// A "realized" hexary node, used for generating proofs and such.
#[derive(Clone, Copy)]
pub struct ExplodedHexary {
    root: Hashed,
    children: [Hashed; 2],
    grands: [Hashed; 4],
    great_grands: [Hashed; 8],
    great_great_grands: [Hashed; 16],
}

impl ExplodedHexary {
    /// Create a new exploded hexary.
    pub fn new<H: Borrow<Hashed>>(source: &[H; 16]) -> Self {
        let mut great_great_grands: [Hashed; 16] = Default::default();
        for i in 0..16 {
            great_great_grands[i] = *source[i].borrow()
        }
        let mut great_grands: [Hashed; 8] = Default::default();
        for i in 0..8 {
            great_grands[i] = hash_node(great_great_grands[2 * i], great_great_grands[2 * i + 1]);
        }
        let mut grands: [Hashed; 4] = Default::default();
        for i in 0..4 {
            grands[i] = hash_node(great_grands[2 * i], great_grands[2 * i + 1]);
        }
        let mut children: [Hashed; 2] = Default::default();
        for i in 0..2 {
            children[i] = hash_node(grands[2 * i], grands[2 * i + 1]);
        }
        let root = hash_node(children[0], children[1]);
        Self {
            root,
            children,
            grands,
            great_grands,
            great_great_grands,
        }
    }

    /// Obtain a proof fragment.
    pub fn proof_frag(&self, mut idx: usize) -> [Hashed; 4] {
        let mut toret = [Hashed::default(); 4];
        toret[3] = self.great_great_grands[idx ^ 1];
        idx >>= 1;
        toret[2] = self.great_grands[idx ^ 1];
        idx >>= 1;
        toret[1] = self.grands[idx ^ 1];
        idx >>= 1;
        toret[0] = self.children[idx ^ 1];
        toret
    }
}

/// Low-level, near-zero-copy representation of a hexary-SMT node.
#[derive(Clone, Debug)]
pub enum RawNode<'a> {
    /// Single data block.
    Single(u8, Hashed, Cow<'a, [u8]>),
    /// Height (between 1 and 64), count, and great-grandchildren
    Hexary(u8, u64, Box<[Hashed; 16]>),
}

impl<'a> RawNode<'a> {
    /// Computes the hash of the node.
    pub fn hash(&self) -> Hashed {
        match self {
            RawNode::Single(height, key, value) => {
                singleton_smt_root((*height as usize) * 4, *key, value)
            }
            RawNode::Hexary(_, _, gggc) => ExplodedHexary::new(gggc).root,
        }
    }

    /// Gets the number of nonzero items in the tree rooted at this node.
    pub fn count(&self) -> u64 {
        match self {
            RawNode::Single(_, _, _) => 1,
            RawNode::Hexary(_, c, _) => *c,
        }
    }

    /// Gets the height of the node, returning a number between 0 and 64, inclusive.
    pub fn hex_height(&self) -> u8 {
        match self {
            RawNode::Single(h, _, _) => *h,
            RawNode::Hexary(h, _, _) => *h,
        }
    }

    /// Convert to a byte vector.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut space = Vec::with_capacity(1024);
        self.write_bytes(&mut space).unwrap();
        space
    }

    /// Write to a byte slice
    pub fn write_bytes(&self, mut out: impl Write) -> std::io::Result<usize> {
        match self {
            RawNode::Single(h, key, inner) => {
                let o = out.write(&[0])?;
                let i = out.write(&[*h])?;
                let b = out.write(key)?;
                Ok(o + i + b + out.write(inner)?)
            }
            RawNode::Hexary(height, count, gggc) => {
                let mut o = out.write(&[*height])?;
                o += out.write(&count.to_le_bytes())?;
                for gggc in gggc.iter() {
                    o += out.write(&gggc[..])?;
                }
                Ok(o)
            }
        }
    }

    /// From a byte slice
    pub fn try_from_slice(slice: &'a [u8]) -> Option<Self> {
        if slice.is_empty() {
            return None;
        }
        match slice[0] {
            0 => {
                if slice.len() < 1 + 1 + 32 {
                    return None;
                }
                let height = slice[1];
                let key = array_ref![slice, 2, 32];
                // data block
                Some(Self::Single(height, *key, (&slice[2 + 32..]).into()))
            }
            height => {
                if slice.len() != 1 + 8 + 32 * 16 {
                    return None;
                }
                let count = u64::from_le_bytes(*array_ref![slice, 1, 8]);
                let slice = &slice[9..];
                let gggc: [Hashed; 16] = [
                    *(array_ref![slice, 0, 32]),
                    *(array_ref![slice, 32, 32]),
                    *(array_ref![slice, 32 * 2, 32]),
                    *(array_ref![slice, 32 * 3, 32]),
                    *(array_ref![slice, 32 * 4, 32]),
                    *(array_ref![slice, 32 * 5, 32]),
                    *(array_ref![slice, 32 * 6, 32]),
                    *(array_ref![slice, 32 * 7, 32]),
                    *(array_ref![slice, 32 * 8, 32]),
                    *(array_ref![slice, 32 * 9, 32]),
                    *(array_ref![slice, 32 * 10, 32]),
                    *(array_ref![slice, 32 * 11, 32]),
                    *(array_ref![slice, 32 * 12, 32]),
                    *(array_ref![slice, 32 * 13, 32]),
                    *(array_ref![slice, 32 * 14, 32]),
                    *(array_ref![slice, 32 * 15, 32]),
                ];
                Some(Self::Hexary(height, count, gggc.into()))
            }
        }
    }

    /// Convert to a fully-owned value
    pub fn into_owned(self) -> RawNode<'static> {
        match self {
            RawNode::Single(h, k, c) => RawNode::Single(h, k, c.into_owned().into()),
            RawNode::Hexary(h, c, gggc) => RawNode::Hexary(h, c, gggc),
        }
    }
}
