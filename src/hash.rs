use crate::Hashed;

pub(crate) const DATA_BLOCK_HASH_KEY: &[u8; 13] = b"smt_datablock";
pub(crate) const NODE_HASH_KEY: &[u8; 8] = b"smt_node";

/// Hash a data block
pub fn hash_data(bytes: &[u8]) -> Hashed {
    if bytes.is_empty() {
        [0; 32]
    } else {
        *blake3::keyed_hash(blake3::hash(DATA_BLOCK_HASH_KEY).as_bytes(), bytes).as_bytes()
    }
}

/// Hash a node
pub fn hash_node(left: Hashed, right: Hashed) -> Hashed {
    if left == [0; 32] && right == [0; 32] {
        return [0; 32];
    }
    let mut buf = [0u8; 64];
    buf[0..32].copy_from_slice(&left);
    buf[32..].copy_from_slice(&right);
    *blake3::keyed_hash(blake3::hash(NODE_HASH_KEY).as_bytes(), &buf).as_bytes()
}
