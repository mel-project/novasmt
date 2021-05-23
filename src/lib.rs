mod hash;
mod merkmath;
mod traits;
mod tree;
pub use merkmath::*;
pub use traits::*;
pub use tree::*;

pub type Hashed = [u8; 32];

#[cfg(test)]
mod tests {
    use env_logger::Env;
    use hash::hash_data;

    use super::*;

    #[test]
    fn basic_insert_get() {
        env_logger::Builder::from_env(Env::default().default_filter_or("novasmt")).init();
        let forest = Forest::new(InMemoryBackend::default());
        let mut tree = forest.open_tree([0; 32]).unwrap();
        for i in 0u64..1000 {
            let key = hash_data(&i.to_be_bytes());
            tree.insert(key, key.to_vec().into());
        }
        tree.save();
        tree.get_with_proof([0; 32]);
        forest.delete_tree(tree.root_hash());
        for i in 0u64..100 {
            let key = hash_data(&i.to_be_bytes());
            let (val, proof) = tree.get_with_proof(key);
            let mut val = val.to_vec();
            assert!(proof.verify(tree.root_hash(), key, &val));
            val[0] ^= 1;
            assert!(!proof.verify(tree.root_hash(), key, &val));
        }
    }

    #[test]
    fn basic_insert_delete() {
        env_logger::Builder::from_env(Env::default().default_filter_or("novasmt")).init();
        let forest = Forest::new(InMemoryBackend::default());
        let mut tree = forest.open_tree([0; 32]).unwrap();
        for i in 0u64..1000 {
            let key = hash_data(&i.to_be_bytes());
            tree.insert(key, key.to_vec().into());
        }
        tree.save();
        let old_root = tree.root_hash();
        for i in 0u64..500 {
            let key = hash_data(&i.to_be_bytes());
            tree.insert(key, vec![].into());
        }
        tree.save();
        forest.delete_tree(old_root);
        tree.get_with_proof([0; 32]);
    }
}
