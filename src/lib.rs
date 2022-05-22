mod database;
pub mod dense;
mod hash;
mod lowlevel;
mod merkmath;
pub use database::{ContentAddrStore, Database, InMemoryCas, Tree};
pub use merkmath::*;
pub use hash::*;

pub type Hashed = [u8; 32];

// #[cfg(test)]
// mod tests {
//     use env_logger::Env;
//     use hash::hash_data;

//     use super::*;

//     fn init_logs() {
//         let _ =
//             env_logger::Builder::from_env(Env::default().default_filter_or("novasmt")).try_init();
//     }

//     #[test]
//     fn basic_insert_get() {
//         init_logs();
//         let forest = Forest::new(InMemoryBackend::default());
//         let mut tree = forest.open_tree([0; 32]).unwrap();
//         for i in 0u64..100 {
//             let key = hash_data(&i.to_be_bytes());
//             tree.insert(key, key.to_vec().into());
//         }z
//         tree.save();
//         tree.get_with_proof([0; 32]);
//         forest.delete_tree(tree.root_hash());
//         for i in 0u64..100 {
//             let mut key = hash_data(&i.to_be_bytes());
//             let (val, proof) = tree.get_with_proof(key);
//             let mut val = val.to_vec();
//             assert!(proof.verify(tree.root_hash(), key, &val));
//             val[0] ^= 1;
//             assert!(!proof.verify(tree.root_hash(), key, &val));
//             key[0] ^= 1;
//             let (val, proof) = tree.get_with_proof(key);
//             assert!(proof.verify(tree.root_hash(), key, &val));
//         }
//     }

//     #[test]
//     fn basic_insert_delete() {
//         init_logs();
//         let forest = Forest::new(InMemoryBackend::default());
//         let mut tree = forest.open_tree([0; 32]).unwrap();
//         for i in 0u64..1000 {
//             let key = hash_data(&i.to_be_bytes());
//             tree.insert(key, key.to_vec().into());
//         }
//         tree.save();
//         std::thread::spawn(move || {
//             let old_root = tree.root_hash();
//             for i in 0u64..500 {
//                 let key = hash_data(&i.to_be_bytes());
//                 tree.insert(key, vec![].into());
//             }
//             tree.save();
//             forest.delete_tree(old_root);
//             tree.get_with_proof([0; 32]);
//         })
//         .join()
//         .unwrap();
//     }
// }
