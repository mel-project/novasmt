use std::convert::TryInto;

use bytes::Bytes;
#[cfg(fuzzing)]
use honggfuzz::fuzz;
use novasmt::{Forest, Hashed, InMemoryBackend};

#[cfg(fuzzing)]
fn main() {
    use env_logger::Env;
    env_logger::Builder::from_env(Env::default().default_filter_or("novasmt")).init();
    // Here you can parse `std::env::args and
    // setup / initialize your project

    // You have full control over the loop but
    // you're supposed to call `fuzz` ad vitam aeternam
    loop {
        // The fuzz macro gives an arbitrary object (see `arbitrary crate`)
        // to a closure-like block of code.
        // For performance reasons, it is recommended that you use the native type
        // `&[u8]` when possible.
        // Here, this slice will contain a "random" quantity of "random" data.
        fuzz!(|data: &[u8]| { test_once(data) });
    }
}

fn test_once(data: &[u8]) {
    let broken_up: Vec<Hashed> = data.windows(32).map(|v| v.try_into().unwrap()).collect();
    let forest = Forest::new(InMemoryBackend::default());
    let mut tree = forest.open_tree([0; 32]).unwrap();
    for bytes in broken_up.iter() {
        let pre_count = tree.iter().count();
        dbg!(pre_count);
        tree.insert([0; 32], Bytes::copy_from_slice(bytes));
        assert!(tree
            .get_with_proof([0; 32])
            .1
            .verify(tree.root_hash(), [0; 32], bytes.as_ref()));
        forest.delete_tree(tree.root_hash());
        tree.save();
        tree.insert(*bytes, Bytes::copy_from_slice(bytes));
        let gotten = tree.get_with_proof(*bytes);
        assert_eq!(gotten.0.as_ref(), bytes.as_ref());
        assert!(tree
            .get_with_proof(*bytes)
            .1
            .verify(tree.root_hash(), *bytes, bytes.as_ref()));
        // tree.save();
    }
    // for bytes in broken_up.iter() {
    //     let (val, proof) = tree.get_with_proof(*bytes);
    //     assert!(proof.verify(tree.root_hash(), *bytes, &val));
    //     assert_eq!(bytes.as_ref(), val.as_ref());
    // }
}

#[cfg(not(fuzzing))]
fn main() {}
