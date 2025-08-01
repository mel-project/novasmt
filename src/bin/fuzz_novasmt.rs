use std::convert::TryInto;

#[cfg(fuzzing)]
use honggfuzz::fuzz;
use novasmt::{Hashed, InMemoryStore, Tree};
#[cfg(fuzzing)]
fn main() {
    use env_logger::Env;
    env_logger::Builder::from_env(Env::default().default_filter_or("debug")).init();
    // Here you can parse `std::env::args and
    // setup / initialize your project

    // You have full control over the loop but
    // you're supposed to call `fuzz` ad vitam aeternam
    // std::thread::spawn(|| {
    //     use std::time::Duration;

    //     std::thread::sleep(Duration::from_secs(1));
    //     panic!("crash due to timeout")
    // });
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
    let forest = InMemoryStore::default();
    let mut tree = Tree::empty(&forest);
    for bytes in broken_up.iter() {
        let _ = tree.get_with_proof(*bytes);
        tree = tree.with([0; 32], bytes).unwrap();
        log::warn!("inserting zero => {}", hex::encode(bytes));
        let (r, p) = tree.get_with_proof([0; 32]).unwrap();
        assert_eq!(&r[..], &bytes[..]);
        assert!(p.verify(tree.root_hash(), [0; 32], bytes.as_ref()));
        // tree.debug_graphviz();
        tree = tree.with(*bytes, bytes).unwrap();
        // tree.debug_graphviz();
        let gotten = tree.get_with_proof(*bytes).unwrap();
        assert_eq!(gotten.0.as_ref(), bytes.as_ref());
        assert!(tree.get_with_proof(*bytes).unwrap().1.verify(
            tree.root_hash(),
            *bytes,
            bytes.as_ref()
        ));
    }
    // for bytes in broken_up.iter() {
    //     let (val, proof) = tree.get_with_proof(*bytes);
    //     assert!(proof.verify(tree.root_hash(), *bytes, &val));
    //     assert_eq!(bytes.as_ref(), val.as_ref());
    // }
}

#[cfg(not(fuzzing))]
fn main() {}
