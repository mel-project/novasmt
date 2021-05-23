use criterion::{criterion_group, criterion_main, Criterion};
use novasmt::{Forest, InMemoryBackend};

fn insert_from_scratch(n: u64) {
    let forest = Forest::new(InMemoryBackend::default());
    let mut tree = forest.open_tree([0; 32]).unwrap();
    for i in 0u64..n {
        let key = *blake3::hash(&i.to_be_bytes()).as_bytes();
        tree.insert(key, key.to_vec().into());
    }
}

fn insert_from_scratch_and_save(n: u64) {
    let forest = Forest::new(InMemoryBackend::default());
    let mut tree = forest.open_tree([0; 32]).unwrap();
    for i in 0u64..n {
        let key = *blake3::hash(&i.to_be_bytes()).as_bytes();
        tree.insert(key, key.to_vec().into());
        tree.save();
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("insert_from_scratch 100", |b| {
        b.iter(|| insert_from_scratch(100))
    });
    c.bench_function("insert_from_scratch_and_save 100", |b| {
        b.iter(|| insert_from_scratch_and_save(100))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
