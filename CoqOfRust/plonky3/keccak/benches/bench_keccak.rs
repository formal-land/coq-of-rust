use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use p3_field::PrimeCharacteristicRing;
use p3_keccak::{KeccakF, VECTOR_LEN};
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge, Permutation, SerializingHasher32To64};

pub fn criterion_benchmark(c: &mut Criterion) {
    keccak_permutation(c);
    keccak_u64_hash(c);
    keccak_field_32_hash(c);
}

pub fn keccak_permutation(c: &mut Criterion) {
    /// The rate is 136 bytes (per permutation), and our vectorized impl processes twice that.
    const BYTES_PER_PERM: usize = 136 * VECTOR_LEN;

    let mut group = c.benchmark_group("keccak permutation");
    let mut bytes: [[u64; VECTOR_LEN]; 25] = unsafe { core::mem::zeroed() };
    group.throughput(Throughput::Bytes(BYTES_PER_PERM as u64));
    group.bench_function("keccak permutation [[u64; VECTOR_LEN]; 25]", |b| {
        b.iter(|| KeccakF.permute_mut(black_box(&mut bytes)))
    });
    group.finish();
}

pub fn keccak_u64_hash(c: &mut Criterion) {
    const U64_PAIRS_PER_HASH: usize = 100;
    const BYTES_PER_HASH: usize = size_of::<[u64; VECTOR_LEN]>() * U64_PAIRS_PER_HASH;
    let input = vec![[0u64; VECTOR_LEN]; U64_PAIRS_PER_HASH];

    type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
    let u64_hash = U64Hash::new(KeccakF {});

    let mut group = c.benchmark_group("keccak u64 hash");
    group.throughput(Throughput::Bytes(BYTES_PER_HASH as u64));
    group.bench_function("keccak u64 hash_slice", |b| {
        b.iter(|| u64_hash.hash_slice(black_box(&input)))
    });
    group.bench_function("keccak u64 hash_iter", |b| {
        b.iter(|| u64_hash.hash_iter(black_box(input.iter().copied())))
    });
    group.finish();
}

pub fn keccak_field_32_hash(c: &mut Criterion) {
    type F = Mersenne31;
    type P = [F; VECTOR_LEN];
    const PACKED_ELEMS_PER_HASH: usize = 100;
    const BYTES_PER_HASH: usize = size_of::<P>() * PACKED_ELEMS_PER_HASH;
    let input = vec![[F::ZERO; VECTOR_LEN]; PACKED_ELEMS_PER_HASH];

    type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
    let u64_hash = U64Hash::new(KeccakF {});
    type FieldHash = SerializingHasher32To64<U64Hash>;
    let field_hash = FieldHash::new(u64_hash);

    let mut group = c.benchmark_group("keccak field 32 hash");
    group.throughput(Throughput::Bytes(BYTES_PER_HASH as u64));
    group.bench_function("keccak field 32 hash_slice", |b| {
        b.iter(|| {
            <FieldHash as CryptographicHasher<P, [[u64; VECTOR_LEN]; 4]>>::hash_slice(
                &field_hash,
                black_box(&input),
            )
        })
    });
    group.bench_function("keccak field 32 hash_iter", |b| {
        b.iter(|| {
            <FieldHash as CryptographicHasher<P, [[u64; VECTOR_LEN]; 4]>>::hash_iter(
                &field_hash,
                black_box(input.iter().copied()),
            )
        })
    });
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
