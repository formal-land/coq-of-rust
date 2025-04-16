use criterion::{BenchmarkGroup, Criterion, Throughput, criterion_group, criterion_main};
use p3_matrix::dense::RowMajorMatrix;
use rand::SeedableRng;
use rand::rngs::SmallRng;

fn transpose_benchmark(c: &mut Criterion) {
    const SMALL_DIMS: [(usize, usize); 4] = [(4, 4), (8, 8), (10, 10), (12, 12)];
    const LARGE_DIMS: [(usize, usize); 4] = [(20, 8), (21, 8), (22, 8), (23, 8)];

    let inner = |g: &mut BenchmarkGroup<_>, dims: &[(usize, usize)]| {
        let mut rng = SmallRng::seed_from_u64(1);
        for (lg_nrows, lg_ncols) in dims {
            let nrows = 1 << lg_nrows;
            let ncols = 1 << lg_ncols;
            let mut matrix1 = RowMajorMatrix::<u32>::rand(&mut rng, nrows, ncols);
            let mut matrix2 = RowMajorMatrix::default(nrows, ncols);

            let name = format!("2^{lg_nrows} x 2^{lg_ncols}");
            g.throughput(Throughput::Bytes(
                (nrows * ncols * core::mem::size_of::<u32>()) as u64,
            ));
            g.bench_function(&name, |b| b.iter(|| matrix1.transpose_into(&mut matrix2)));

            if nrows != ncols {
                let matrix2 = RowMajorMatrix::rand(&mut rng, ncols, nrows);
                let name = format!("2^{lg_ncols} x 2^{lg_nrows}");
                g.throughput(Throughput::Bytes(
                    (nrows * ncols * core::mem::size_of::<u32>()) as u64,
                ));
                g.bench_function(&name, |b| b.iter(|| matrix2.transpose_into(&mut matrix1)));
            }
        }
    };

    let mut g = c.benchmark_group("transpose");
    inner(&mut g, &SMALL_DIMS);
    g.sample_size(10);
    inner(&mut g, &LARGE_DIMS);
}

criterion_group!(benches, transpose_benchmark);
criterion_main!(benches);
