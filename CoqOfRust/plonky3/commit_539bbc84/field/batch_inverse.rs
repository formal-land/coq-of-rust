use alloc::vec::Vec;

use p3_maybe_rayon::prelude::*;
use tracing::instrument;

use crate::field::Field;
use crate::{FieldAlgebra, FieldArray, PackedValue};

/// Batch multiplicative inverses with Montgomery's trick
/// This is Montgomery's trick. At a high level, we invert the product of the given field
/// elements, then derive the individual inverses from that via multiplication.
///
/// The usual Montgomery trick involves calculating an array of cumulative products,
/// resulting in a long dependency chain. To increase instruction-level parallelism, we
/// compute WIDTH separate cumulative product arrays that only meet at the end.
///
/// # Panics
/// This will panic if any of the inputs is zero.
#[instrument(level = "debug", skip_all)]
pub fn batch_multiplicative_inverse<F: Field>(x: &[F]) -> Vec<F> {
    // How many elements to invert in one thread.
    const CHUNK_SIZE: usize = 1024;

    let n = x.len();
    let mut result = F::zero_vec(n);

    x.par_chunks(CHUNK_SIZE)
        .zip(result.par_chunks_mut(CHUNK_SIZE))
        .for_each(|(x, result)| {
            batch_multiplicative_inverse_helper(x, result);
        });

    result
}

/// Like `batch_multiplicative_inverse`, but writes the result to the given output buffer.
fn batch_multiplicative_inverse_helper<F: Field>(x: &[F], result: &mut [F]) {
    // Higher WIDTH increases instruction-level parallelism, but too high a value will cause us
    // to run out of registers.
    const WIDTH: usize = 4;

    let n = x.len();
    assert_eq!(result.len(), n);
    if n % WIDTH != 0 {
        // There isn't a very clean way to do this with FieldArray; for now just do it in serial.
        // Another simple (though suboptimal) workaround would be to make two separate calls, one
        // for the packed part and one for the remainder.
        return batch_multiplicative_inverse_general(x, result, |x| x.inverse());
    }

    let x_packed = FieldArray::<F, 4>::pack_slice(x);
    let result_packed = FieldArray::<F, 4>::pack_slice_mut(result);

    batch_multiplicative_inverse_general(x_packed, result_packed, |x_packed| x_packed.inverse());
}

/// A simple single-threaded implementation of Montgomery's trick. Since not all `FieldAlgebra`s
/// support inversion, this takes a custom inversion function.
pub(crate) fn batch_multiplicative_inverse_general<F, Inv>(x: &[F], result: &mut [F], inv: Inv)
where
    F: FieldAlgebra + Copy,
    Inv: Fn(F) -> F,
{
    let n = x.len();
    assert_eq!(result.len(), n);
    if n == 0 {
        return;
    }

    result[0] = F::ONE;
    for i in 1..n {
        result[i] = result[i - 1] * x[i - 1];
    }

    let product = result[n - 1] * x[n - 1];
    let mut inv = inv(product);

    for i in (0..n).rev() {
        result[i] *= inv;
        inv *= x[i];
    }
}
