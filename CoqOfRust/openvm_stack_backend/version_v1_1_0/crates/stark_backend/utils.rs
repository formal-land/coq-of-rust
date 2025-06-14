use std::borrow::Cow;

use cfg_if::cfg_if;
use p3_field::Field;
use tracing::instrument;

use crate::air_builders::debug::USE_DEBUG_BUILDER;

// Copied from valida-util
/// Calculates and returns the multiplicative inverses of each field element, with zero
/// values remaining unchanged.
#[instrument(name = "batch_multiplicative_inverse", level = "info", skip_all)]
pub fn batch_multiplicative_inverse_allowing_zero<F: Field>(values: Vec<F>) -> Vec<F> {
    // Check if values are zero, and construct a new vector with only nonzero values
    let mut nonzero_values = Vec::with_capacity(values.len());
    let mut indices = Vec::with_capacity(values.len());
    for (i, value) in values.iter().cloned().enumerate() {
        if value.is_zero() {
            continue;
        }
        nonzero_values.push(value);
        indices.push(i);
    }

    // Compute the multiplicative inverse of nonzero values
    let inverse_nonzero_values = p3_field::batch_multiplicative_inverse(&nonzero_values);

    // Reconstruct the original vector
    let mut result = values.clone();
    for (i, index) in indices.into_iter().enumerate() {
        result[index] = inverse_nonzero_values[i];
    }

    result
}

/// Disables the debug builder so there are not debug assert panics.
/// Commonly used in negative tests to prevent panics.
pub fn disable_debug_builder() {
    USE_DEBUG_BUILDER.with(|debug| {
        *debug.lock().unwrap() = false;
    });
}

/// A span that will run the given closure `f`,
/// and emit a metric with the given `name` using [`gauge`](metrics::gauge)
/// when the feature `"bench-metrics"` is enabled.
#[allow(unused_variables)]
pub fn metrics_span<R, F: FnOnce() -> R>(name: impl Into<Cow<'static, str>>, f: F) -> R {
    cfg_if! {
        if #[cfg(feature = "bench-metrics")] {
            let start = std::time::Instant::now();
            let res = f();
            metrics::gauge!(name.into()).set(start.elapsed().as_millis() as f64);
            res
        } else {
            f()
        }
    }
}

#[macro_export]
#[cfg(feature = "parallel")]
macro_rules! parizip {
    ( $first:expr $( , $rest:expr )* $(,)* ) => {
        {
            use rayon::iter::*;
            (( $first $( , $rest)* )).into_par_iter()
        }
    };
}
#[macro_export]
#[cfg(not(feature = "parallel"))]
macro_rules! parizip {
    ( $first:expr $( , $rest:expr )* $(,)* ) => {
        itertools::izip!( $first $( , $rest)* )
    };
}
