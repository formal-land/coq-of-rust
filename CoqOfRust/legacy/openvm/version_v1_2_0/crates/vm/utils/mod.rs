#[cfg(any(test, feature = "test-utils"))]
mod stark_utils;
#[cfg(any(test, feature = "test-utils"))]
mod test_utils;

pub use openvm_circuit_primitives::utils::next_power_of_two_or_zero;
#[cfg(any(test, feature = "test-utils"))]
pub use stark_utils::*;
#[cfg(any(test, feature = "test-utils"))]
pub use test_utils::*;
