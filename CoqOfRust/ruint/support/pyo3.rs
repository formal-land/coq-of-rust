//! Support for the [`pyo3`](https://crates.io/crates/pyo3) crate.
//!
//! Conversion is to/from Python native integers. Beware that Python native
//! integers are unbounded and not a ring modulo a power of two like [`Uint`].
//!
//! This uses the not-so-public `_PyLong_FromByteArray`, `_PyLong_AsByteArray`
//! ABI, which according to this [Stackoverflow answer][so] is the accepted way
//! to do efficient bigint conversions. It is supported by [CPython][cpython]
//! and [PyPy][pypy].
//!
//! [so]: https://stackoverflow.com/a/18326068
//! [cpython]: https://github.com/python/cpython/blob/e8165d47b852e933c176209ddc0b5836a9b0d5f4/Include/cpython/longobject.h#L47
//! [pypy]: https://foss.heptapod.net/pypy/pypy/-/blob/branch/default/pypy/module/cpyext/longobject.py#L238
//!
//! The implementation uses Pyo3 builtin `u64` conversion when $\mathtt{BITS} ≤
//! 64$ and otherwise uses similar conversion to Pyo3 builtin `num-bigint`
//! support. See Pyo3's [`num.rs`][num] and [`num_bigint.rs`][bigint] for
//! reference.
//!
//! [num]: https://github.com/PyO3/pyo3/blob/caaf7bbda74f873297d277733c157338f5492580/src/types/num.rs#L81
//! [bigint]: https://github.com/PyO3/pyo3/blob/4a68273b173ef86dac059106cc0b5b3c2c9830e2/src/conversions/num_bigint.rs#L80

#![cfg(feature = "pyo3")]
#![cfg_attr(docsrs, doc(cfg(feature = "pyo3")))]

use crate::Uint;
use core::ffi::c_uchar;
use pyo3::{
    exceptions::PyOverflowError, ffi, AsPyPointer, FromPyObject, IntoPy, PyAny, PyErr, PyObject,
    PyResult, Python, ToPyObject,
};

impl<const BITS: usize, const LIMBS: usize> ToPyObject for Uint<BITS, LIMBS> {
    fn to_object(&self, py: Python<'_>) -> PyObject {
        // Fast path for small ints
        if BITS <= 64 {
            let value = self.as_limbs().first().copied().unwrap_or(0);
            return unsafe {
                let obj = ffi::PyLong_FromUnsignedLongLong(value);
                assert!(!obj.is_null(), "Out of memory");
                PyObject::from_owned_ptr(py, obj)
            };
        }

        // Convert using little endian bytes (trivial on LE archs)
        // and `_PyLong_FromByteArray`.
        let bytes = self.as_le_bytes();
        unsafe {
            let obj =
                ffi::_PyLong_FromByteArray(bytes.as_ptr().cast::<c_uchar>(), bytes.len(), 1, 0);
            PyObject::from_owned_ptr(py, obj)
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> IntoPy<PyObject> for Uint<BITS, LIMBS> {
    fn into_py(self, py: Python<'_>) -> PyObject {
        self.to_object(py)
    }
}

impl<'source, const BITS: usize, const LIMBS: usize> FromPyObject<'source> for Uint<BITS, LIMBS> {
    fn extract(ob: &'source PyAny) -> PyResult<Self> {
        let mut result = Self::ZERO;

        // On little endian let Python write directly to the uint.
        #[cfg(target_endian = "little")]
        let py_result = unsafe {
            let raw = result.as_le_slice_mut();
            ffi::_PyLong_AsByteArray(
                ob.as_ptr().cast::<ffi::PyLongObject>(),
                raw.as_mut_ptr(),
                raw.len(),
                1,
                0,
            )
        };

        // On big endian we use an intermediate
        #[cfg(not(target_endian = "little"))]
        let py_result = {
            let mut raw = vec![0_u8; Self::LIMBS * 8];
            let py_result = unsafe {
                ffi::_PyLong_AsByteArray(
                    ob.as_ptr().cast::<ffi::PyLongObject>(),
                    raw.as_mut_ptr(),
                    raw.len(),
                    1,
                    0,
                )
            };
            result = Self::try_from_le_slice(raw.as_slice()).ok_or_else(|| {
                PyOverflowError::new_err(format!("Number to large to fit Uint<{}>", Self::BITS))
            })?;
            py_result
        };

        // Handle error from `_PyLong_AsByteArray`.
        if py_result != 0 {
            // A TypeError is set if the value is negative and an Overflow error if the
            // value does not fit `raw.len()` bytes.
            return Err(PyErr::fetch(ob.py()));
        }

        // Check mask since we wrote raw.
        #[cfg(target_endian = "little")]
        if let Some(last) = result.as_limbs().last() {
            if *last > Self::MASK {
                return Err(PyOverflowError::new_err(format!(
                    "Number to large to fit Uint<{}>",
                    Self::BITS
                )));
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        aliases::{U0, U256, U512, U64, U8},
        const_for, nlimbs,
    };
    use proptest::proptest;

    #[test]
    fn test_roundtrip() {
        pyo3::prepare_freethreaded_python();
        Python::with_gil(|py| {
            const_for!(BITS in SIZES {
                const LIMBS: usize = nlimbs(BITS);
                type U = Uint<BITS, LIMBS>;
                proptest!(|(value: U)| {
                    let obj = value.into_py(py);
                    let native = obj.extract::<U>(py).unwrap();
                    assert_eq!(value, native);
                });
            });
        });
    }

    #[test]
    fn test_errors() {
        pyo3::prepare_freethreaded_python();
        Python::with_gil(|py| {
            let obj = (-1_i64).to_object(py);
            assert!(obj.extract::<U0>(py).is_err());
            assert!(obj.extract::<U256>(py).is_err());

            let obj = (1000_i64).to_object(py);
            assert!(obj.extract::<U0>(py).is_err());
            assert!(obj.extract::<U8>(py).is_err());

            let obj = U512::MAX.to_object(py);
            assert!(obj.extract::<U0>(py).is_err());
            assert!(obj.extract::<U64>(py).is_err());
            assert!(obj.extract::<U256>(py).is_err());
        });
    }
}
