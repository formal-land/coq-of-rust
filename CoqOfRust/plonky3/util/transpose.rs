use core::ptr::swap;

const LB_BLOCK_SIZE: usize = 3;

/// Transpose square matrix in-place
/// The matrix is of size `1 << lb_size` by `1 << lb_size`. It occupies
/// `M[i, j] == arr[(i + x << lb_stride) + j + x]` for `0 <= i, j < 1 << lb_size`. The transposition
/// swaps `M[i, j]` and `M[j, i]`.
///
/// SAFETY:
/// Make sure that `(i + x << lb_stride) + j + x` is a valid index in `arr` for all
/// `0 <= i, j < 1 << lb_size`. Ensure also that `lb_size <= lb_stride` to prevent overlap.
unsafe fn transpose_in_place_square_small<T>(
    arr: &mut [T],
    lb_stride: usize,
    lb_size: usize,
    x: usize,
) {
    unsafe {
        for i in x + 1..x + (1 << lb_size) {
            for j in x..i {
                swap(
                    arr.get_unchecked_mut(i + (j << lb_stride)),
                    arr.get_unchecked_mut((i << lb_stride) + j),
                );
            }
        }
    }
}

/// Transpose square matrices and swap
/// The matrices are of size `1 << lb_size` by `1 << lb_size`. They occupy
/// `M0[i, j] == arr[(i + x << lb_stride) + j + y]`, `M1[i, j] == arr[i + x + (j + y << lb_stride)]`
/// for `0 <= i, j < 1 << lb_size. The transposition swaps `M0[i, j]` and `M1[j, i]`.
///
/// SAFETY:
/// Make sure that `(i + x << lb_stride) + j + y` and `i + x + (j + y << lb_stride)` are valid
/// indices in `arr` for all `0 <= i, j < 1 << lb_size`. Ensure also that `lb_size <= lb_stride` to
/// prevent overlap.
unsafe fn transpose_swap_square_small<T>(
    arr: &mut [T],
    lb_stride: usize,
    lb_size: usize,
    x: usize,
    y: usize,
) {
    unsafe {
        for i in x..x + (1 << lb_size) {
            for j in y..y + (1 << lb_size) {
                swap(
                    arr.get_unchecked_mut(i + (j << lb_stride)),
                    arr.get_unchecked_mut((i << lb_stride) + j),
                );
            }
        }
    }
}

/// Transpose square matrices and swap
/// The matrices are of size `1 << lb_size` by `1 << lb_size`. They occupy
/// `M0[i, j] == arr[(i + x << lb_stride) + j + y]`, `M1[i, j] == arr[i + x + (j + y << lb_stride)]`
/// for `0 <= i, j < 1 << lb_size. The transposition swaps `M0[i, j]` and `M1[j, i]`.
///
/// SAFETY:
/// Make sure that `(i + x << lb_stride) + j + y` and `i + x + (j + y << lb_stride)` are valid
/// indices in `arr` for all `0 <= i, j < 1 << lb_size`. Ensure also that `lb_size <= lb_stride` to
/// prevent overlap.
unsafe fn transpose_swap_square<T>(
    arr: &mut [T],
    lb_stride: usize,
    lb_size: usize,
    x: usize,
    y: usize,
) {
    unsafe {
        if lb_size <= LB_BLOCK_SIZE {
            transpose_swap_square_small(arr, lb_stride, lb_size, x, y);
        } else {
            let lb_block_size = lb_size - 1;
            let block_size = 1 << lb_block_size;
            transpose_swap_square(arr, lb_stride, lb_block_size, x, y);
            transpose_swap_square(arr, lb_stride, lb_block_size, x + block_size, y);
            transpose_swap_square(arr, lb_stride, lb_block_size, x, y + block_size);
            transpose_swap_square(
                arr,
                lb_stride,
                lb_block_size,
                x + block_size,
                y + block_size,
            );
        }
    }
}

/// Transpose square matrix in-place
/// The matrix is of size `1 << lb_size` by `1 << lb_size`. It occupies
/// `M[i, j] == arr[(i + x << lb_stride) + j + x]` for `0 <= i, j < 1 << lb_size`. The transposition
/// swaps `M[i, j]` and `M[j, i]`.
///
/// SAFETY:
/// Make sure that `(i + x << lb_stride) + j + x` is a valid index in `arr` for all
/// `0 <= i, j < 1 << lb_size`. Ensure also that `lb_size <= lb_stride` to prevent overlap.
pub(crate) unsafe fn transpose_in_place_square<T>(
    arr: &mut [T],
    lb_stride: usize,
    lb_size: usize,
    x: usize,
) {
    unsafe {
        if lb_size <= LB_BLOCK_SIZE {
            transpose_in_place_square_small(arr, lb_stride, lb_size, x);
        } else {
            let lb_block_size = lb_size - 1;
            let block_size = 1 << lb_block_size;
            transpose_in_place_square(arr, lb_stride, lb_block_size, x);
            transpose_swap_square(arr, lb_stride, lb_block_size, x, x + block_size);
            transpose_in_place_square(arr, lb_stride, lb_block_size, x + block_size);
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use super::*;

    /// Helper to create a square matrix of size `2^log_size` with elements `0..n^2`
    fn generate_matrix(log_size: usize) -> Vec<u32> {
        let size = 1 << log_size;
        (0..size * size).collect()
    }

    /// Reference transpose that returns a new vector (row-major layout)
    fn transpose_reference(input: &[u32], log_size: usize) -> Vec<u32> {
        let size = 1 << log_size;
        let mut transposed = vec![0; size * size];
        for i in 0..size {
            for j in 0..size {
                transposed[j * size + i] = input[i * size + j];
            }
        }
        transposed
    }

    /// Helper to test the full transpose and assert equality with reference
    fn test_transpose(log_size: usize) {
        let size = 1 << log_size;
        let mut mat = generate_matrix(log_size);

        let expected = transpose_reference(&mat, log_size);

        unsafe {
            transpose_in_place_square(&mut mat, log_size, log_size, 0);
        }

        assert_eq!(
            mat, expected,
            "Transpose failed for {}x{} matrix",
            size, size
        );
    }

    #[test]
    fn test_transpose_2x2() {
        test_transpose(1);
    }

    #[test]
    fn test_transpose_4x4() {
        test_transpose(2);
    }

    #[test]
    fn test_transpose_8x8() {
        test_transpose(3);
    }

    #[test]
    fn test_transpose_16x16() {
        test_transpose(4);
    }

    #[test]
    fn test_transpose_32x32() {
        test_transpose(5);
    }
}
