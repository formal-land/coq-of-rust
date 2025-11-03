#![no_std]

pub fn sum_checked(xs: &[u32]) -> Option<u32> {
    let mut acc: u32 = 0;
    let mut i: usize = 0;
    // Invariant idea (Coq):
    //  - 0 <= i <= xs.len()
    //  - acc = sum(xs[0..i]) and never overflowed
    while i < xs.len() {
        match acc.checked_add(xs[i]) {
            Some(v) => acc = v,
            None => return None,
        }
        i += 1;
    }
    Some(acc)
}

pub fn reverse_in_place(xs: &mut [i32]) {
  if xs.len() == 0 { return; }
  let mut l: usize = 0;
  let mut r: usize = xs.len() - 1;
  // Invariant idea:
  //  - xs[0..l] and xs[r+1..] are already reversed wrt original
  //  - l <= r + 1
  while l < r {
      let tmp = xs[l];
      xs[l] = xs[r];
      xs[r] = tmp;
      l += 1;
      r -= 1;
  }
}

pub fn is_sorted(xs: &[i32]) -> bool {
  let mut i: usize = 1;
  // Invariant idea:
  //  - prefix xs[0..i] is sorted (pairwise non-decreasing)
  while i < xs.len() {
      if xs[i - 1] > xs[i] { return false; }
      i += 1;
  }
  true
}

pub fn max_array<const N: usize>(a: &[i32; N]) -> i32 {
  let mut m = a[0];
  let mut i: usize = 1;
  // Invariant idea:
  //  - m = max(a[0..i])
  while i < N {
      if a[i] > m { m = a[i]; }
      i += 1;
  }
  m
}
