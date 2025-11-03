#![no_std]

// max2(a,b) = a or max2(a,b) = b
// max2(a,b) >= a and >= b
pub fn max2(a: u32, b: u32) -> u32 {
    if a < b { b } else { a }
}

// result ≥ 0
pub fn abs_i32(x: i32) -> i32 {
  if x < 0 { -x } else { x }
}

// Truth table correctness
pub fn bool_and(a: bool, b: bool) -> bool {
  if a {
      if b { true } else { false }
  } else {
      false
  }
}

pub fn get_or_zero(xs: &[u32; 4], i: usize) -> u32 {
  if i < 4 { xs[i] } else { 0 }
}

pub fn eq2(a: &[u32; 2], b: &[u32; 2]) -> bool {
  if a[0] == b[0] && a[1] == b[1] {
      true
  } else {
      false
  }
}

pub fn eq_pair(x: (u32, u32), y: (u32, u32)) -> bool {
  if x.0 == y.0 && x.1 == y.1 { true } else { false }
}

pub fn min3(a: u32, b: u32, c: u32) -> u32 {
  let m = if a < b { a } else { b };
  if m < c { m } else { c }
}
