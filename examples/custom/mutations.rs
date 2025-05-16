#[derive(Debug)]
struct Numbers {
  a: u64,
  b: u64,
  c: u64,
}

fn get_a_ref(numbers: &Numbers) -> &u64 {
  &numbers.a
}

fn get_b_mut(numbers: &mut Numbers) -> &mut u64 {
  &mut numbers.b
}

fn duplicate(a: &u64, b: &mut u64, c: &mut u64) {
  *b = *a;
  *c = *a;
}

fn apply_duplicate(numbers: &mut Numbers) {
  duplicate(get_a_ref(&numbers), get_b_mut(&mut numbers), &mut numbers.c);
}

fn main() {
  let mut numbers = Numbers { a: 1, b: 2, c: 3 };

  apply_duplicate(&mut numbers);

  println!("{:#?}", numbers);
}

fn incr(mut x: u64, y: u64) -> u64 {
  x += y;
  x
}
