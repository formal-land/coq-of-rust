struct Foo<const N: usize, T> {
  data: T,
  array: [T; N],
}

impl<const N: usize, A> Foo<N, A> {
  fn convert<B: From<A>>(self) -> Foo<0, B> {
      Foo {
          data: self.data.into(),
          array: [],
      }
  }
}

fn main() {
  let foo = Foo { data: 42, array: [42; 3] };
  let bar: Foo<0, f64> = foo.convert();

  assert_eq!(bar.data, 42.0);
  assert_eq!(bar.array, []);
}
