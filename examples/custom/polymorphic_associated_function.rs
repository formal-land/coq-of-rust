struct Foo<T> {
    data: T,
}

impl<A> Foo<A> {
    fn convert<B: From<A>>(self) -> Foo<B> {
        Foo {
            data: self.data.into(),
        }
    }
}

fn main() {
    let foo = Foo { data: 42 };
    let bar: Foo<f64> = foo.convert();

    assert_eq!(bar.data, 42.0);
}
