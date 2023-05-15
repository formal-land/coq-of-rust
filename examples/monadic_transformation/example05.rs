struct Foo(u32);

impl Foo {
    fn plus1(s: Self) -> u32 {
        s.0 + 1
    }
}

fn main() {
    let foo = Foo(0);
    foo.plus1;
}
