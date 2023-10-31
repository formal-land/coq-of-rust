struct Foo(u32);

impl Foo {
    fn plus1(self) -> u32 {
        self.0 + 1
    }
}

fn main() {
    let foo = Foo(0);
    foo.plus1();
}
