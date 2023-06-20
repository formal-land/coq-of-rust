const _: () = {
    struct Foo {
        test: bool,
    }
};

struct Bar {
    test: String,
}

trait BarTrait {
    fn show(self) -> String;
}

const _: () = {
    impl BarTrait for Bar {
        fn show(self: Self) -> String {
            self.test
        }
    }
};
