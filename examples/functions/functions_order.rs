pub struct SomeType(u32); // functions_order::SomeType

impl SomeType {
    pub fn meth1(self) {
        self.meth2();
    } // functions_order::impl_SomeType::meth1
    fn meth2(self) {} // functions_order::impl_SomeType::meth2
}

trait SomeTrait {
    fn some_trait_foo(&self);
    fn some_trait_bar(&self);
}

impl SomeTrait for SomeType {
    fn some_trait_foo(&self) {
        self.some_trait_bar()
    }

    fn some_trait_bar(&self) {}
}

mod inner_mod {
    // functions_order::inner_mod
    pub fn bar() {
        // functions_order::inner_mod::bar
        tar();
    }

    fn tar() {} // functions_order::inner_mod::bar

    mod nested_mod {
        pub fn tick() {
            tack();
        }
        fn tack() {}
    }
}

fn main() {
    // functions_order::main
    foo();
    inner_mod::bar();
    // SomeType(0).meth1();
}

fn foo() {} // functions_order::foo
