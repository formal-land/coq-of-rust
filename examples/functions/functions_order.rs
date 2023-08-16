pub struct SomeType(u32);
pub struct OtherType(bool);

impl SomeType {
    pub fn meth1(self) {
        self.meth2();
    } // functions_order::impl_SomeType::meth1
    fn meth2(self) {} // functions_order::impl_SomeType::meth2
}

fn depends_on_trait_impl(u: u32, b: bool) {
    OtherType(b).some_trait_foo();
    SomeType(u).some_trait_foo();
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

impl SomeTrait for OtherType {
    fn some_trait_foo(&self) {}
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
    SomeType(0).meth1();
}

fn foo() {} // functions_order::foo
