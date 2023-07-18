pub struct SomeType(u32);

impl SomeType {
    pub fn meth1(self) { self.meth2(); }
    fn meth2(self) {}
}

mod inner_mod {
    pub fn bar() {
	tar();
    }
    
    fn tar() {}
}

fn main() {
    foo();
    inner_mod::bar();
    SomeType(0).meth1();
}

fn foo() {}

