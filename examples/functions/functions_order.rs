mod inner_mod {
    pub fn bar() {
	tar();
    }
    
    fn tar() {}
}

fn main() {
    foo();
    inner_mod::bar();
}

fn foo() {}

