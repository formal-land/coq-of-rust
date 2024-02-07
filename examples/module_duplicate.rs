mod foo {
    mod gre {
        pub fn f_foo_gre() {
            println!("foo::gre::bar");
        }
    }

    pub fn f_foo() {
        println!("foo::bar");
        gre::f_foo_gre();
    }
}

fn f() {
    foo::f_foo();
}
