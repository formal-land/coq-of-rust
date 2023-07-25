pub struct SomeType(u32); // functions_order::SomeType

impl SomeType {
    pub fn meth1(self) {
        self.meth2();
    } // functions_order::impl_SomeType::meth1
    fn meth2(self) {} // functions_order::impl_SomeType::meth2
}

impl Default for SomeType {
    fn default() -> SomeType {
        SomeType(42)
    }
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

/*

- type definitions
- fucntion definitions
- impl definitions
- module definitions
- impl trait definitions

{
  "reorder": {
    "functions_order": {
      "top_level": [
         "SomeType",
         "impl_SomeType",
         "inner_mod",
         "foo",
         "main"
      ],
      "impl_Default_for_SomeType": ["default"]
      "impl_SomeType": ["meth2", "meth1"]
      "inner_mod": ["tar", "bar"],
       inner_mod::nested_mod": ["tack", "tick"],
    },
  }
}
*/
