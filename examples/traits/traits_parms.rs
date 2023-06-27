trait Foo {}
trait Bar {}
trait Tar {}

trait SomeTrait {
    type SomeType: Foo + Bar + Tar;

    fn some_fn();
}

struct SomeOtherType(u32);

impl Foo for SomeOtherType {}
impl Bar for SomeOtherType {}
impl Tar for SomeOtherType {}

impl SomeTrait for SomeOtherType {
    fn some_fn() {}
}
