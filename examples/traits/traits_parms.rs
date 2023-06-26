trait Foo {}
trait Bar {}
trait Tar {}

trait SomeTrait {
    type SomeType: Foo + Bar + Tar;

    fn some_fn();
}

struct SomeOtherType(u32);

impl SomeTrait for SomeOtherType {
    fn some_fn() {}
}
