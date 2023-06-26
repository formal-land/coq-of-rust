trait Foo {}
trait Bar {}
trait Tar {}

trait SomeTrait {
    type SomeType: Foo + Bar + Tar;

    fn some_fn();
}

struct SomeType(u32);

impl SomeTrait for SomeType {
    fn some_fn() {}
}
