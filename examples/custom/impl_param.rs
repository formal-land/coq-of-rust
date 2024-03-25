fn with_impls<A>(func: impl Default, func2: impl Default, foo: A) {
    let mut x = func;
    x = Default::default();

    let mut y = func2;
    y = Default::default();

    let z = foo;

    let b = Box::new((x, y, z));
}
