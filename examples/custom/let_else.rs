fn foo(x: Option<i32>) -> i32 {
    let Some(x) = x else {
        return 0;
    };
    x + 1
}
