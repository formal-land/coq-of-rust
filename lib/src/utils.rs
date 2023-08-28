#[allow(dead_code)]
pub fn print_stacktrace(n: usize) {
    eprintln!("------------ Backtrace ------------");
    for frame in std::backtrace::Backtrace::capture()
        .frames()
        .iter()
        .skip(2)
        .take(n)
    {
        eprintln!("{:?}", frame);
    }
    eprintln!("--------- end of backtrace -------");
}
