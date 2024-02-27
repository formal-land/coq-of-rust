#[derive(Debug)]
struct Constructor(i32);

fn main() {
    let v: Vec<_> = vec![1, 2, 3].into_iter().map(Constructor).collect();

    println!("{v:?}");
}
