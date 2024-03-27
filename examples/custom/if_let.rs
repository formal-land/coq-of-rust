fn main() {
    let x = Some(5);

    if let Some(y) = x {
        println!("if: {y}");
    }

    match x {
        Some(_) if let Some(y) = x => println!("match: {y}"),
        None => {}
    }
}
