fn order(b1: bool, b2: bool, b3: bool, b4: bool) -> bool {
    b1 && b2 && b3 && b4
}

enum Container {
    Left(i32),
    Right(i32),
    Empty,
}

fn extract_value(container: Container) -> i32 {
    match container {
        Container::Left(value) | Container::Right(value) => value,
        Container::Empty => 0,
    }
}

fn main() {
    let x = Some(5);

    if let Some(y) = x {
        println!("if: {y}");
    }

    match x {
        Some(_) if let Some(y) = x => println!("match: {y}"),
        None => {}
    }

    if let Some(y) = x
        && y > 3
        && let Some(z) = x
    {
        println!("if and: {y} {z}");
    }

    match x {
        Some(_)
            if let Some(y) = x
                && y > 3
                && let Some(z) = x =>
        {
            println!("match and: {y} {z}")
        }
        None => {}
    }
}
