(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn gen_range() -> u32 {
    todo!()
}
*)
Parameter gen_range : M u32.t.

(*
fn main() {
    println!("Guess the number!");
    let secret_number = gen_range();
    // println!("The secret number is: {secret_number}");
    loop {
        println!("Please input your guess.");

        let mut guess = String::new();

        io::stdin()
            .read_line(&mut guess)
            .expect("Failed to read line");

        // shadowing previous var {guess}.
        // We do shadowing when we want to convert var from one type to another
        let guess: u32 = match guess.trim().parse() {
            Ok(num) => num,
            Err(_) => continue,
        };

        println!("You guessed: {guess}");

        match guess.cmp(&secret_number) {
            Ordering::Less => println!("Too small!"),
            Ordering::Greater => println!("Too big!"),
            Ordering::Equal => {
                println!("You win!");
                break;
            }
        }
    }
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.