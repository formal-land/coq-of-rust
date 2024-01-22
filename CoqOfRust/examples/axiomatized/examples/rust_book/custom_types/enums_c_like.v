(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module Number.
  Inductive t : Set :=
  | Zero
  | One
  | Two.
End Number.

Module Color.
  Inductive t : Set :=
  | Red
  | Green
  | Blue.
  
  Definition Red_discriminant : isize.t := Integer.of_Z 16711680.
  Definition Green_discriminant : isize.t := Integer.of_Z 65280.
  Definition Blue_discriminant : isize.t := Integer.of_Z 255.
End Color.

(*
fn main() {
    // `enums` can be cast as integers.
    println!("zero is {}", Number::Zero as i32);
    println!("one is {}", Number::One as i32);

    println!("roses are #{:06x}", Color::Red as i32);
    println!("violets are #{:06x}", Color::Blue as i32);
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.