Require Import Coq.Strings.String.
Require Import CoqOfRust.Simulations.M.
Require Import CoqOfRust.core.option.
Import Simulations.M.Notations.

Module Option.
  Definition expect {State A : Set}
    (self : core.option.Option.t A) (msg : string) : MS? State A :=
    match self with
    | Option.None => panicS? msg
    | Option.Some x => returnS? x
    end.

  Definition unwrap {State A : Set}
    (self : core.option.Option.t A) (msg : string) : MS? State A :=
    expect self "". 
End Option.