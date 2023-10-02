(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* 
pub enum DispatchError {
    Other(&'static str),
    CannotLookup,
    BadOrigin,
    Module(ModuleError),
    ConsumerRemaining,
    NoProviders,
    TooManyConsumers,
    Token(TokenError),
    Arithmetic(ArithmeticError),
    Transactional(TransactionalError),
    Exhausted,
    Corruption,
    Unavailable,
    RootNotAllowed,
}
*)

(* NOTE: arguments should be added in the future *)
Module DispatchError.
  Inductive t : Set := 
  | Other
  | CannotLookup
  | BadOrigin
  | Module
  | ConsumerRemaining
  | NoProviders
  | TooManyConsumers
  | Token
  | Arithmetic
  | Transactional
  | Exhausted
  | Corruption
  | Unavailable
  | RootNotAllowed
  .
End DispatchError.
Definition DispatchError := DispatchError.t.

Module multiaddress.
  Parameter MultiAddress : Set -> Set -> Set.
End multiaddress.

Parameter MultiSignature : Set.
