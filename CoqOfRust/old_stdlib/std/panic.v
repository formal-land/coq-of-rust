Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] AssertUnwindSafe
[x] Location
[x] PanicInfo
*)
(* pub struct AssertUnwindSafe<T>(pub T); *)
Module AssertUnwindSafe.
  Parameter t : forall (T : Set), Set.
End AssertUnwindSafe.
Definition AssertUnwindSafe := AssertUnwindSafe.t.

(* pub struct Location<'a> { /* private fields */ } *)
Module Location.
  Parameter t : Set.
End Location.
Definition Location := Location.t.

(* pub struct PanicInfo<'a> { /* private fields */ } *)
Module PanicInfo.
  Parameter t : Set.
End PanicInfo.
Definition PanicInfo := PanicInfo.t.

(* ********TRAITS******** *)
(*
[x] RefUnwindSafe
[x] UnwindSafe
*)
(* pub auto trait RefUnwindSafe { } *)
Module RefUnwindSafe.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End RefUnwindSafe.

(* pub auto trait UnwindSafe { } *)
Module UnsindSafe.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End UnsindSafe.



(* ********ENUMS******** *)
(*
[x] BacktraceStyle
*)
(* 
#[non_exhaustive]
pub enum BacktraceStyle {
    Short,
    Full,
    Off,
}
*)
Module BacktraceStyle.
  Inductive t : Set := 
  | Short
  | Full
  | Off
  .
End BacktraceStyle.
Definition BacktraceStyle := BacktraceStyle.t.

(* ********FUNCTIONS******** *)
(*
[ ] always_abort
[ ] get_backtrace_style
[ ] set_backtrace_style
[ ] update_hook
[ ] catch_unwind
[ ] panic_any
[ ] resume_unwind
[ ] set_hook
[ ] take_hook
*)
