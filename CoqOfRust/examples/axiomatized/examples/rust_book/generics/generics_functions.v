(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "A";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

(* StructTuple
  {
    name := "S";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "generics_functions::A" ];
  } *)

(* StructTuple
  {
    name := "SGen";
    const_params := [];
    ty_params := [ "T" ];
    fields := [ T ];
  } *)

Parameter reg_fn : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_reg_fn : M.IsFunction.C "generics_functions::reg_fn" reg_fn.
Admitted.

Parameter gen_spec_t : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_gen_spec_t :
  M.IsFunction.C "generics_functions::gen_spec_t" gen_spec_t.
Admitted.

Parameter gen_spec_i32 : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_gen_spec_i32 :
  M.IsFunction.C "generics_functions::gen_spec_i32" gen_spec_i32.
Admitted.

Parameter generic : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_generic : M.IsFunction.C "generics_functions::generic" generic.
Admitted.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.C "generics_functions::main" main.
Admitted.
