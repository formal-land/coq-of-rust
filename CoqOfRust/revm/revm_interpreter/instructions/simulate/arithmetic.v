Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Definition make_ref {A : Set} `{Link A} {kind : Pointer.Kind.t} (index : nat) : Ref.t kind A :=
  {| Ref.core := Ref.Core.Mutable (A := A) index [] φ Some (fun _ => Some) |}.

Module Stack.
  Class C (WIRE_types : InterpreterTypes.Types.t) : Set := {
    popn_top :
      forall
        (POPN : Usize.t)
        (self : WIRE_types.(InterpreterTypes.Types.Stack)),
      (option (array.t aliases.U256.t POPN * Z)) *
      WIRE_types.(InterpreterTypes.Types.Stack);
  }.

  Module Eq.
    Record t
        {WIRE : Set} `{Link WIRE}
        {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      popn_top
          (Stack : list Set) (stack : Stack.to_Set Stack)
          (POPN : Usize.t)
          (self : WIRE_types.(InterpreterTypes.Types.Stack)) :
        let ref_self := make_ref 0 in
        {{
          StackM.eval_f (Stack := WIRE_types.(InterpreterTypes.Types.Stack) :: Stack)
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_StackTrait_for_Stack).(StackTrait.popn_top).(TraitMethod.run)
              POPN
              ref_self
            )
            (self, stack) 🌲
          (Output.Success None, (self, stack))
        }};
    }.
  End Eq.
End Stack.

(*
  {{StackM.eval
      (evaluate
         (run_InterpreterTypes_for_WIRE
          .(InterpreterTypes.run_StackTrait_for_Stack).(
          StackTrait.popn_top).(TraitMethod.run) {| Integer.value := 1 |}
            (Ref.cast_to Pointer.Kind.MutRef
               {|
                 Ref.core :=
                   Ref.Core.Mutable 0%nat
                     [Pointer.Index.StructRecord
                     "revm_interpreter::interpreter::Interpreter" "stack"]
                     Interpreter.IsLink.(φ)
                     (fun big_a : Interpreter.t WIRE WIRE_types =>
                      Some big_a.(Interpreter.stack))
                     (fun (big_a : Interpreter.t WIRE WIRE_types)
                        (new_sub_a : WIRE_types
                                     .(InterpreterTypes.Types.Stack)) =>
                      Some big_a<|Interpreter.stack:= new_sub_a|>)
               |})).(run_f))
      (interpreter, (_host, (ref_interpreter, ref_host))) 🌲 
  ?value_inter}}
*)
(* Lemma foo
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (POPN : Usize.t)
    (self : WIRE_types.(InterpreterTypes.Types.Stack)) :
  let ref_self := make_ref 0 in
  {{
    StackM.eval_f (Stack := [_])
      (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_StackTrait_for_Stack).(StackTrait.popn_top).(TraitMethod.run)
        POPN
        ref_self
      )
      self 🌲
    (Output.Success None, self)
  }}. *)

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    StackM.eval_f (Stack := [_; _]) (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host) (interpreter, _host) 🌲
    (Output.Success tt, (interpreter, _host))
  }}.
Proof.
  intros.
  Time unfold run_add, StackM.eval_f, StackM.eval, evaluate.
  Time hnf.
  Time cbn.
  Time get_can_access.
  Time cbn.
  Time eapply Run.Call. {
    Print Output.t.
  }
  Show.
  
Qed.
