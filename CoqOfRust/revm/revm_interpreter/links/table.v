Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.links.interpreter_Interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.table.

Import Run.

(*
pub type Instruction<W, H> = for<'a> fn(&'a mut Interpreter<W>, &'a mut H);
*)
Module Instruction.
  Definition t
      (W H : Set) `{Link W} `{Link H}
      (W_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks W_types} :
      Set :=
    Function2.t
      (Ref.t Pointer.Kind.MutRef (Interpreter.t W W_types))
      (Ref.t Pointer.Kind.MutRef H)
      unit.
End Instruction.

(*
pub trait CustomInstruction {
    type Wire: InterpreterTypes;
    type Host;

    fn exec(&self, interpreter: &mut Interpreter<Self::Wire>, host: &mut Self::Host);

    fn from_base(instruction: Instruction<Self::Wire, Self::Host>) -> Self;
}
*)
Module CustomInstruction.
  Definition run_exec
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} :
      Set :=
    {exec @
      IsTraitMethod.t "revm_interpreter::table::CustomInstruction" [] [] (Φ Self) "exec" exec *
      forall
          (self : Ref.t Pointer.Kind.Ref Self)
          (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t Wire Wire_types))
          (host : Ref.t Pointer.Kind.MutRef Host),
        {{ exec [] [] [ φ self; φ interpreter; φ host ] 🔽 unit }}
    }.

  Definition run_from_base
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} :
      Set :=
    {from_base @
      IsTraitMethod.t "revm_interpreter::table::CustomInstruction" [] [] (Φ Self) "from_base" from_base *
      forall
          (instruction : Ref.t Pointer.Kind.Ref (Instruction.t Wire Host Wire_types)),
        {{ from_base [] [] [ φ instruction ] 🔽 Ref.t Pointer.Kind.Ref Self }}
    }.

  Class Run
      (Self : Set) `{Link Self}
      (Wire : Set) `{Link Wire}
      (Wire_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks Wire_types}
      (Host : Set) `{Link Host} : Set := {
    Wire_IsAssociated :
      IsTraitAssociatedType
      "revm_interpreter::table::CustomInstruction" [] [] (Φ Self)
      "Wire" (Φ Wire);
    run_InterpreterTypes_for_Wire : InterpreterTypes.Run Wire Wire_types;
    Host_IsAssociated :
      IsTraitAssociatedType
      "revm_interpreter::table::CustomInstruction" [] [] (Φ Self)
      "Host" (Φ Host);
    exec : run_exec Self Wire Wire_types Host;
    from_base : run_from_base Self Wire Wire_types Host;
  }.
End CustomInstruction.
