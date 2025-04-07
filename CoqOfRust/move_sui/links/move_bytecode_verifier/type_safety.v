Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import move_sui.translations.move_bytecode_verifier.type_safety.

(*
struct TypeSafetyChecker<'a> {
    module: &'a CompiledModule,
    function_context: &'a FunctionContext<'a>,
    locals: Locals<'a>,
    stack: AbstractStack<SignatureToken>,
}
*)
Module TypeSafetyChecker.
  Record t : Set := {
    module : Ref.t Pointer.Kind.Ref CompiledModule.t;
    function_context : Ref.t Pointer.Kind.Ref (FunctionContext.t t);
    locals : Locals.t;
    stack : AbstractStack.t SignatureToken.t;
  }.
End TypeSafetyChecker.

(*
fn verify_instr(
    verifier: &mut TypeSafetyChecker,
    bytecode: &Bytecode,
    offset: CodeOffset,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()>
*)
Definition run_verify_instr
    (verifier : Ref.t Pointer.Kind.MutRef TypeSafetyChecker.t)
    (bytecode : Ref.t Pointer.Kind.Ref Bytecode.t)
    (offset : CodeOffset.t)
    (meter : Ref.t Pointer.Kind.MutRef (Meter.t + ?Sized)) :
  {{
    move_bytecode_verifier::type_safety::verify_instr
      [TypeSafetyChecker_ty; Bytecode_ty; CodeOffset_ty; Meter_ty]
      [ φ verifier; φ bytecode; φ offset; φ meter ] ⇓
    output_pure (PartialVMResult.t unit)
  }}.

(*
    pub trait Default: Sized {
        // Required method
        fn default() -> Self;
    }
*)
Module Default.
  Definition Run_default (Self : Set) `{Link Self} : Set :=
    {default @
      IsTraitMethod.t "core::default::Default" (to_ty Self) [] "default" default *
      {{
        default [] [] [] ⇓
        output_pure Self
      }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    default : Run_default Self;
  }.
End Default.

Module Impl_Default_for_unit.
  Definition Self : Set := unit.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_Tuple_.Implements. }
      { reflexivity. }
    }
    { cbn.
      eapply Run.Pure.
      now instantiate (1 := tt).
    }
  Defined.

  Definition run : Default.Run Self.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_unit.

Module Impl_Default_for_bool.
  Definition Self : Set := bool.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_bool.Implements. }
      { reflexivity. }
    }
    { cbn; eapply Run.Pure.
      now instantiate (1 := false).
    }
  Defined.

  Definition run : Default.Run Self.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_bool.

Module Impl_Default_for_char.
  (* TODO *)
End Impl_Default_for_char.

Module Impl_Default_for_integer.
  Definition Self (kind : IntegerKind.t) : Set :=
    Integer.t kind.

  Definition method_of_ingeter_kind (kind : IntegerKind.t) :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.default
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.default
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.default
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.default
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.default
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.default
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.default
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.default
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.default
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.default
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.default
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.default
    end.

  Definition implements_of_integer_kind (kind : IntegerKind.t) :
      IsTraitInstance "core::default::Default"
        (to_ty (Self kind))
        []
        [("default", InstanceField.Method (method_of_ingeter_kind kind))] :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.Implements
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.Implements
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.Implements
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.Implements
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.Implements
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.Implements
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.Implements
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.Implements
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.Implements
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.Implements
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.Implements
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.Implements
    end.

  Definition run_default (kind : IntegerKind.t) : Default.Run_default (Self kind).
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply implements_of_integer_kind. }
      { reflexivity. }
    }
    { destruct kind; cbn; eapply Run.Pure;
        now instantiate (1 := Integer.Make 0).
    }
  Defined.

  Definition run (kind : IntegerKind.t) : Default.Run (Self kind).
  Proof.
    constructor.
    { (* default *)
      apply run_default.
    }
  Defined.
End Impl_Default_for_integer.
