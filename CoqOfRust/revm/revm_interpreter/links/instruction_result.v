Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.instruction_result.

Module InstructionResult.
Inductive t : Set :=
| Continue
| Stop
| Return
| SelfDestruct
| ReturnContract
| Revert
| CallTooDeep
| OutOfFunds
| CreateInitCodeStartingEF00
| InvalidEOFInitCode
| InvalidExtDelegateCallTarget
| CallOrCreate
| OutOfGas
| MemoryOOG
| MemoryLimitOOG
| PrecompileOOG
| InvalidOperandOOG
| ReentrancySentryOOG
| OpcodeNotFound
| CallNotAllowedInsideStatic
| StateChangeDuringStaticCall
| InvalidFEOpcode
| InvalidJump
| NotActivated
| StackUnderflow
| StackOverflow
| OutOfOffset
| CreateCollision
| OverflowPayment
| PrecompileError
| NonceOverflow
| CreateContractSizeLimit
| CreateContractStartingWithEF
| CreateInitCodeSizeLimit
| FatalExternalError
| ReturnContractInNotInitEOF
| EOFOpcodeDisabledInLegacy
| SubRoutineStackOverflow
| EofAuxDataOverflow
| EofAuxDataTooSmall
| InvalidEXTCALLTarget
.

Global Instance IsLink : Link t := {
  Φ := Ty.path "revm_interpreter::instruction_result::InstructionResult";
  φ x :=
    match x with
    | Continue =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
    | Stop =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
    | Return =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
    | SelfDestruct =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
    | ReturnContract =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
    | Revert =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
    | CallTooDeep =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
    | OutOfFunds =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
    | CreateInitCodeStartingEF00 =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
    | InvalidEOFInitCode =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
    | InvalidExtDelegateCallTarget =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
    | CallOrCreate =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
    | OutOfGas =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
    | MemoryOOG =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
    | MemoryLimitOOG =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
    | PrecompileOOG =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
    | InvalidOperandOOG =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
    | ReentrancySentryOOG =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
    | OpcodeNotFound =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
    | CallNotAllowedInsideStatic =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
    | StateChangeDuringStaticCall =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
    | InvalidFEOpcode =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
    | InvalidJump =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
    | NotActivated =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
    | StackUnderflow =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
    | StackOverflow =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
    | OutOfOffset =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
    | CreateCollision =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
    | OverflowPayment =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
    | PrecompileError =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
    | NonceOverflow =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
    | CreateContractSizeLimit =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
    | CreateContractStartingWithEF =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
    | CreateInitCodeSizeLimit =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
    | FatalExternalError =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
    | ReturnContractInNotInitEOF =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
    | EOFOpcodeDisabledInLegacy =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
    | SubRoutineStackOverflow =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" []
    | EofAuxDataOverflow =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" []
    | EofAuxDataTooSmall =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" []
    | InvalidEXTCALLTarget =>
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" []
    end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::InstructionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Continue :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" [] =
    φ Continue.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Continue : of_value.

  Lemma of_value_with_Stop :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" [] =
    φ Stop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Stop : of_value.

  Lemma of_value_with_Return :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" [] =
    φ Return.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_SelfDestruct :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" [] =
    φ SelfDestruct.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SelfDestruct : of_value.

  Lemma of_value_with_ReturnContract :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" [] =
    φ ReturnContract.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnContract : of_value.

  Lemma of_value_with_Revert :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" [] =
    φ Revert.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_CallTooDeep :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" [] =
    φ CallTooDeep.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallTooDeep : of_value.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_CreateInitCodeStartingEF00 :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" [] =
    φ CreateInitCodeStartingEF00.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeStartingEF00 : of_value.

  Lemma of_value_with_InvalidEOFInitCode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" [] =
    φ InvalidEOFInitCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFInitCode : of_value.

  Lemma of_value_with_InvalidExtDelegateCallTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" [] =
    φ InvalidExtDelegateCallTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidExtDelegateCallTarget : of_value.

  Lemma of_value_with_CallOrCreate :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" [] =
    φ CallOrCreate.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallOrCreate : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_MemoryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" [] =
    φ MemoryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryOOG : of_value.

  Lemma of_value_with_MemoryLimitOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" [] =
    φ MemoryLimitOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryLimitOOG : of_value.

  Lemma of_value_with_PrecompileOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" [] =
    φ PrecompileOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileOOG : of_value.

  Lemma of_value_with_InvalidOperandOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" [] =
    φ InvalidOperandOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidOperandOOG : of_value.

  Lemma of_value_with_ReentrancySentryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" [] =
    φ ReentrancySentryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReentrancySentryOOG : of_value.

  Lemma of_value_with_OpcodeNotFound :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" [] =
    φ OpcodeNotFound.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeNotFound : of_value.

  Lemma of_value_with_CallNotAllowedInsideStatic :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" [] =
    φ CallNotAllowedInsideStatic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallNotAllowedInsideStatic : of_value.

  Lemma of_value_with_StateChangeDuringStaticCall :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" [] =
    φ StateChangeDuringStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StateChangeDuringStaticCall : of_value.

  Lemma of_value_with_InvalidFEOpcode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" [] =
    φ InvalidFEOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFEOpcode : of_value.

  Lemma of_value_with_InvalidJump :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" [] =
    φ InvalidJump.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidJump : of_value.

  Lemma of_value_with_NotActivated :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" [] =
    φ NotActivated.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NotActivated : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_OutOfOffset :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" [] =
    φ OutOfOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfOffset : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_PrecompileError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" [] =
    φ PrecompileError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileError : of_value.

  Lemma of_value_with_NonceOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" [] =
    φ NonceOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflow : of_value.

  Lemma of_value_with_CreateContractSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" [] =
    φ CreateContractSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractSizeLimit : of_value.

  Lemma of_value_with_CreateContractStartingWithEF :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" [] =
    φ CreateContractStartingWithEF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractStartingWithEF : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_FatalExternalError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" [] =
    φ FatalExternalError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FatalExternalError : of_value.

  Lemma of_value_with_ReturnContractInNotInitEOF :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" [] =
    φ ReturnContractInNotInitEOF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnContractInNotInitEOF : of_value.

  Lemma of_value_with_EOFOpcodeDisabledInLegacy :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" [] =
    φ EOFOpcodeDisabledInLegacy.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EOFOpcodeDisabledInLegacy : of_value.

  Lemma of_value_with_SubRoutineStackOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" [] =
    φ SubRoutineStackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SubRoutineStackOverflow : of_value.

  Lemma of_value_with_EofAuxDataOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" [] =
    φ EofAuxDataOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataOverflow : of_value.

  Lemma of_value_with_EofAuxDataTooSmall :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" [] =
    φ EofAuxDataTooSmall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataTooSmall : of_value.

  Lemma of_value_with_InvalidEXTCALLTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" [] =
    φ InvalidEXTCALLTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEXTCALLTarget : of_value.

  Definition of_value_Continue :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
    ).
  Proof. econstructor; apply of_value_with_Continue; eassumption. Defined.
  Smpl Add simple apply of_value_Continue : of_value.

  Definition of_value_Stop :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
    ).
  Proof. econstructor; apply of_value_with_Stop; eassumption. Defined.
  Smpl Add simple apply of_value_Stop : of_value.

  Definition of_value_Return :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_SelfDestruct :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
    ).
  Proof. econstructor; apply of_value_with_SelfDestruct; eassumption. Defined.
  Smpl Add simple apply of_value_SelfDestruct : of_value.

  Definition of_value_ReturnContract :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
    ).
  Proof. econstructor; apply of_value_with_ReturnContract; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnContract : of_value.

  Definition of_value_Revert :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_CallTooDeep :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
    ).
  Proof. econstructor; apply of_value_with_CallTooDeep; eassumption. Defined.
  Smpl Add simple apply of_value_CallTooDeep : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_CreateInitCodeStartingEF00 :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeStartingEF00; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeStartingEF00 : of_value.

  Definition of_value_InvalidEOFInitCode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFInitCode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFInitCode : of_value.

  Definition of_value_InvalidExtDelegateCallTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidExtDelegateCallTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidExtDelegateCallTarget : of_value.

  Definition of_value_CallOrCreate :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
    ).
  Proof. econstructor; apply of_value_with_CallOrCreate; eassumption. Defined.
  Smpl Add simple apply of_value_CallOrCreate : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_MemoryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryOOG : of_value.

  Definition of_value_MemoryLimitOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryLimitOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryLimitOOG : of_value.

  Definition of_value_PrecompileOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileOOG; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileOOG : of_value.

  Definition of_value_InvalidOperandOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
    ).
  Proof. econstructor; apply of_value_with_InvalidOperandOOG; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidOperandOOG : of_value.

  Definition of_value_ReentrancySentryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
    ).
  Proof. econstructor; apply of_value_with_ReentrancySentryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_ReentrancySentryOOG : of_value.

  Definition of_value_OpcodeNotFound :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeNotFound; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeNotFound : of_value.

  Definition of_value_CallNotAllowedInsideStatic :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
    ).
  Proof. econstructor; apply of_value_with_CallNotAllowedInsideStatic; eassumption. Defined.
  Smpl Add simple apply of_value_CallNotAllowedInsideStatic : of_value.

  Definition of_value_StateChangeDuringStaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StateChangeDuringStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StateChangeDuringStaticCall : of_value.

  Definition of_value_InvalidFEOpcode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFEOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFEOpcode : of_value.

  Definition of_value_InvalidJump :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
    ).
  Proof. econstructor; apply of_value_with_InvalidJump; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidJump : of_value.

  Definition of_value_NotActivated :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
    ).
  Proof. econstructor; apply of_value_with_NotActivated; eassumption. Defined.
  Smpl Add simple apply of_value_NotActivated : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_OutOfOffset :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
    ).
  Proof. econstructor; apply of_value_with_OutOfOffset; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfOffset : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_PrecompileError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileError; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileError : of_value.

  Definition of_value_NonceOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflow : of_value.

  Definition of_value_CreateContractSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractSizeLimit : of_value.

  Definition of_value_CreateContractStartingWithEF :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractStartingWithEF; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractStartingWithEF : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_FatalExternalError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
    ).
  Proof. econstructor; apply of_value_with_FatalExternalError; eassumption. Defined.
  Smpl Add simple apply of_value_FatalExternalError : of_value.

  Definition of_value_ReturnContractInNotInitEOF :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
    ).
  Proof. econstructor; apply of_value_with_ReturnContractInNotInitEOF; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnContractInNotInitEOF : of_value.

  Definition of_value_EOFOpcodeDisabledInLegacy :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
    ).
  Proof. econstructor; apply of_value_with_EOFOpcodeDisabledInLegacy; eassumption. Defined.
  Smpl Add simple apply of_value_EOFOpcodeDisabledInLegacy : of_value.

  Definition of_value_SubRoutineStackOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_SubRoutineStackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_SubRoutineStackOverflow : of_value.

  Definition of_value_EofAuxDataOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataOverflow : of_value.

  Definition of_value_EofAuxDataTooSmall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataTooSmall; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataTooSmall : of_value.

  Definition of_value_InvalidEXTCALLTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEXTCALLTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEXTCALLTarget : of_value.
End InstructionResult.

Module Impl_InstructionResult.
  Definition Self : Set :=
    InstructionResult.t.

  (* pub const fn is_ok(self) -> bool *)
  Instance run_is_ok (self : Self) :
    Run.Trait
      instruction_result.Impl_revm_interpreter_instruction_result_InstructionResult.is_ok
        [] [] [ φ self ]
      bool.
  Proof.
    (* This file is too slow. There a lot of constructors, and we need to find a way to optimize
       that! *)
    (* Time destruct self; run. *)
  Admitted.

  (* pub const fn is_ok_or_revert(self) -> bool *)
  Instance run_is_ok_or_revert (self : Self) :
    Run.Trait
      instruction_result.Impl_revm_interpreter_instruction_result_InstructionResult.is_ok_or_revert
        [] [] [ φ self ]
      bool.
  Proof.
    (* Time destruct self; run.
  Defined. *)
  Admitted.

  (* pub const fn is_continue(self) -> bool *)
  Instance run_is_continue (self : Self) :
    Run.Trait
      instruction_result.Impl_revm_interpreter_instruction_result_InstructionResult.is_continue
        [] [] [ φ self ]
      bool.
  Proof.
    (* This is the only one that is fast in this file, for some reasons! *)
    constructor.
    destruct self;
      run_next;
      RunTactic.unfold_link_in_match;
      run_next.
  Defined.

  (* pub const fn is_revert(self) -> bool *)
  Instance run_is_revert (self : Self) :
    Run.Trait
      instruction_result.Impl_revm_interpreter_instruction_result_InstructionResult.is_revert
        [] [] [ φ self ]
      bool.
  Proof.
  Admitted.
    (* Time destruct self; run.
  Defined. *)

  (* pub const fn is_error(self) -> bool *)
  Instance run_is_error (self : Self) :
    Run.Trait
      instruction_result.Impl_revm_interpreter_instruction_result_InstructionResult.is_error
        [] [] [ φ self ]
      bool.
  Proof.
  Admitted.
    (* Time destruct self; run.
  Defined. *)
End Impl_InstructionResult.
