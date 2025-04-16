Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.instructions.host.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_context_interface.links.journaled_state.

(*
pub fn balance<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_balance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.balance [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct Impl_IntoAddress_for_U256.run.
  (* 
  {{LowM.CallClosure
    (Ty.apply
       (Ty.path
          "core::option::Option") []
       [Ty.apply
          (Ty.path
             "revm_context_interface::journaled_state::StateLoad")
  Seems like LowM has some issue to make calls properly after the type annotation update?...
  *)
  run_symbolic.
Admitted.

(*
pub fn selfbalance<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)

Instance run_selfbalance
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.selfbalance [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* NOTE: for this instance of `Self`, Coq will complain that it is not a inductive definition *)
  (* destruct (links.interpreter_types.InputsTrait.Run_target_address 
    WIRE_types.(InterpreterTypes.Types.Input)). *)
  run_symbolic.
Admitted.

(*
pub fn extcodesize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodesize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodesize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    aliases.U256.t.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  (* destruct run_Host_for_H. *)
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO: "revm_interpreter::instructions::utility::IntoAddress::into_address" *)
  run_symbolic.
  (* - apply aliases.U256.t. 
  Coq seems to say the goal being a Type while U256.t being defined is a Set?...
  *)
Admitted.

(*
pub fn extcodehash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodehash
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodehash [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    aliases.U256.t.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  (* destruct run_Host_for_H. *)
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - Value.Tuple [] = lib.Uint.IsLink.(φ) ?return_
  ^ (?What is this?)
  *)
  run_symbolic.
Admitted.

(*
pub fn extcodecopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodecopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodecopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  (* destruct run_Host_for_H. *)
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - "revm_interpreter::instructions::utility::IntoAddress"::into_address
  ^ with a correct instance of Self maybe?
  *)
  run_symbolic.
Admitted.

(*
pub fn blockhash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_blockhash
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.blockhash [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    aliases.U256.t.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  (* destruct run_Host_for_H. *)
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - Value.Tuple [] = lib.Uint.IsLink.(φ) ?return_
  *)
  run_symbolic.
Admitted.

(*
pub fn sload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_sload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.sload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    aliases.U256.t.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - revm_interpreter::interpreter_types::InputsTrait::target_address
  ^ `Self` issue?
  *)
  run_symbolic.
Admitted.

(*
pub fn sstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_sstore
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.sstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - "revm_interpreter::interpreter_types::InputsTrait"::target_address
  *)
  run_symbolic.
Admitted.

(*
pub fn tstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_tstore
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}  
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.tstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO:
  - "revm_interpreter::interpreter_types::InputsTrait"::target_address
  *)
  run_symbolic.
Admitted.

(*
pub fn tload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_tload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.tload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    aliases.U256.t.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  run_symbolic.
Admitted.

(*
pub fn log<const N: usize, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
(* TODO: fill in parameter `N` : usize *)
Instance run_log
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.log [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO: 
  - {{impossible "wrong number of arguments" 🔽 unit}}
  *)
  (* run_symbolic. *)
Admitted.

(*
pub fn selfdestruct<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_selfdestruct
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.selfdestruct [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  (* TODO: 
  - "revm_interpreter::instructions::utility::IntoAddress"::into_address
  *)
  run_symbolic.
Admitted.
