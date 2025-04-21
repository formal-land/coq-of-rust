Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

(* 
/// Dynamic config options for the Move VM.
pub struct VMConfig {
    pub verifier: VerifierConfig,
    pub max_binary_format_version: u32,
    pub runtime_limits_config: VMRuntimeLimitsConfig,
    // When this flag is set to true, MoveVM will check invariant violation in swap_loc
    pub enable_invariant_violation_check_in_swap_loc: bool,
    // When this flag is set to true, MoveVM will check that there are no trailing bytes after
    // deserializing and check for no metadata bytes
    pub check_no_extraneous_bytes_during_deserialization: bool,
    // Configs for profiling VM
    pub profiler_config: Option<VMProfilerConfig>,
    // When this flag is set to true, errors from the VM will be augmented with execution state
    // (stacktrace etc.)
    pub error_execution_state: bool,
    // configuration for binary deserialization (modules)
    pub binary_config: BinaryConfig,
}
*)
Module VMConfig.
  Record t : Set := {
    (* verifier : VerifierConfig.t; *)
    (* max_binary_format_version : Z; *)
    (* runtime_limits_config : VMRuntimeLimitsConfig.t; *)
    enable_invariant_violation_check_in_swap_loc : bool;
    check_no_extraneous_bytes_during_deserialization : bool;
    (* profiler_config : option VMProfilerConfig.t; *)
    error_execution_state : bool;
    (* binary_config : BinaryConfig.t; *)
  }.
End VMConfig.