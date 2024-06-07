Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
    /// State of the [`Bytecode`] analysis.
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    pub enum Bytecode {
        /// No analysis has been performed.
        LegacyRaw(Bytes),
        /// The bytecode has been analyzed for valid jump destinations.
        LegacyAnalyzed(LegacyAnalyzedBytecode),
        /// Ethereum Object Format
        Eof(Eof),
    }
*)

Module Bytecode.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::Bytecode";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Bytecode.
