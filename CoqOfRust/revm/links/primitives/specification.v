Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
  /// Specification IDs and their activation block.
  ///
  /// Information was obtained from the [Ethereum Execution Specifications](https://github.com/ethereum/execution-specs)
  #[cfg(not(feature = "optimism"))]
  #[repr(u8)]
  #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, enumn::N)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum SpecId {
      FRONTIER = 0,         // Frontier               0
      FRONTIER_THAWING = 1, // Frontier Thawing       200000
      HOMESTEAD = 2,        // Homestead              1150000
      DAO_FORK = 3,         // DAO Fork               1920000
      TANGERINE = 4,        // Tangerine Whistle      2463000
      SPURIOUS_DRAGON = 5,  // Spurious Dragon        2675000
      BYZANTIUM = 6,        // Byzantium              4370000
      CONSTANTINOPLE = 7,   // Constantinople         7280000 is overwritten with PETERSBURG
      PETERSBURG = 8,       // Petersburg             7280000
      ISTANBUL = 9,         // Istanbul	            9069000
      MUIR_GLACIER = 10,    // Muir Glacier           9200000
      BERLIN = 11,          // Berlin	                12244000
      LONDON = 12,          // London	                12965000
      ARROW_GLACIER = 13,   // Arrow Glacier          13773000
      GRAY_GLACIER = 14,    // Gray Glacier           15050000
      MERGE = 15,           // Paris/Merge            15537394 (TTD: 58750000000000000000000)
      SHANGHAI = 16,        // Shanghai               17034870 (Timestamp: 1681338455)
      CANCUN = 17,          // Cancun                 19426587 (Timestamp: 1710338135)
      PRAGUE = 18,          // Praque                 TBD
      #[default]
      LATEST = u8::MAX,
  }
*)

Module SpecId.
  Inductive t : Set :=
    | FRONTIER
    | FRONTIER_THAWING
    | HOMESTEAD
    | DAO_FORK
    | TANGERINE
    | SPURIOUS_DRAGON
    | BYZANTIUM
    | CONSTANTINOPLE
    | PETERSBURG
    | ISTANBUL
    | MUIR_GLACIER
    | BERLIN
    | LONDON
    | ARROW_GLACIER
    | GRAY_GLACIER
    | MERGE
    | SHANGHAI
    | CANCUN
    | PRAGUE
    | LATEST.
    
  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::specification::SpecId";
  }.
    
  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | FRONTIER => Value.StructRecord "revm_primitives::specification::SpecId::FRONTIER" []
      | FRONTIER_THAWING => Value.StructRecord "revm_primitives::specification::SpecId::FRONTIER_THAWING" []
      | HOMESTEAD => Value.StructRecord "revm_primitives::specification::SpecId::HOMESTEAD" []
      | DAO_FORK => Value.StructRecord "revm_primitives::specification::SpecId::DAO_FORK" []
      | TANGERINE => Value.StructRecord "revm_primitives::specification::SpecId::TANGERINE" []
      | SPURIOUS_DRAGON => Value.StructRecord "revm_primitives::specification::SpecId::SPURIOUS_DRAGON" []
      | BYZANTIUM => Value.StructRecord "revm_primitives::specification::SpecId::BYZANTIUM" []
      | CONSTANTINOPLE => Value.StructRecord "revm_primitives::specification::SpecId::CONSTANTINOPLE" []
      | PETERSBURG => Value.StructRecord "revm_primitives::specification::SpecId::PETERSBURG" []
      | ISTANBUL => Value.StructRecord "revm_primitives::specification::SpecId::ISTANBUL" []
      | MUIR_GLACIER => Value.StructRecord "revm_primitives::specification::SpecId::MUIR_GLACIER" []
      | BERLIN => Value.StructRecord "revm_primitives::specification::SpecId::BERLIN" []
      | LONDON => Value.StructRecord "revm_primitives::specification::SpecId::LONDON" []
      | ARROW_GLACIER => Value.StructRecord "revm_primitives::specification::SpecId::ARROW_GLACIER" []
      | GRAY_GLACIER => Value.StructRecord "revm_primitives::specification::SpecId::GRAY_GLACIER" []
      | MERGE => Value.StructRecord "revm_primitives::specification::SpecId::MERGE" []
      | SHANGHAI => Value.StructRecord "revm_primitives::specification::SpecId::SHANGHAI" []
      | CANCUN => Value.StructRecord "revm_primitives::specification::SpecId::CANCUN" []
      | PRAGUE => Value.StructRecord "revm_primitives::specification::SpecId::PRAGUE" []
      | LATEST => Value.StructRecord "revm_primitives::specification::SpecId::LATEST" []
      end;
  }.
End SpecId.

(*
  pub trait Spec: Sized + 'static {
      /// The specification ID.
      const SPEC_ID: SpecId;

      /// Returns `true` if the given specification ID is enabled in this spec.
      #[inline]
      fn enabled(spec_id: SpecId) -> bool {
          SpecId::enabled(Self::SPEC_ID, spec_id)
      }
  }
*)

Module Spec.
  Record t : Set := {
    SPEC_ID : SpecId.t;
    enabled : SpecId.t -> bool;
  }.
End Spec.
