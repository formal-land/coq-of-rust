Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.revm.links.primitives.specification.

Module SpecId.
  Definition as_u8 (spec_id : SpecId.t) : Z :=
    match spec_id with
    | SpecId.FRONTIER => 0
    | SpecId.FRONTIER_THAWING => 1
    | SpecId.HOMESTEAD => 2
    | SpecId.DAO_FORK => 3
    | SpecId.TANGERINE => 4
    | SpecId.SPURIOUS_DRAGON => 5
    | SpecId.BYZANTIUM => 6
    | SpecId.CONSTANTINOPLE => 7
    | SpecId.PETERSBURG => 8
    | SpecId.ISTANBUL => 9
    | SpecId.MUIR_GLACIER => 10
    | SpecId.BERLIN => 11
    | SpecId.LONDON => 12
    | SpecId.ARROW_GLACIER => 13
    | SpecId.GRAY_GLACIER => 14
    | SpecId.MERGE => 15
    | SpecId.SHANGHAI => 16
    | SpecId.CANCUN => 17
    | SpecId.PRAGUE => 18
    | SpecId.LATEST => 255
    end.

  (*
    /// Returns `true` if the given specification ID is enabled in this spec.
    #[inline]
    pub const fn enabled(our: SpecId, other: SpecId) -> bool {
        our as u8 >= other as u8
    }
  *)
  Definition enabled (our other : SpecId.t) : bool :=
    as_u8 our >=? as_u8 other.
  
  (*
    /// Returns `true` if the given specification ID is enabled in this spec.
    #[inline]
    pub const fn is_enabled_in(self, other: Self) -> bool {
        Self::enabled(self, other)
    }
  *)

  Definition is_enabled_in (self other : SpecId.t) : bool :=
    enabled self other.
End SpecId.
