Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require core.links.option.
Require Import revm.revm_specification.hardfork.

Import Run.

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
  | OSAKA
  | LATEST
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_specification::hardfork::SpecId";
    φ x :=
      match x with
      | FRONTIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" []
      | FRONTIER_THAWING  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" []
      | HOMESTEAD  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" []
      | DAO_FORK  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" []
      | TANGERINE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" []
      | SPURIOUS_DRAGON  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" []
      | BYZANTIUM  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" []
      | CONSTANTINOPLE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" []
      | PETERSBURG  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" []
      | ISTANBUL  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" []
      | MUIR_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" []
      | BERLIN  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" []
      | LONDON  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" []
      | ARROW_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" []
      | GRAY_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" []
      | MERGE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" []
      | SHANGHAI  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" []
      | CANCUN  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" []
      | PRAGUE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" []
      | OSAKA  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" []
      | LATEST  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" []
      end
  }.
End SpecId.

Module Impl_SpecId.
  Definition Self : Set := SpecId.t.

  Definition run_n (spec_id : U8.t) :
    {{
      hardfork.Impl_revm_specification_hardfork_SpecId.n [] [] [ φ spec_id ] 🔽
      option Self
    }}.
  Proof.
    run_symbolic.
  Admitted.
  Smpl Add apply run_n : run_closure.

  Definition run_try_from_u8 (spec_id : U8.t) :
    {{
      hardfork.Impl_revm_specification_hardfork_SpecId.try_from_u8 [] [] [ φ spec_id ] 🔽
      option Self
    }}.
  Proof.
    run_symbolic.
  Admitted.
  Smpl Add apply run_try_from_u8 : run_closure.
End Impl_SpecId.
