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

  Definition of_ty : OfTy.t (Ty.path "revm_specification::hardfork::SpecId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_FRONTIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" [] =
    φ FRONTIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER : of_value.

  Lemma of_value_with_FRONTIER_THAWING :
    Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" [] =
    φ FRONTIER_THAWING.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER_THAWING : of_value.

  Lemma of_value_with_HOMESTEAD :
    Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" [] =
    φ HOMESTEAD.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_HOMESTEAD : of_value.

  Lemma of_value_with_DAO_FORK :
    Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" [] =
    φ DAO_FORK.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DAO_FORK : of_value.

  Lemma of_value_with_TANGERINE :
    Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" [] =
    φ TANGERINE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TANGERINE : of_value.

  Lemma of_value_with_SPURIOUS_DRAGON :
    Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" [] =
    φ SPURIOUS_DRAGON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SPURIOUS_DRAGON : of_value.

  Lemma of_value_with_BYZANTIUM :
    Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" [] =
    φ BYZANTIUM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BYZANTIUM : of_value.

  Lemma of_value_with_CONSTANTINOPLE :
    Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" [] =
    φ CONSTANTINOPLE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CONSTANTINOPLE : of_value.

  Lemma of_value_with_PETERSBURG :
    Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" [] =
    φ PETERSBURG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PETERSBURG : of_value.

  Lemma of_value_with_ISTANBUL :
    Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" [] =
    φ ISTANBUL.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ISTANBUL : of_value.

  Lemma of_value_with_MUIR_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" [] =
    φ MUIR_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MUIR_GLACIER : of_value.

  Lemma of_value_with_BERLIN :
    Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" [] =
    φ BERLIN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BERLIN : of_value.

  Lemma of_value_with_LONDON :
    Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" [] =
    φ LONDON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LONDON : of_value.

  Lemma of_value_with_ARROW_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" [] =
    φ ARROW_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ARROW_GLACIER : of_value.

  Lemma of_value_with_GRAY_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" [] =
    φ GRAY_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GRAY_GLACIER : of_value.

  Lemma of_value_with_MERGE :
    Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" [] =
    φ MERGE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MERGE : of_value.

  Lemma of_value_with_SHANGHAI :
    Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" [] =
    φ SHANGHAI.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SHANGHAI : of_value.

  Lemma of_value_with_CANCUN :
    Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" [] =
    φ CANCUN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CANCUN : of_value.

  Lemma of_value_with_PRAGUE :
    Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" [] =
    φ PRAGUE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PRAGUE : of_value.

  Lemma of_value_with_OSAKA :
    Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" [] =
    φ OSAKA.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OSAKA : of_value.

  Lemma of_value_with_LATEST :
    Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" [] =
    φ LATEST.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LATEST : of_value.

  Definition of_value_FRONTIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER : of_value.

  Definition of_value_FRONTIER_THAWING :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER_THAWING; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER_THAWING : of_value.

  Definition of_value_HOMESTEAD :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" []
    ).
  Proof. econstructor; apply of_value_with_HOMESTEAD; eassumption. Defined.
  Smpl Add simple apply of_value_HOMESTEAD : of_value.

  Definition of_value_DAO_FORK :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" []
    ).
  Proof. econstructor; apply of_value_with_DAO_FORK; eassumption. Defined.
  Smpl Add simple apply of_value_DAO_FORK : of_value.

  Definition of_value_TANGERINE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" []
    ).
  Proof. econstructor; apply of_value_with_TANGERINE; eassumption. Defined.
  Smpl Add simple apply of_value_TANGERINE : of_value.

  Definition of_value_SPURIOUS_DRAGON :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" []
    ).
  Proof. econstructor; apply of_value_with_SPURIOUS_DRAGON; eassumption. Defined.
  Smpl Add simple apply of_value_SPURIOUS_DRAGON : of_value.

  Definition of_value_BYZANTIUM :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" []
    ).
  Proof. econstructor; apply of_value_with_BYZANTIUM; eassumption. Defined.
  Smpl Add simple apply of_value_BYZANTIUM : of_value.

  Definition of_value_CONSTANTINOPLE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" []
    ).
  Proof. econstructor; apply of_value_with_CONSTANTINOPLE; eassumption. Defined.
  Smpl Add simple apply of_value_CONSTANTINOPLE : of_value.

  Definition of_value_PETERSBURG :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" []
    ).
  Proof. econstructor; apply of_value_with_PETERSBURG; eassumption. Defined.
  Smpl Add simple apply of_value_PETERSBURG : of_value.

  Definition of_value_ISTANBUL :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" []
    ).
  Proof. econstructor; apply of_value_with_ISTANBUL; eassumption. Defined.
  Smpl Add simple apply of_value_ISTANBUL : of_value.

  Definition of_value_MUIR_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_MUIR_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_MUIR_GLACIER : of_value.

  Definition of_value_BERLIN :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" []
    ).
  Proof. econstructor; apply of_value_with_BERLIN; eassumption. Defined.
  Smpl Add simple apply of_value_BERLIN : of_value.

  Definition of_value_LONDON :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" []
    ).
  Proof. econstructor; apply of_value_with_LONDON; eassumption. Defined.
  Smpl Add simple apply of_value_LONDON : of_value.

  Definition of_value_ARROW_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_ARROW_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_ARROW_GLACIER : of_value.

  Definition of_value_GRAY_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_GRAY_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_GRAY_GLACIER : of_value.

  Definition of_value_MERGE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" []
    ).
  Proof. econstructor; apply of_value_with_MERGE; eassumption. Defined.
  Smpl Add simple apply of_value_MERGE : of_value.

  Definition of_value_SHANGHAI :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" []
    ).
  Proof. econstructor; apply of_value_with_SHANGHAI; eassumption. Defined.
  Smpl Add simple apply of_value_SHANGHAI : of_value.

  Definition of_value_CANCUN :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" []
    ).
  Proof. econstructor; apply of_value_with_CANCUN; eassumption. Defined.
  Smpl Add simple apply of_value_CANCUN : of_value.

  Definition of_value_PRAGUE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" []
    ).
  Proof. econstructor; apply of_value_with_PRAGUE; eassumption. Defined.
  Smpl Add simple apply of_value_PRAGUE : of_value.

  Definition of_value_OSAKA :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" []
    ).
  Proof. econstructor; apply of_value_with_OSAKA; eassumption. Defined.
  Smpl Add simple apply of_value_OSAKA : of_value.

  Definition of_value_LATEST :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" []
    ).
  Proof. econstructor; apply of_value_with_LATEST; eassumption. Defined.
  Smpl Add simple apply of_value_LATEST : of_value.

  Definition get_discriminant (x : t) : Z :=
    match x with
    | FRONTIER => 0
    | FRONTIER_THAWING => 1
    | HOMESTEAD => 2
    | DAO_FORK => 3
    | TANGERINE => 4
    | SPURIOUS_DRAGON => 5
    | BYZANTIUM => 6
    | CONSTANTINOPLE => 7
    | PETERSBURG => 8
    | ISTANBUL => 9
    | MUIR_GLACIER => 10
    | BERLIN => 11
    | LONDON => 12
    | ARROW_GLACIER => 13
    | GRAY_GLACIER => 14
    | MERGE => 15
    | SHANGHAI => 16
    | CANCUN => 17
    | PRAGUE => 18
    | OSAKA => 19
    | LATEST => 20
    end.

  Lemma cast_integer_eq (kind : IntegerKind.t) (x : t) :
    M.cast (Φ (Integer.t kind)) (φ x) =
    Value.Integer kind (Integer.normalize_wrap kind (get_discriminant x)).
  Proof.
    destruct x;
      with_strategy transparent [φ] cbn;
      apply M.is_discriminant_tuple_eq;
      (
        apply hardfork.IsDiscriminant_SpecId_FRONTIER ||
        apply hardfork.IsDiscriminant_SpecId_FRONTIER_THAWING ||
        apply hardfork.IsDiscriminant_SpecId_HOMESTEAD ||
        apply hardfork.IsDiscriminant_SpecId_DAO_FORK ||
        apply hardfork.IsDiscriminant_SpecId_TANGERINE ||
        apply hardfork.IsDiscriminant_SpecId_SPURIOUS_DRAGON ||
        apply hardfork.IsDiscriminant_SpecId_BYZANTIUM ||
        apply hardfork.IsDiscriminant_SpecId_CONSTANTINOPLE ||
        apply hardfork.IsDiscriminant_SpecId_PETERSBURG ||
        apply hardfork.IsDiscriminant_SpecId_ISTANBUL ||
        apply hardfork.IsDiscriminant_SpecId_MUIR_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_BERLIN ||
        apply hardfork.IsDiscriminant_SpecId_LONDON ||
        apply hardfork.IsDiscriminant_SpecId_ARROW_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_GRAY_GLACIER ||
        apply hardfork.IsDiscriminant_SpecId_MERGE ||
        apply hardfork.IsDiscriminant_SpecId_SHANGHAI ||
        apply hardfork.IsDiscriminant_SpecId_CANCUN ||
        apply hardfork.IsDiscriminant_SpecId_PRAGUE ||
        apply hardfork.IsDiscriminant_SpecId_OSAKA ||
        apply hardfork.IsDiscriminant_SpecId_LATEST
      ).
  Qed.
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
    repeat (
      run_symbolic_are_equal_integer;
      run_symbolic
    ).
  Defined.
  Smpl Add simple apply run_n : run_closure.

  Definition run_try_from_u8 (spec_id : U8.t) :
    {{
      hardfork.Impl_revm_specification_hardfork_SpecId.try_from_u8 [] [] [ φ spec_id ] 🔽
      option Self
    }}.
  Proof.
    run_symbolic.
    run_symbolic_closure. {
      apply run_n.
    }
    intros []; run_symbolic.
  Defined.
  Smpl Add simple apply run_try_from_u8 : run_closure.

  Definition run_is_enabled_in (self other : Self) :
    {{
      hardfork.Impl_revm_specification_hardfork_SpecId.is_enabled_in [] [] [ φ self; φ other ] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    change_cast_integer.
    eapply Run.Rewrite. {
      do 2 rewrite SpecId.cast_integer_eq.
      reflexivity.
    }
    run_symbolic.
  Defined.
  Smpl Add simple apply run_is_enabled_in : run_closure.
End Impl_SpecId.
