Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.mod.

(*
pub struct Log<T = LogData> {
    pub address: Address,
    pub data: T,
}
*)
Module Log.
  Record t {T : Set} : Set := {
    address : Address.t;
    data : T;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T : Set) `{Link T}: Link (t T) := {
    Φ := Ty.apply (Ty.path "alloy_primitives::log::Log") [] [Φ T];
    φ x :=
      Value.StructRecord "alloy_primitives::log::Log" [] [Φ T] [
        ("address", φ x.(address));
        ("data", φ x.(data))
      ];
  }.

  Definition of_ty T' :
    OfTy.t T' ->
    OfTy.t (Ty.apply (Ty.path "alloy_primitives::log::Log") [] [T']).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Lemma of_value_with
      (T : Set) `{Link T} T'
      address address'
      (data : T) data' :
    T' = Φ T ->
    address' = φ address ->
    data' = φ data ->
    Value.StructRecord "alloy_primitives::log::Log" [] [T'] [
      ("address", address');
      ("data", data')
    ] = φ (Build_t T address data).
  Proof.
    intros.
    now subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.
End Log.

(*
pub struct LogData {
    topics: Vec<B256>,
    pub data: Bytes,
}
*)
Module LogData.
  Record t : Set := {
    topics : Vec.t aliases.U256.t Global.t;
    data : Bytes.t;
  }.


  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::log::LogData";
    φ x :=
      Value.StructRecord "alloy_primitives::log::LogData" [] [] [
        ("data", φ x.(data));
        ("topics", φ x.(topics))
      ];
  }.

  Definition of_ty :
    OfTy.t (Ty.path "alloy_primitives::log::LogData").
  Proof.
    eapply OfTy.Make with (A := t).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Lemma of_value_with
      topics topics'
      data data' :
    topics' = φ topics ->
    data' = φ data ->
    Value.StructRecord "alloy_primitives::log::LogData" [] [] [
      ("data", data');
      ("topics", topics')
    ] = φ (Build_t topics data).
  Proof.
    intros.
    now subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.
End LogData.

Module Impl_LogData.
  Definition Self : Set :=
    LogData.t.

  (* pub fn new(topics: Vec<B256>, data: Bytes) -> Option<Self> *)
  Instance run_new (topics : Vec.t aliases.B256.t Global.t) (data : Bytes.t) :
    Run.Trait log.Impl_alloy_primitives_log_LogData.new [] [] [φ topics; φ data]
    (option Self).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_LogData.
Export Impl_LogData.
