(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module load_sign_extend.
  Axiom Rv32LoadSignExtendChip :
    forall (F : Ty.t),
    (Ty.apply
        (Ty.path "openvm_rv32im_circuit::load_sign_extend::Rv32LoadSignExtendChip")
        []
        [ F ]) =
      (Ty.apply
        (Ty.path "openvm_circuit::arch::integration_api::VmChipWrapper")
        []
        [
          F;
          Ty.apply
            (Ty.path "openvm_rv32im_circuit::adapters::loadstore::Rv32LoadStoreAdapterChip")
            []
            [ F ];
          Ty.apply
            (Ty.path "openvm_rv32im_circuit::load_sign_extend::core::LoadSignExtendCoreChip")
            [
              M.unevaluated_const
                (mk_str (|
                  "openvm_rv32im_circuit_load_sign_extend_Rv32LoadSignExtendChip_discriminant"
                |));
              M.unevaluated_const
                (mk_str (|
                  "openvm_rv32im_circuit_load_sign_extend_Rv32LoadSignExtendChip_discriminant"
                |))
            ]
            []
        ]).
End load_sign_extend.
