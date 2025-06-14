Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import openvm.version_v1_2_0.crates.vm.arch.integration_api.

(*
  pub trait VmAdapterInterface<T> {
      type Reads;
      type Writes;
      type ProcessedInstruction;
  }
*)
Module VmAdapterInterface.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("openvm_circuit::arch::integration_api::VmAdapterInterface", [], [Φ T], Φ Self).

  Module AssociatedTypes.
    Record t : Type := {
      Reads : Set;
      Writes : Set;
      ProcessedInstruction : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Reads : Link types.(Reads);
      H_Writes : Link types.(Writes);
      H_ProcessedInstruction : Link types.(ProcessedInstruction);
    }.

    Global Instance IsLinkReads (types : t) (H : AreLinks types) : Link types.(Reads) :=
      H.(H_Reads _).
    Global Instance IsLinkWrites (types : t) (H : AreLinks types) : Link types.(Writes) :=
      H.(H_Writes _).
    Global Instance IsLinkProcessedInstruction (types : t) (H : AreLinks types) : Link types.(ProcessedInstruction) :=
      H.(H_ProcessedInstruction _).
  End AssociatedTypes.

  Class Run
      (Self T : Set) `{Link Self} `{Link T} 
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
  {
    Reads_IsAssociated :
      IsTraitAssociatedType
        "openvm_circuit::arch::integration_api::VmAdapterInterface" [] [Φ T] (Φ Self)
        "Reads" (Φ types.(AssociatedTypes.Reads));
    Writes_IsAssociated :
      IsTraitAssociatedType
        "openvm_circuit::arch::integration_api::VmAdapterInterface" [] [Φ T] (Φ Self)
        "Writes" (Φ types.(AssociatedTypes.Writes));
    ProcessedInstruction_IsAssociated :
      IsTraitAssociatedType
        "openvm_circuit::arch::integration_api::VmAdapterInterface" [] [Φ T] (Φ Self)
        "ProcessedInstruction" (Φ types.(AssociatedTypes.ProcessedInstruction));
  }.
End VmAdapterInterface.
