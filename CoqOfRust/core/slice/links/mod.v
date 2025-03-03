Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.slice.mod.
Require Import core.slice.links.index.
Require core.links.option.
Import Run.

Module Impl_Slice.
  Definition Self (T : Set) `{Link T} : Set := list T.
  
  (*
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: SliceIndex<Self>,
    {
        index.get(self)
    }
  *)
  Definition run_get 
      (T : Set) `{Link T}
      {I : Set} `{Link I} 
      {Output : Set} `{Link Output}
      (run_SliceIndex_for_I : SliceIndex.Run I (T := Self T) (Output := Output))
      (self : Ref.t Pointer.Kind.Ref (Self T)) 
      (index : I) :
    {{ slice.Impl_slice_T.get (Φ T) [] [ Φ I ] [ φ self; φ index ] 🔽 option (Ref.t Pointer.Kind.Ref Output)}}.
  Proof.
    destruct run_SliceIndex_for_I eqn:?.
    destruct get as [get [H_get run_get]].
    run_symbolic.
    eapply Run.Rewrite. {
      erewrite IsTraitAssociatedType_eq by eassumption.
      reflexivity.
    }
    run_symbolic_closure.
    intros []; run_symbolic.
  Defined.
End Impl_Slice.
