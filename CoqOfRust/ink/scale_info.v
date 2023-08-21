(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

Module form.
  (*
  pub trait Form {
      type Type: PartialEq + Eq + PartialOrd + Ord + Clone + Debug + JsonSchemaMaybe;
      type String: AsRef<str>
          + PartialEq
          + Eq
          + PartialOrd
          + Ord
          + Clone
          + Debug
          + JsonSchemaMaybe;
  }
  *)
  Module Form.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
      (* TODO *)
    }.
    Set Primitive Projections.
  End Form.

  (*
  pub enum MetaForm {}
  *)
  Module MetaForm.
    Inductive t : Set :=.
  End MetaForm.
  Definition MetaForm := MetaForm.t.

  (*
  pub enum PortableForm {}
  *)
  Module PortableForm.
    Inductive t : Set :=.
  End PortableForm.
  Definition PortableForm := PortableForm.t.

  (*
  impl Form for MetaForm {
      type Type = MetaType;
      type String = &'static str;
  }
  *)
  Module Impl_Form_for_MetaForm.
    Global Instance I : Form.Trait MetaForm := {
      (* TODO *)
    }.
  End Impl_Form_for_MetaForm.

  Module Impl_Form_for_PortableForm.
    Global Instance I : Form.Trait PortableForm := {
      (* TODO *)
    }.
  End Impl_Form_for_PortableForm.
End form.

(*
pub struct Type<T: Form = MetaForm> {
    pub path: Path<T>,
    pub type_params: Vec<TypeParameter<T>>,
    pub type_def: TypeDef<T>,
    pub docs: Vec<T::String>,
}
*)
Module Type_.
  Unset Primitive Projections.
  Record t (T : Set) `{form.Form.Trait T} : Set := { (* TODO *) }.
  Set Primitive Projections.
End Type_.
Definition Type_ := Type_.t.
Arguments Type_ _ {_}.

(*
pub struct PortableType {
    pub id: u32,
    pub ty: Type<PortableForm>,
}
*)
Module PortableType.
  Record t : Set := {
    id : u32;
    ty : Type_ form.PortableForm;
  }.
End PortableType.

(*
pub struct PortableRegistry {
    pub types: Vec<PortableType>,
}
*)
Module PortableRegistry.
  Unset Primitive Projections.
  Record t : Set := {}.
  Set Primitive Projections.
End PortableRegistry.
Definition PortableRegistry := PortableRegistry.t.
