(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Module Person.
  Record t : Set := {
    job : Option;
  }.
  
  Global Instance Get_job : NamedField.Class t "job" _ := {|
    NamedField.get '(Build_t x0) := x0;
  |}.
  Class AssociatedFunction (name : string) (T : Set) : Set := {
    associated_function : T;
  }.
  Arguments associated_function name {T AssociatedFunction}.
End Person.
Definition Person : Set := Person.t.

Module Job.
  Record t : Set := {
    phone_number : Option;
  }.
  
  Global Instance Get_phone_number : NamedField.Class t "phone_number" _ := {|
    NamedField.get '(Build_t x0) := x0;
  |}.
  Class AssociatedFunction (name : string) (T : Set) : Set := {
    associated_function : T;
  }.
  Arguments associated_function name {T AssociatedFunction}.
End Job.
Definition Job : Set := Job.t.

Module Impl__crate_clone_Clone_for_Job.
  Definition Self := Job.
  
  Definition clone (self : ref Self) : Job :=
    let _ := tt in
    deref self.
  
  Global Instance M_clone : Method "clone" _ := {|
    method := clone;
  |}.
  Global Instance AF_clone : Job.AssociatedFunction "clone" _ := {|
    Job.associated_function := clone;
  |}.
  Global Instance
    AFT_clone
    :
    _crate.clone.Clone.AssociatedFunction
    "clone"
    _
    :=
    {|
    _crate.clone.Clone.associated_function := clone;
  |}.
  
  Global Instance I : _crate.clone.Clone.Class Self := {|
    _crate.clone.Clone.clone := clone;
  |}.
End Impl__crate_clone_Clone_for_Job.

Module Impl__crate_marker_Copy_for_Job.
  Definition Self := Job.
  
  Global Instance I : _crate.marker.Copy.Class Self :=
    _crate.marker.Copy.Build_Class _.
End Impl__crate_marker_Copy_for_Job.

Module PhoneNumber.
  Record t : Set := {
    area_code : Option;
    number : u32;
  }.
  
  Global Instance Get_area_code : NamedField.Class t "area_code" _ := {|
    NamedField.get '(Build_t x0 _) := x0;
  |}.
  Global Instance Get_number : NamedField.Class t "number" _ := {|
    NamedField.get '(Build_t _ x1) := x1;
  |}.
  Class AssociatedFunction (name : string) (T : Set) : Set := {
    associated_function : T;
  }.
  Arguments associated_function name {T AssociatedFunction}.
End PhoneNumber.
Definition PhoneNumber : Set := PhoneNumber.t.

Module Impl__crate_clone_Clone_for_PhoneNumber.
  Definition Self := PhoneNumber.
  
  Definition clone (self : ref Self) : PhoneNumber :=
    let _ := tt in
    let _ := tt in
    deref self.
  
  Global Instance M_clone : Method "clone" _ := {|
    method := clone;
  |}.
  Global Instance AF_clone : PhoneNumber.AssociatedFunction "clone" _ := {|
    PhoneNumber.associated_function := clone;
  |}.
  Global Instance
    AFT_clone
    :
    _crate.clone.Clone.AssociatedFunction
    "clone"
    _
    :=
    {|
    _crate.clone.Clone.associated_function := clone;
  |}.
  
  Global Instance I : _crate.clone.Clone.Class Self := {|
    _crate.clone.Clone.clone := clone;
  |}.
End Impl__crate_clone_Clone_for_PhoneNumber.

Module Impl__crate_marker_Copy_for_PhoneNumber.
  Definition Self := PhoneNumber.
  
  Global Instance I : _crate.marker.Copy.Class Self :=
    _crate.marker.Copy.Build_Class _.
End Impl__crate_marker_Copy_for_PhoneNumber.

Module ImplPerson.
  Definition Self := Person.
  
  Definition work_phone_area_code (self : ref Self) : Option :=
    NamedField.get
      (name := "area_code")
      match
        branch
          (NamedField.get
            (name := "phone_number")
            match branch (NamedField.get (name := "job") self) with
            | Break {| Break.0 := residual; |} =>
              Return (from_residual residual)
            | Continue {| Continue.0 := val; |} => val
            end)
      with
      | Break {| Break.0 := residual; |} => Return (from_residual residual)
      | Continue {| Continue.0 := val; |} => val
      end.
  
  Global Instance M_work_phone_area_code : Method "work_phone_area_code" _ := {|
    method := work_phone_area_code;
  |}.
  Global Instance
    AF_work_phone_area_code
    :
    Person.AssociatedFunction
    "work_phone_area_code"
    _
    :=
    {|
    Person.associated_function := work_phone_area_code;
  |}.
End ImplPerson.

Definition main (_ : unit) : unit :=
  let p :=
    {|
      Person.job :=
        Some
          {|
            Job.phone_number :=
              Some
                {|
                  PhoneNumber.area_code := Some 61;
                  PhoneNumber.number := 439222222;
                |};
          |};
    |} in
  match (method "work_phone_area_code" p, Some 61) with
  | (left_val, right_val) =>
    if (not (eqb (deref left_val) (deref right_val)) : bool) then
      let kind := _crate.panicking.AssertKind.Eq in
      _crate.panicking.assert_failed
        kind
        (deref left_val)
        (deref right_val)
        _crate.option.Option.None ;;
      tt
    else
      tt
  end ;;
  tt.
