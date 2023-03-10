(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Module error := std.error.

Module Error := std.error.Error.

Module fmt := std.fmt.

Module ParseIntError := std.num.ParseIntError.
Definition ParseIntError := ParseIntError.t.

Definition Result : Set := std.result.Result.

Module DoubleError.
  Inductive t : Set :=
  | EmptyVec
  | Parse (_ : ParseIntError).
End DoubleError.
Definition DoubleError := DoubleError.t.

Module Impl__crate_fmt_Debug_for_DoubleError.
  Definition Self := DoubleError.
  
  Definition fmt
      (self : ref Self)
      (f : mut_ref _crate.fmt.Formatter)
      : _crate.fmt.Result :=
    match self with
    | DoubleError.EmptyVec => _crate.fmt.ImplFormatter.write_str f "EmptyVec"
    | DoubleError.Parse (__self_0) =>
      _crate.fmt.ImplFormatter.debug_tuple_field1_finish f "Parse" __self_0
    end.
  
  Global Instance M_fmt : Method "fmt" _ := {|
    method := fmt;
  |}.
  Global Instance AF_fmt : DoubleError.AssociatedFunction "fmt" _ := {|
    DoubleError.associated_function := fmt;
  |}.
  Global Instance AFT_fmt : _crate.fmt.Debug.AssociatedFunction "fmt" _ := {|
    _crate.fmt.Debug.associated_function := fmt;
  |}.
  
  Global Instance I : _crate.fmt.Debug.Class Self := {|
    _crate.fmt.Debug.fmt := fmt;
  |}.
End Impl__crate_fmt_Debug_for_DoubleError.

Module Impl_fmt_Display_for_DoubleError.
  Definition Self := DoubleError.
  
  Definition fmt (self : ref Self) (f : mut_ref fmt.Formatter) : fmt.Result :=
    match deref self with
    | DoubleError.EmptyVec =>
      method
        "write_fmt"
        f
        (_crate.fmt.ImplArguments.new_v1
          [ "please use a vector with at least one element" ]
          [  ])
    | DoubleError.Parse () =>
      method
        "write_fmt"
        f
        (_crate.fmt.ImplArguments.new_v1
          [ "the provided string could not be parsed as int" ]
          [  ])
    end.
  
  Global Instance M_fmt : Method "fmt" _ := {|
    method := fmt;
  |}.
  Global Instance AF_fmt : DoubleError.AssociatedFunction "fmt" _ := {|
    DoubleError.associated_function := fmt;
  |}.
  Global Instance AFT_fmt : fmt.Display.AssociatedFunction "fmt" _ := {|
    fmt.Display.associated_function := fmt;
  |}.
  
  Global Instance I : fmt.Display.Class Self := {|
    fmt.Display.fmt := fmt;
  |}.
End Impl_fmt_Display_for_DoubleError.

Module Impl_error_Error_for_DoubleError.
  Definition Self := DoubleError.
  
  Definition source (self : ref Self) : Option :=
    match deref self with
    | DoubleError.EmptyVec => None
    | DoubleError.Parse (e) => Some e
    end.
  
  Global Instance M_source : Method "source" _ := {|
    method := source;
  |}.
  Global Instance AF_source : DoubleError.AssociatedFunction "source" _ := {|
    DoubleError.associated_function := source;
  |}.
  Global Instance AFT_source : error.Error.AssociatedFunction "source" _ := {|
    error.Error.associated_function := source;
  |}.
  
  Global Instance I : error.Error.Class Self := {|
  |}.
End Impl_error_Error_for_DoubleError.

Module Impl_From_for_DoubleError.
  Definition Self := DoubleError.
  
  Definition from (err : ParseIntError) : DoubleError := DoubleError.Parse err.
  
  Global Instance AF_from : DoubleError.AssociatedFunction "from" _ := {|
    DoubleError.associated_function := from;
  |}.
  Global Instance AFT_from : From.AssociatedFunction "from" _ := {|
    From.associated_function := from;
  |}.
  
  Global Instance I : From.Class ParseIntError Self := {|
    From.from := from;
  |}.
End Impl_From_for_DoubleError.

Definition double_first (vec : Vec) : Result :=
  let first :=
    match branch (method "ok_or" (method "first" vec) DoubleError.EmptyVec) with
    | Break {| Break.0 := residual; |} => Return (from_residual residual)
    | Continue {| Continue.0 := val; |} => val
    end in
  let parsed :=
    match branch (method "parse" first) with
    | Break {| Break.0 := residual; |} => Return (from_residual residual)
    | Continue {| Continue.0 := val; |} => val
    end in
  Ok (mul 2 parsed).

Definition print (result : Result) : unit :=
  match result with
  | Ok (n) =>
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "The first doubled is "; "\n" ]
        [ _crate.fmt.ImplArgumentV1.new_display n ]) ;;
    tt
  | Err (e) =>
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "Error: "; "\n" ]
        [ _crate.fmt.ImplArgumentV1.new_display e ]) ;;
    tt ;;
    if (let_if Some (source) := method "source" e : bool) then
      _crate.io._print
        (_crate.fmt.ImplArguments.new_v1
          [ "  Caused by: "; "\n" ]
          [ _crate.fmt.ImplArgumentV1.new_display source ]) ;;
      tt ;;
      tt
    else
      tt
  end.

Definition main (_ : unit) : unit :=
  let numbers := ComplexTypePath.into_vec [ "42"; "93"; "18" ] in
  let empty := _crate.vec.ImplVec.new tt in
  let strings := ComplexTypePath.into_vec [ "tofu"; "93"; "18" ] in
  print (double_first numbers) ;;
  print (double_first empty) ;;
  print (double_first strings) ;;
  tt.
