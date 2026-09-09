Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.

From Stdlib Require Export extraction.Extraction.
From Stdlib Require Export extraction.ExtrOcamlBasic.
From Stdlib Require Export extraction.ExtrOcamlNatInt.
From Stdlib Require Export extraction.ExtrOcamlZBigInt.
From Stdlib Require Export extraction.ExtrOCamlPString.

Extraction Language OCaml.

Extract Constant Ty.t => "Extracted_ty.t".
Extract Constant Ty.path => "Extracted_ty.path".
Extract Constant Ty.function => "Extracted_ty.function_".
Extract Constant Ty.tuple => "Extracted_ty.tuple".
Extract Constant Translated.ty_eqb =>
  "Extracted_ty.equal".
Extract Constant Ty.apply =>
  "(fun ty consts types ->
    let consts =
      Stdlib.List.map
        (function
          | Value.Integer (_, value) ->
            Extracted_ty.Integer (Big_int_Z.string_of_big_int value)
          | Value.Bool value -> Extracted_ty.Bool value
          | _ -> Extracted_ty.Unsupported)
        consts
    in
    Extracted_ty.apply ty consts types)".
Extract Constant Ty.dyn => "Extracted_ty.dyn".
Extract Constant Ty.associated_in_trait =>
  "(fun trait_name consts types self_ty associated_name ->
    let consts =
      Stdlib.List.map
        (function
          | Value.Integer (_, value) ->
            Extracted_ty.Integer (Big_int_Z.string_of_big_int value)
          | Value.Bool value -> Extracted_ty.Bool value
          | _ -> Extracted_ty.Unsupported)
        consts
    in
    Extracted_ty.associated_in_trait
      trait_name consts types self_ty associated_name)".
Extract Constant Ty.associated_unknown => "Extracted_ty.Associated_unknown".
Extract Constant M.cast =>
  "(fun ty value ->
    match Extracted_ty.path_name ty, value with
    | Some ""u8"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.U8, Big_int_Z.extract_big_int value 0 8)
    | Some ""u16"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.U16, Big_int_Z.extract_big_int value 0 16)
    | Some ""u32"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.U32, Big_int_Z.extract_big_int value 0 32)
    | Some ""u64"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.U64, Big_int_Z.extract_big_int value 0 64)
    | Some ""u128"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.U128, Big_int_Z.extract_big_int value 0 128)
    | Some ""usize"", Value.Integer (_, value) ->
      Value.Integer (IntegerKind.Usize, Big_int_Z.extract_big_int value 0 64)
    | _ -> failwith ""unsupported extracted cast""
    )".
Extract Constant Translated.Stack.address_to_nat =>
  "(fun address -> Some (Obj.magic address : int))".
Extract Constant Translated.Evaluate.closure_body =>
  "(fun value ->
    match value with
    | Value.Closure (ExistS (_, body)) ->
      Some ((Obj.magic body : Value.t list -> m))
    | _ -> None)".
