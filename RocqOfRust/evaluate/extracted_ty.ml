type constant =
  | Bool of bool
  | Integer of string
  | Unsupported

type t =
  | Apply of t * constant list * t list
  | Associated_in_trait of string * constant list * t list * t * string
  | Associated_unknown
  | Dyn of (string * t list) list
  | Function of t list * t
  | Path of string
  | Tuple of t list

let apply ty consts types =
  Apply (ty, consts, types)

let associated_in_trait trait_name consts types self_ty associated_name =
  Associated_in_trait
    ( Pstring.to_string trait_name,
      consts,
      types,
      self_ty,
      Pstring.to_string associated_name )

let dyn traits =
  Dyn
    (Stdlib.List.map
       (fun (trait_name, types) -> (Pstring.to_string trait_name, types))
       traits)

let equal left right =
  left = right

let function_ arguments result =
  Function (arguments, result)

let path path =
  Path (Pstring.to_string path)

let path_name ty =
  match ty with
  | Path path -> Some path
  | _ -> None

let tuple types =
  Tuple types
