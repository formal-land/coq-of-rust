Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] VaList
[x] VaListImpl
[x] CStr
[x] CString	
[x] FromBytesWithNulError
[x] FromVecWithNulError
[x] IntoStringError
[x] NulError
[x] OsStr
[x] OsString
*)
(* 
pub struct VaList<'a, 'f>
where
    'f: 'a,
{ /* private fields */ }
*)
Module VaList.
  Parameter t : Set.
End VaList.

(* pub struct VaListImpl<'f> { /* private fields */ } *)
Module VaListImpl.
  Parameter t : Set.
End VaListImpl.

(* pub struct CStr { /* private fields */ } *)
Module CStr.
  Parameter t : Set.
End CStr.

(* pub struct CString { /* private fields */ } *)
Module CString.
  Parameter t : Set.
End CString.

(* pub struct FromBytesWithNulError { /* private fields */ } *)
Module FromBytesWithNulError.
  Parameter t : Set.
End FromBytesWithNulError.

(* pub struct FromVecWithNulError { /* private fields */ } *)
Module FromVecWithNulError.
  Parameter t : Set.
End FromVecWithNulError.

(* pub struct IntoStringError { /* private fields */ } *)
Module IntoStringError.
  Parameter t : Set.
End IntoStringError.

(* pub struct NulError(_, _); *)
Module NulError.
  Parameter t : Set.
End NulError.

Module os_str.
  (* pub struct OsString { /* private fields */ } *)
  Module OsString.
    Parameter t : Set.
  End OsString.

  (* pub struct OsStr { /* private fields */ } *)
  Module OsStr.
    Parameter t : Set.
  End OsStr.
End os_str.

(* ********ENUMS******** *)
(*
[x] c_void
*)
(* 
pub enum c_void {
    // some variants omitted
}
*)
Module c_void.
  Inductive t : Set := .
End c_void.


(* ********TYPE DEFINITIONS******** *)
(*
[ ] c_char
[ ] c_double
[ ] c_float
[ ] c_int
[ ] c_long
[ ] c_longlong
[ ] c_schar
[ ] c_short
[ ] c_uchar
[ ] c_uint
[ ] c_ulong
[ ] c_ulonglong
[ ] c_ushort
*)
