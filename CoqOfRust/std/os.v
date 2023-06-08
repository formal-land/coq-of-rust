Require Import CoqOfRust.lib.lib.

(* ********MODULES******** *)
(*
[ ] fd
[ ] linux
[x] raw
[ ] unix
[ ] wasi
[ ] windows
*)

Module fd.
  (* ********STRUCTS******** *)
  (*
  [ ] BorrowedFd
  [ ] OwnedFd
  *)

  (* ********TRAITS******** *)
  (*
  [ ] AsFd
  [ ] AsRawFd
  [ ] FromRawFd
  [ ] IntoRawFd
  *)

  (* ********TYPE DEFINITIONS******** *)
  (*
  [ ] RawFd
  *)
End fd.

Module linux.
  (* ********MODULES******** *)
  (*
  [ ] process
  [ ] fs
  [ ] net
  [x] raw(Deprecated)
  *)
  Module process.
  End process.
  
  Module fs.
  End fs.
  
  Module net.
  End net.
End linux.

Module raw.
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
  [ ] c_void
  *)
  
End raw.

Module unix.
  (* ********MODULES******** *)
  (*
  [ ] ucred
  [ ] ffi
  [ ] fs
  [ ] io
  [ ] net
  [ ] prelude
  [ ] process
  [x] raw(Deprecated)
  [ ] thread
  *)
  
End unix.

Module wasi.
  (* ********MODULES******** *)
  (*
  [ ] fs
  [ ] net
  [ ] ffi
  [ ] io
  [ ] prelude
  *)
  
End wasi.

Module windows.
  (* ********MODULES******** *)
  (*
  [ ] ffi
  [ ] fs
  [ ] io
  [ ] prelude
  [ ] process
  [ ] raw
  [ ] thread
  *)
End windows.
