Require Import CoqOfRust.Monad.
Require Import CoqOfRust.lib.lib.

(* ********MODULES******** *)
(*
[x]rust_2024
[x]rust_2015
[x]rust_2018
[x]rust_2021
[x]v1
*)

Module v1.
  (* ********RE-EXPORTS******** *)
  (*
  [ ] core::prelude::v1::concat_bytes
  [ ] crate::marker::Send
  [ ] crate::marker::Sized
  [ ] crate::marker::Sync
  [ ] crate::marker::Unpin
  [ ] crate::ops::Drop
  [ ] crate::ops::Fn
  [ ] crate::ops::FnMut
  [ ] crate::ops::FnOnce
  [ ] crate::mem::drop
  [ ] crate::convert::AsMut
  [ ] crate::convert::AsRef
  [ ] crate::convert::From
  [ ] crate::convert::Into
  [ ] crate::iter::DoubleEndedIterator
  [ ] crate::iter::ExactSizeIterator
  [ ] crate::iter::Extend
  [ ] crate::iter::IntoIterator
  [ ] crate::iter::Iterator
  [ ] crate::option::Option
  [ ] crate::option::Option::None
  [ ] crate::option::Option::Some
  [ ] crate::result::Result
  [ ] crate::result::Result::Err
  [ ] crate::result::Result::Ok
  [ ] core::prelude::v1::assert
  [ ] core::prelude::v1::cfg
  [ ] core::prelude::v1::column
  [ ] core::prelude::v1::compile_error
  [ ] core::prelude::v1::concat
  [ ] core::prelude::v1::concat_idents
  [ ] core::prelude::v1::env
  [ ] core::prelude::v1::file
  [ ] core::prelude::v1::format_args
  [ ] core::prelude::v1::format_args_nl
  [ ] core::prelude::v1::include
  [ ] core::prelude::v1::include_bytes
  [ ] core::prelude::v1::include_str
  [ ] core::prelude::v1::line
  [ ] core::prelude::v1::log_syntax
  [ ] core::prelude::v1::module_path
  [ ] core::prelude::v1::option_env
  [ ] core::prelude::v1::stringify
  [ ] core::prelude::v1::trace_macros
  [ ] core::prelude::v1::Clone
  [ ] core::prelude::v1::Clone
  [ ] core::prelude::v1::Copy
  [ ] core::prelude::v1::Copy
  [ ] core::prelude::v1::Debug
  [ ] core::prelude::v1::Default
  [ ] core::prelude::v1::Default
  [ ] core::prelude::v1::Eq
  [ ] core::prelude::v1::Eq
  [ ] core::prelude::v1::Hash
  [ ] core::prelude::v1::Ord
  [ ] core::prelude::v1::Ord
  [ ] core::prelude::v1::PartialEq
  [ ] core::prelude::v1::PartialEq
  [ ] core::prelude::v1::PartialOrd
  [ ] core::prelude::v1::PartialOrd
  [ ] crate::borrow::ToOwned
  [ ] crate::boxed::Box
  [ ] crate::string::String
  [ ] crate::string::ToString
  [ ] crate::vec::Vec
  *)
End v1.


Module rust_2024.
  (* ********RE-EXPORTS******** *)
  (*
  [ ] super::v1::*
  [ ] core::prelude::rust_2024::*
  *)
End rust_2024.

Module rust_2015.
  (* ********RE-EXPORTS******** *)
  (*
  [ ] super::v1::*
  *)
End rust_2015.

Module rust_2018.
  (* ********RE-EXPORTS******** *)
  (*
  [ ] super::v1::*
  *)
End rust_2018.

Module rust_2021.
  (* ********RE-EXPORTS******** *)
  (*
  super::v1::*
  core::prelude::rust_2021::*
  *)
  Module From.
    Class Trait (T : Set) (Self : Set) : Set := {
      from : T -> M Self;
    }.
  End From.
End rust_2021.
