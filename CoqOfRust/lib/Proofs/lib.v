Require Import CoqOfRust.lib.lib.

Module u8.
  Module Valid.
    Definition t (v : u8.t) : Prop :=
      0 <= Integer.to_Z v < 2^8.
  End Valid.
End u8.

Module u16.
  Module Valid.
    Definition t (v : u16.t) : Prop :=
      0 <= Integer.to_Z v < 2^16.
  End Valid.
End u16.

Module u32.
  Module Valid.
    Definition t (v : u32.t) : Prop :=
      0 <= Integer.to_Z v < 2^32.
  End Valid.
End u32.

Module u64.
  Module Valid.
    Definition t (v : u64.t) : Prop :=
      0 <= Integer.to_Z v < 2^64.
  End Valid.
End u64.

Module u128.
  Module Valid.
    Definition t (v : u128.t) : Prop :=
      0 <= Integer.to_Z v < 2^128.
  End Valid.
End u128.

Module usize.
  Module Valid.
    Definition t (v : usize.t) : Prop :=
      0 <= Integer.to_Z v < 2^64.
  End Valid.
End usize.

Module i8.
  Module Valid.
    Definition t (v : i8.t) : Prop :=
      -2^7 <= Integer.to_Z v < 2^7.
  End Valid.
End i8.

Module i16.
  Module Valid.
    Definition t (v : i16.t) : Prop :=
      -2^15 <= Integer.to_Z v < 2^15.
  End Valid.
End i16.

Module i32.
  Module Valid.
    Definition t (v : i32.t) : Prop :=
      -2^31 <= Integer.to_Z v < 2^31.
  End Valid.
End i32.

Module i64.
  Module Valid.
    Definition t (v : i64.t) : Prop :=
      -2^63 <= Integer.to_Z v < 2^63.
  End Valid.
End i64.

Module i128.
  Module Valid.
    Definition t (v : i128.t) : Prop :=
      -2^127 <= Integer.to_Z v < 2^127.
  End Valid.
End i128.

Module isize.
  Module Valid.
    Definition t (v : isize.t) : Prop :=
      -2^63 <= Integer.to_Z v < 2^63.
  End Valid.
End isize.
