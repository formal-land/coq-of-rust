Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.signed.links.int.
Require Import ruint.links.lib.

(** We define the aliases for convenience. They are actually expanded in the translation
    from Rust.

    We wrap everything in a module to avoid name clashes.
*)

Module aliases.
  Module I0.
    Definition t : Set :=
      Signed.t {| Integer.value := 0 |} {| Integer.value := 0 |}.
  End I0.

  Module I1.
    Definition t : Set :=
      Signed.t {| Integer.value := 1 |} {| Integer.value := 1 |}.
  End I1.

  Module U8.
    Definition t : Set :=
      Uint.t {| Integer.value := 8 |} {| Integer.value := 1 |}.
  End U8.

  Module I8.
    Definition t : Set :=
      Signed.t {| Integer.value := 8 |} {| Integer.value := 1 |}.
  End I8.

  Module U16.
    Definition t : Set :=
      Uint.t {| Integer.value := 16 |} {| Integer.value := 1 |}.
  End U16.

  Module I16.
    Definition t : Set :=
      Signed.t {| Integer.value := 16 |} {| Integer.value := 1 |}.
  End I16.

  Module U24.
    Definition t : Set :=
      Uint.t {| Integer.value := 24 |} {| Integer.value := 1 |}.
  End U24.

  Module I24.
    Definition t : Set :=
      Signed.t {| Integer.value := 24 |} {| Integer.value := 1 |}.
  End I24.

  Module U32.
    Definition t : Set :=
      Uint.t {| Integer.value := 32 |} {| Integer.value := 1 |}.
  End U32.

  Module I32.
    Definition t : Set :=
      Signed.t {| Integer.value := 32 |} {| Integer.value := 1 |}.
  End I32.

  Module U40.
    Definition t : Set :=
      Uint.t {| Integer.value := 40 |} {| Integer.value := 1 |}.
  End U40.

  Module I40.
    Definition t : Set :=
      Signed.t {| Integer.value := 40 |} {| Integer.value := 1 |}.
  End I40.

  Module U48.
    Definition t : Set :=
      Uint.t {| Integer.value := 48 |} {| Integer.value := 1 |}.
  End U48.

  Module I48.
    Definition t : Set :=
      Signed.t {| Integer.value := 48 |} {| Integer.value := 1 |}.
  End I48.

  Module U56.
    Definition t : Set :=
      Uint.t {| Integer.value := 56 |} {| Integer.value := 1 |}.
  End U56.

  Module I56.
    Definition t : Set :=
      Signed.t {| Integer.value := 56 |} {| Integer.value := 1 |}.
  End I56.

  Module U64.
    Definition t : Set :=
      Uint.t {| Integer.value := 64 |} {| Integer.value := 1 |}.
  End U64.

  Module I64.
    Definition t : Set :=
      Signed.t {| Integer.value := 64 |} {| Integer.value := 1 |}.
  End I64.

  Module U72.
    Definition t : Set :=
      Uint.t {| Integer.value := 72 |} {| Integer.value := 2 |}.
  End U72.

  Module I72.
    Definition t : Set :=
      Signed.t {| Integer.value := 72 |} {| Integer.value := 2 |}.
  End I72.

  Module U80.
    Definition t : Set :=
      Uint.t {| Integer.value := 80 |} {| Integer.value := 2 |}.
  End U80.

  Module I80.
    Definition t : Set :=
      Signed.t {| Integer.value := 80 |} {| Integer.value := 2 |}.
  End I80.

  Module U88.
    Definition t : Set :=
      Uint.t {| Integer.value := 88 |} {| Integer.value := 2 |}.
  End U88.

  Module I88.
    Definition t : Set :=
      Signed.t {| Integer.value := 88 |} {| Integer.value := 2 |}.
  End I88.

  Module U96.
    Definition t : Set :=
      Uint.t {| Integer.value := 96 |} {| Integer.value := 2 |}.
  End U96.

  Module I96.
    Definition t : Set :=
      Signed.t {| Integer.value := 96 |} {| Integer.value := 2 |}.
  End I96.

  Module U104.
    Definition t : Set :=
      Uint.t {| Integer.value := 104 |} {| Integer.value := 2 |}.
  End U104.

  Module I104.
    Definition t : Set :=
      Signed.t {| Integer.value := 104 |} {| Integer.value := 2 |}.
  End I104.

  Module U112.
    Definition t : Set :=
      Uint.t {| Integer.value := 112 |} {| Integer.value := 2 |}.
  End U112.

  Module I112.
    Definition t : Set :=
      Signed.t {| Integer.value := 112 |} {| Integer.value := 2 |}.
  End I112.

  Module U120.
    Definition t : Set :=
      Uint.t {| Integer.value := 120 |} {| Integer.value := 2 |}.
  End U120.

  Module I120.
    Definition t : Set :=
      Signed.t {| Integer.value := 120 |} {| Integer.value := 2 |}.
  End I120.

  Module U128.
    Definition t : Set :=
      Uint.t {| Integer.value := 128 |} {| Integer.value := 2 |}.
  End U128.

  Module I128.
    Definition t : Set :=
      Signed.t {| Integer.value := 128 |} {| Integer.value := 2 |}.
  End I128.

  Module U136.
    Definition t : Set :=
      Uint.t {| Integer.value := 136 |} {| Integer.value := 3 |}.
  End U136.

  Module I136.
    Definition t : Set :=
      Signed.t {| Integer.value := 136 |} {| Integer.value := 3 |}.
  End I136.

  Module U144.
    Definition t : Set :=
      Uint.t {| Integer.value := 144 |} {| Integer.value := 3 |}.
  End U144.

  Module I144.
    Definition t : Set :=
      Signed.t {| Integer.value := 144 |} {| Integer.value := 3 |}.
  End I144.

  Module U152.
    Definition t : Set :=
      Uint.t {| Integer.value := 152 |} {| Integer.value := 3 |}.
  End U152.

  Module I152.
    Definition t : Set :=
      Signed.t {| Integer.value := 152 |} {| Integer.value := 3 |}.
  End I152.

  Module U160.
    Definition t : Set :=
      Uint.t {| Integer.value := 160 |} {| Integer.value := 3 |}.
  End U160.

  Module I160.
    Definition t : Set :=
      Signed.t {| Integer.value := 160 |} {| Integer.value := 3 |}.
  End I160.

  Module U168.
    Definition t : Set :=
      Uint.t {| Integer.value := 168 |} {| Integer.value := 3 |}.
  End U168.

  Module I168.
    Definition t : Set :=
      Signed.t {| Integer.value := 168 |} {| Integer.value := 3 |}.
  End I168.

  Module U176.
    Definition t : Set :=
      Uint.t {| Integer.value := 176 |} {| Integer.value := 3 |}.
  End U176.

  Module I176.
    Definition t : Set :=
      Signed.t {| Integer.value := 176 |} {| Integer.value := 3 |}.
  End I176.

  Module U184.
    Definition t : Set :=
      Uint.t {| Integer.value := 184 |} {| Integer.value := 3 |}.
  End U184.

  Module I184.
    Definition t : Set :=
      Signed.t {| Integer.value := 184 |} {| Integer.value := 3 |}.
  End I184.

  Module U192.
    Definition t : Set :=
      Uint.t {| Integer.value := 192 |} {| Integer.value := 3 |}.
  End U192.

  Module I192.
    Definition t : Set :=
      Signed.t {| Integer.value := 192 |} {| Integer.value := 3 |}.
  End I192.

  Module U200.
    Definition t : Set :=
      Uint.t {| Integer.value := 200 |} {| Integer.value := 4 |}.
  End U200.

  Module I200.
    Definition t : Set :=
      Signed.t {| Integer.value := 200 |} {| Integer.value := 4 |}.
  End I200.

  Module U208.
    Definition t : Set :=
      Uint.t {| Integer.value := 208 |} {| Integer.value := 4 |}.
  End U208.

  Module I208.
    Definition t : Set :=
      Signed.t {| Integer.value := 208 |} {| Integer.value := 4 |}.
  End I208.

  Module U216.
    Definition t : Set :=
      Uint.t {| Integer.value := 216 |} {| Integer.value := 4 |}.
  End U216.

  Module I216.
    Definition t : Set :=
      Signed.t {| Integer.value := 216 |} {| Integer.value := 4 |}.
  End I216.

  Module U224.
    Definition t : Set :=
      Uint.t {| Integer.value := 224 |} {| Integer.value := 4 |}.
  End U224.

  Module I224.
    Definition t : Set :=
      Signed.t {| Integer.value := 224 |} {| Integer.value := 4 |}.
  End I224.

  Module U232.
    Definition t : Set :=
      Uint.t {| Integer.value := 232 |} {| Integer.value := 4 |}.
  End U232.

  Module I232.
    Definition t : Set :=
      Signed.t {| Integer.value := 232 |} {| Integer.value := 4 |}.
  End I232.

  Module U240.
    Definition t : Set :=
      Uint.t {| Integer.value := 240 |} {| Integer.value := 4 |}.
  End U240.

  Module I240.
    Definition t : Set :=
      Signed.t {| Integer.value := 240 |} {| Integer.value := 4 |}.
  End I240.

  Module U248.
    Definition t : Set :=
      Uint.t {| Integer.value := 248 |} {| Integer.value := 4 |}.
  End U248.

  Module I248.
    Definition t : Set :=
      Signed.t {| Integer.value := 248 |} {| Integer.value := 4 |}.
  End I248.

  Module U256.
    Definition t : Set :=
      Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |}.
  End U256.

  Module I256.
    Definition t : Set :=
      Signed.t {| Integer.value := 256 |} {| Integer.value := 4 |}.
  End I256.

  Module U512.
    Definition t : Set :=
      Uint.t {| Integer.value := 512 |} {| Integer.value := 8 |}.
  End U512.

  Module I512.
    Definition t : Set :=
      Signed.t {| Integer.value := 512 |} {| Integer.value := 8 |}.
  End I512.

  Module B8.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 1 |}.
  End B8.

  Module B16.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 2 |}.
  End B16.

  Module B32.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 4 |}.
  End B32.

  Module B64.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 8 |}.
  End B64.

  Module B96.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 12 |}.
  End B96.

  Module B128.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 16 |}.
  End B128.

  Module B160.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 20 |}.
  End B160.

  Module B192.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 24 |}.
  End B192.

  Module B224.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 28 |}.
  End B224.

  Module B256.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 32 |}.
  End B256.

  Module B512.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 64 |}.
  End B512.

  Module B1024.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 128 |}.
  End B1024.

  Module B2048.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 256 |}.
  End B2048.

  Module BlockHash.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 32 |}.
  End BlockHash.

  Module BlockNumber.
    Definition t : Set :=
      U64.t.
  End BlockNumber.

  Module BlockTimestamp.
    Definition t : Set :=
      U64.t.
  End BlockTimestamp.

  Module TxHash.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 32 |}.
  End TxHash.

  Module TxNumber.
    Definition t : Set :=
      U64.t.
  End TxNumber.

  Module TxNonce.
    Definition t : Set :=
      U64.t.
  End TxNonce.

  Module TxIndex.
    Definition t : Set :=
      U64.t.
  End TxIndex.

  Module ChainId.
    Definition t : Set :=
      U64.t.
  End ChainId.

  Module StorageKey.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 32 |}.
  End StorageKey.

  Module StorageValue.
    Definition t : Set :=
      Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |}.
  End StorageValue.

  Module Selector.
    Definition t : Set :=
      FixedBytes.t {| Integer.value := 4 |}.
  End Selector.
End aliases.
