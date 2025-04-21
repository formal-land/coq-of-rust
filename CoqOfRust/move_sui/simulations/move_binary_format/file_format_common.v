Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

(*
pub enum BinaryConstants {}
impl BinaryConstants {
    /// The blob that must start a binary.
    pub const MOVE_MAGIC_SIZE: usize = 4;
    pub const MOVE_MAGIC: [u8; BinaryConstants::MOVE_MAGIC_SIZE] = [0xA1, 0x1C, 0xEB, 0x0B];
    /// The `DIEM_MAGIC` size, 4 byte for major version and 1 byte for table count.
    pub const HEADER_SIZE: usize = BinaryConstants::MOVE_MAGIC_SIZE + 5;
    /// A (Table Type, Start Offset, Byte Count) size, which is 1 byte for the type and
    /// 4 bytes for the offset/count.
    pub const TABLE_HEADER_SIZE: u8 = size_of::<u32>() as u8 * 2 + 1;
}
*)
Module BinaryConstants.
  Definition MOVE_MAGIC_SIZE : Z := 4.
  Definition MOVE_MAGIC : list Z := [0xA1; 0x1C; 0xEB; 0x0B].
  Definition HEADER_SIZE : Z := MOVE_MAGIC_SIZE + 5.
  Definition TABLE_HEADER_SIZE : Z := 4 * 2 + 1.
End BinaryConstants.

(*
pub const TABLE_COUNT_MAX: u64 = 255;

pub const TABLE_OFFSET_MAX: u64 = 0xffff_ffff;
pub const TABLE_SIZE_MAX: u64 = 0xffff_ffff;
pub const TABLE_CONTENT_SIZE_MAX: u64 = 0xffff_ffff;

pub const TABLE_INDEX_MAX: u64 = 65535;
pub const SIGNATURE_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const ADDRESS_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const IDENTIFIER_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const MODULE_HANDLE_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const STRUCT_HANDLE_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const STRUCT_DEF_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const FUNCTION_HANDLE_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const FUNCTION_INST_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const FIELD_HANDLE_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const FIELD_INST_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const STRUCT_DEF_INST_INDEX_MAX: u64 = TABLE_INDEX_MAX;
pub const CONSTANT_INDEX_MAX: u64 = TABLE_INDEX_MAX;
*)
Definition TABLE_COUNT_MAX : Z := 255.
Definition TABLE_OFFSET_MAX : Z := 2^32 - 1.
Definition TABLE_SIZE_MAX : Z := 2^32 - 1.
Definition TABLE_CONTENT_SIZE_MAX : Z := 2^32 - 1.
Definition TABLE_INDEX_MAX : Z := 2^16 - 1.
Definition SIGNATURE_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition ADDRESS_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition IDENTIFIER_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition MODULE_HANDLE_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition STRUCT_HANDLE_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition STRUCT_DEF_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition FUNCTION_HANDLE_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition FUNCTION_INST_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition FIELD_HANDLE_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition FIELD_INST_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition STRUCT_DEF_INST_INDEX_MAX : Z := TABLE_INDEX_MAX.
Definition CONSTANT_INDEX_MAX : Z := TABLE_INDEX_MAX.

(*
pub const BYTECODE_COUNT_MAX: u64 = 65535;
pub const BYTECODE_INDEX_MAX: u64 = 65535;

pub const LOCAL_INDEX_MAX: u64 = 255;

pub const IDENTIFIER_SIZE_MAX: u64 = 65535;

pub const CONSTANT_SIZE_MAX: u64 = 65535;

pub const METADATA_KEY_SIZE_MAX: u64 = 1023;
pub const METADATA_VALUE_SIZE_MAX: u64 = 65535;

pub const SIGNATURE_SIZE_MAX: u64 = 255;

pub const ACQUIRES_COUNT_MAX: u64 = 255;

pub const FIELD_COUNT_MAX: u64 = 255;
pub const FIELD_OFFSET_MAX: u64 = 255;

pub const TYPE_PARAMETER_COUNT_MAX: u64 = 255;
pub const TYPE_PARAMETER_INDEX_MAX: u64 = 65536;

pub const SIGNATURE_TOKEN_DEPTH_MAX: usize = 256;
*)
Definition BYTECODE_COUNT_MAX : Z := 2^16 - 1.
Definition BYTECODE_INDEX_MAX : Z := 2^16 - 1.
Definition LOCAL_INDEX_MAX : Z := 255.
Definition IDENTIFIER_SIZE_MAX : Z := 2^16 - 1.
Definition CONSTANT_SIZE_MAX : Z := 2^16 - 1.
Definition METADATA_KEY_SIZE_MAX : Z := 1023.
Definition METADATA_VALUE_SIZE_MAX : Z := 2^16 - 1.
Definition SIGNATURE_SIZE_MAX : Z := 255.
Definition ACQUIRES_COUNT_MAX : Z := 255.
Definition FIELD_COUNT_MAX : Z := 255.
Definition FIELD_OFFSET_MAX : Z := 255.
Definition TYPE_PARAMETER_COUNT_MAX : Z := 255.
Definition TYPE_PARAMETER_INDEX_MAX : Z := 2^16.
Definition SIGNATURE_TOKEN_DEPTH_MAX : Z := 256.

(*
/// Version 1: the initial version
pub const VERSION_1: u32 = 1;

/// Version 2: changes compared with version 1
///  + function visibility stored in separate byte before the flags byte
///  + the flags byte now contains only the is_native information (at bit 0x2)
///  + new visibility modifiers for "friend" and "script" functions
///  + friend list for modules
pub const VERSION_2: u32 = 2;

/// Version 3: changes compared with version 2
///  + phantom type parameters
pub const VERSION_3: u32 = 3;

/// Version 4: changes compared with version 3
///  + bytecode for vector operations
pub const VERSION_4: u32 = 4;

/// Version 5: changes compared with version 4
///  +/- script and public(script) verification is now adapter specific
///  + metadata
pub const VERSION_5: u32 = 5;

/// Version 6: changes compared with version 5
///  + u16, u32, u256 integers and corresponding Ld, Cast bytecodes
pub const VERSION_6: u32 = 6;

// Mark which version is the latest version
pub const VERSION_MAX: u32 = VERSION_6;

// Mark which oldest version is supported.
// TODO(#145): finish v4 compatibility; as of now, only metadata is implemented
pub const VERSION_MIN: u32 = VERSION_5;
*)
Definition VERSION_1 : Z := 1.
Definition VERSION_2 : Z := 2.
Definition VERSION_3 : Z := 3.
Definition VERSION_4 : Z := 4.
Definition VERSION_5 : Z := 5.
Definition VERSION_6 : Z := 6.
Definition VERSION_MAX : Z := VERSION_6.
Definition VERSION_MIN : Z := VERSION_5.
