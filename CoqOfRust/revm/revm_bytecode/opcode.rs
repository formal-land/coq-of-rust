//! EVM opcode definitions and utilities.

#[cfg(feature = "parse")]
pub mod parse;

use core::{fmt, ptr::NonNull};

/// An EVM opcode
///
/// This is always a valid opcode, as declared in the [`opcode`][self] module or the
/// [`OPCODE_INFO`] constant.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct OpCode(u8);

impl fmt::Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.get();
        if let Some(val) = OPCODE_INFO[n as usize] {
            f.write_str(val.name())
        } else {
            write!(f, "UNKNOWN(0x{n:02X})")
        }
    }
}

impl OpCode {
    /// Instantiates a new opcode from a u8.
    #[inline]
    pub const fn new(opcode: u8) -> Option<Self> {
        match OPCODE_INFO[opcode as usize] {
            Some(_) => Some(Self(opcode)),
            None => None,
        }
    }

    /// Returns true if the opcode is a jump destination.
    #[inline]
    pub const fn is_jumpdest(&self) -> bool {
        false
    }

    /// Takes a u8 and returns true if it is a jump destination.
    #[inline]
    pub const fn is_jumpdest_by_op(opcode: u8) -> bool {
        if let Some(opcode) = Self::new(opcode) {
            opcode.is_jumpdest()
        } else {
            false
        }
    }

    /// Returns true if the opcode is a legacy jump instruction.
    #[inline]
    pub const fn is_jump(self) -> bool {
        false
    }

    /// Takes a u8 and returns true if it is a jump instruction.
    #[inline]
    pub const fn is_jump_by_op(opcode: u8) -> bool {
        if let Some(opcode) = Self::new(opcode) {
            opcode.is_jump()
        } else {
            false
        }
    }

    /// Returns true if the opcode is a `PUSH` instruction.
    #[inline]
    pub const fn is_push(self) -> bool {
        false
    }

    /// Takes a u8 and returns true if it is a push instruction.
    #[inline]
    pub fn is_push_by_op(opcode: u8) -> bool {
        if let Some(opcode) = Self::new(opcode) {
            opcode.is_push()
        } else {
            false
        }
    }

    /// Instantiates a new opcode from a u8 without checking if it is valid.
    ///
    /// # Safety
    ///
    /// All code using `Opcode` values assume that they are valid opcodes, so providing an invalid
    /// opcode may cause undefined behavior.
    #[inline]
    pub unsafe fn new_unchecked(opcode: u8) -> Self {
        Self(opcode)
    }

    /// Returns the opcode as a string. This is the inverse of [`parse`](Self::parse).
    #[doc(alias = "name")]
    #[inline]
    pub const fn as_str(self) -> &'static str {
        self.info().name()
    }

    /// Returns the opcode name.
    #[inline]
    pub const fn name_by_op(opcode: u8) -> &'static str {
        if let Some(opcode) = Self::new(opcode) {
            opcode.as_str()
        } else {
            "Unknown"
        }
    }

    /// Returns the number of input stack elements.
    #[inline]
    pub const fn inputs(&self) -> u8 {
        self.info().inputs()
    }

    /// Returns the number of output stack elements.
    #[inline]
    pub const fn outputs(&self) -> u8 {
        self.info().outputs()
    }

    /// Calculates the difference between the number of input and output stack elements.
    #[inline]
    pub const fn io_diff(&self) -> i16 {
        self.info().io_diff()
    }

    /// Returns the opcode information for the given opcode.
    #[inline]
    pub const fn info_by_op(opcode: u8) -> Option<OpCodeInfo> {
        if let Some(opcode) = Self::new(opcode) {
            Some(opcode.info())
        } else {
            None
        }
    }

    /// Returns the opcode as a usize.
    #[inline]
    pub const fn as_usize(&self) -> usize {
        self.0 as usize
    }

    /// Returns the opcode information.
    #[inline]
    pub const fn info(&self) -> OpCodeInfo {
        if let Some(t) = OPCODE_INFO[self.0 as usize] {
            t
        } else {
            panic!("opcode not found")
        }
    }

    /// Returns the number of both input and output stack elements.
    ///
    /// Can be slightly faster that calling `inputs` and `outputs` separately.
    pub const fn input_output(&self) -> (u8, u8) {
        let info = self.info();
        (info.inputs, info.outputs)
    }

    /// Returns the opcode as a u8.
    #[inline]
    pub const fn get(self) -> u8 {
        self.0
    }

    /// Returns true if the opcode modifies memory.
    ///
    /// <https://bluealloy.github.io/revm/crates/interpreter/memory.html#opcodes>
    ///
    /// <https://github.com/crytic/evm-opcodes>
    #[inline]
    pub const fn modifies_memory(&self) -> bool {
        false
    }
}

/// Information about opcode, such as name, and stack inputs and outputs
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OpCodeInfo {
    /// Invariant: `(name_ptr, name_len)` is a [`&'static str`][str]
    ///
    /// It is a shorted variant of [`str`] as
    /// the name length is always less than 256 characters.
    name_ptr: NonNull<u8>,
    name_len: u8,
    /// Stack inputs
    inputs: u8,
    /// Stack outputs
    outputs: u8,
    /// Number of intermediate bytes
    ///
    /// RJUMPV is a special case where the bytes len depends on bytecode value,
    /// for RJUMV size will be set to one byte as it is the minimum immediate size.
    immediate_size: u8,
    /// Used by EOF verification
    ///
    /// All not EOF opcodes are marked false.
    not_eof: bool,
    /// If the opcode stops execution. aka STOP, RETURN, ..
    terminating: bool,
}

impl fmt::Debug for OpCodeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OpCodeInfo")
            .field("name", &self.name())
            .field("inputs", &self.inputs())
            .field("outputs", &self.outputs())
            .field("not_eof", &self.is_disabled_in_eof())
            .field("terminating", &self.is_terminating())
            .field("immediate_size", &self.immediate_size())
            .finish()
    }
}

impl OpCodeInfo {
    /// Creates a new opcode info with the given name and default values.
    pub const fn new(name: &'static str) -> Self {
        assert!(name.len() < 256, "opcode name is too long");
        Self {
            name_ptr: unsafe { NonNull::new_unchecked(name.as_ptr().cast_mut()) },
            name_len: name.len() as u8,
            inputs: 0,
            outputs: 0,
            not_eof: false,
            terminating: false,
            immediate_size: 0,
        }
    }

    /// Returns the opcode name.
    #[inline]
    pub const fn name(&self) -> &'static str {
        // SAFETY: `self.name_*` can only be initialized with a valid `&'static str`.
        unsafe {
            // TODO : Use `str::from_raw_parts` when it's stable.
            let slice = core::slice::from_raw_parts(self.name_ptr.as_ptr(), self.name_len as usize);
            core::str::from_utf8_unchecked(slice)
        }
    }

    /// Calculates the difference between the number of input and output stack elements.
    #[inline]
    pub const fn io_diff(&self) -> i16 {
        self.outputs as i16 - self.inputs as i16
    }

    /// Returns the number of input stack elements.
    #[inline]
    pub const fn inputs(&self) -> u8 {
        self.inputs
    }

    /// Returns the number of output stack elements.
    #[inline]
    pub const fn outputs(&self) -> u8 {
        self.outputs
    }

    /// Returns whether this opcode is disabled in EOF bytecode.
    #[inline]
    pub const fn is_disabled_in_eof(&self) -> bool {
        self.not_eof
    }

    /// Returns whether this opcode terminates execution, e.g. `STOP`, `RETURN`, etc.
    #[inline]
    pub const fn is_terminating(&self) -> bool {
        self.terminating
    }

    /// Returns the size of the immediate value in bytes.
    #[inline]
    pub const fn immediate_size(&self) -> u8 {
        self.immediate_size
    }
}

/// Sets the EOF flag to false.
#[inline]
pub const fn not_eof(mut op: OpCodeInfo) -> OpCodeInfo {
    op.not_eof = true;
    op
}

/// Sets the immediate bytes number.
///
/// RJUMPV is special case where the bytes len is depending on bytecode value,
/// for RJUMPV size will be set to one byte while minimum is two.
#[inline]
pub const fn immediate_size(mut op: OpCodeInfo, n: u8) -> OpCodeInfo {
    op.immediate_size = n;
    op
}

/// Sets the terminating flag to true.
#[inline]
pub const fn terminating(mut op: OpCodeInfo) -> OpCodeInfo {
    op.terminating = true;
    op
}

/// Sets the number of stack inputs and outputs.
#[inline]
pub const fn stack_io(mut op: OpCodeInfo, inputs: u8, outputs: u8) -> OpCodeInfo {
    op.inputs = inputs;
    op.outputs = outputs;
    op
}

macro_rules! opcodes {
    ($($val:literal => $name:ident => $($modifier:ident $(( $($modifier_arg:expr),* ))?),*);* $(;)?) => {
        // Constants for each opcode. This also takes care of duplicate names.
        $(
            #[doc = concat!("The `", stringify!($val), "` (\"", stringify!($name),"\") opcode.")]
            pub const $name: u8 = $val;
        )*
        impl OpCode {$(
            #[doc = concat!("The `", stringify!($val), "` (\"", stringify!($name),"\") opcode.")]
            pub const $name: Self = Self($val);
        )*}

        /// Maps each opcode to its info.
        pub const OPCODE_INFO: [Option<OpCodeInfo>; 256] = {
            let mut map = [None; 256];
            let mut prev: u8 = 0;
            $(
                let val: u8 = $val;
                assert!(val == 0 || val > prev, "opcodes must be sorted in ascending order");
                prev = val;
                let info = OpCodeInfo::new(stringify!($name));
                $(
                let info = $modifier(info, $($($modifier_arg),*)?);
                )*
                map[$val] = Some(info);
            )*
            let _ = prev;
            map
        };


        /// Maps each name to its opcode.
        #[cfg(feature = "parse")]
        pub(crate) static NAME_TO_OPCODE: phf::Map<&'static str, OpCode> = stringify_with_cb! { phf_map_cb; $($name)* };
    };
}

/// Callback for creating a [`phf`] map with `stringify_with_cb`.
#[cfg(feature = "parse")]
macro_rules! phf_map_cb {
    ($(#[doc = $s:literal] $id:ident)*) => {
        phf::phf_map! {
            $($s => OpCode::$id),*
        }
    };
}

/// Stringifies identifiers with `paste` so that they are available as literals.
///
/// This doesn't work with [`stringify!`] because it cannot be expanded inside of another macro.
#[cfg(feature = "parse")]
macro_rules! stringify_with_cb {
    ($callback:ident; $($id:ident)*) => { paste::paste! {
        $callback! { $(#[doc = "" $id ""] $id)* }
    }};
}

// When adding new opcodes:
// 1. add the opcode to the list below; make sure it's sorted by opcode value
// 2. implement the opcode in the corresponding module;
//    the function signature must be the exact same as the others
opcodes! {
    0x00 => STOP     => stack_io(0, 0), terminating;
    0x01 => ADD      => stack_io(2, 1);
    0x31 => BALANCE    => stack_io(1, 1);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opcode() {
        let opcode = OpCode::new(0x00).unwrap();
        assert!(!opcode.is_jumpdest());
        assert!(!opcode.is_jump());
        assert!(!opcode.is_push());
        assert_eq!(opcode.as_str(), "STOP");
        assert_eq!(opcode.get(), 0x00);
    }

    #[test]
    fn test_eof_disable() {
        const REJECTED_IN_EOF: &[u8] = &[
            0x38, 0x39, 0x3b, 0x3c, 0x3f, 0x5a, 0xf1, 0xf2, 0xf4, 0xfa, 0xff,
        ];

        for opcode in REJECTED_IN_EOF {
            let opcode = OpCode::new(*opcode).unwrap();
            assert!(
                opcode.info().is_disabled_in_eof(),
                "not disabled in EOF: {opcode:#?}",
            );
        }
    }

    #[test]
    fn test_immediate_size() {
        let mut expected = [0u8; 256];
        // PUSH opcodes
        for push in PUSH1..=PUSH32 {
            expected[push as usize] = push - PUSH1 + 1;
        }
        expected[DATALOADN as usize] = 2;
        expected[RJUMP as usize] = 2;
        expected[RJUMPI as usize] = 2;
        expected[RJUMPV as usize] = 1;
        expected[CALLF as usize] = 2;
        expected[JUMPF as usize] = 2;
        expected[DUPN as usize] = 1;
        expected[SWAPN as usize] = 1;
        expected[EXCHANGE as usize] = 1;
        expected[EOFCREATE as usize] = 1;
        expected[RETURNCONTRACT as usize] = 1;

        for (i, opcode) in OPCODE_INFO.iter().enumerate() {
            if let Some(opcode) = opcode {
                assert_eq!(
                    opcode.immediate_size(),
                    expected[i],
                    "immediate_size check failed for {opcode:#?}",
                );
            }
        }
    }

    #[test]
    fn test_enabled_opcodes() {
        // List obtained from https://eips.ethereum.org/EIPS/eip-3670
        let opcodes = [
            0x10..=0x1d,
            0x20..=0x20,
            0x30..=0x3f,
            0x40..=0x48,
            0x50..=0x5b,
            0x54..=0x5f,
            0x60..=0x6f,
            0x70..=0x7f,
            0x80..=0x8f,
            0x90..=0x9f,
            0xa0..=0xa4,
            0xf0..=0xf5,
            0xfa..=0xfa,
            0xfd..=0xfd,
            //0xfe,
            0xff..=0xff,
        ];
        for i in opcodes {
            for opcode in i {
                OpCode::new(opcode).expect("Opcode should be valid and enabled");
            }
        }
    }

    #[test]
    fn count_opcodes() {
        let mut opcode_num = 0;
        let mut eof_opcode_num = 0;
        for opcode in OPCODE_INFO.into_iter().flatten() {
            opcode_num += 1;
            if !opcode.is_disabled_in_eof() {
                eof_opcode_num += 1;
            }
        }
        assert_eq!(opcode_num, 168);
        assert_eq!(eof_opcode_num, 152);
    }

    #[test]
    fn test_terminating_opcodes() {
        let terminating = [
            RETF,
            REVERT,
            RETURN,
            INVALID,
            SELFDESTRUCT,
            RETURNCONTRACT,
            STOP,
            RJUMP,
            JUMPF,
        ];
        let mut opcodes = [false; 256];
        for terminating in terminating.iter() {
            opcodes[*terminating as usize] = true;
        }

        for (i, opcode) in OPCODE_INFO.into_iter().enumerate() {
            assert_eq!(
                opcode.map(|opcode| opcode.terminating).unwrap_or_default(),
                opcodes[i],
                "Opcode {:?} terminating chack failed.",
                opcode
            );
        }
    }

    #[test]
    #[cfg(feature = "parse")]
    fn test_parsing() {
        for i in 0..=u8::MAX {
            if let Some(op) = OpCode::new(i) {
                assert_eq!(OpCode::parse(op.as_str()), Some(op));
            }
        }
    }
}
