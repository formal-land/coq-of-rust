use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, Result, VmAdapterInterface, VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::{
    utils::select,
    var_range::{SharedVariableRangeCheckerChip, VariableRangeCheckerBus},
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::Rv32LoadStoreOpcode::{self, *};
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::BaseAir,
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_big_array::BigArray;

use crate::adapters::LoadStoreInstruction;

/// LoadSignExtend Core Chip handles byte/halfword into word conversions through sign extend
/// This chip uses read_data to construct write_data
/// prev_data columns are not used in constraints defined in the CoreAir, but are used in
/// constraints by the Adapter shifted_read_data is the read_data shifted by (shift_amount & 2),
/// this reduces the number of opcode flags needed using this shifted data we can generate the
/// write_data as if the shift_amount was 0 for loadh and 0 or 1 for loadb
#[repr(C)]
#[derive(Debug, Clone, AlignedBorrow)]
pub struct LoadSignExtendCoreCols<T, const NUM_CELLS: usize> {
    /// This chip treats loadb with 0 shift and loadb with 1 shift as different instructions
    pub opcode_loadb_flag0: T,
    pub opcode_loadb_flag1: T,
    pub opcode_loadh_flag: T,

    pub shift_most_sig_bit: T,
    // The bit that is extended to the remaining bits
    pub data_most_sig_bit: T,

    pub shifted_read_data: [T; NUM_CELLS],
    pub prev_data: [T; NUM_CELLS],
}

#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(bound = "F: Serialize + DeserializeOwned")]
pub struct LoadSignExtendCoreRecord<F, const NUM_CELLS: usize> {
    #[serde(with = "BigArray")]
    pub shifted_read_data: [F; NUM_CELLS],
    #[serde(with = "BigArray")]
    pub prev_data: [F; NUM_CELLS],
    pub opcode: Rv32LoadStoreOpcode,
    pub shift_amount: u32,
    pub most_sig_bit: bool,
}

#[derive(Debug, Clone)]
pub struct LoadSignExtendCoreAir<const NUM_CELLS: usize, const LIMB_BITS: usize> {
    pub range_bus: VariableRangeCheckerBus,
}

impl<F: Field, const NUM_CELLS: usize, const LIMB_BITS: usize> BaseAir<F>
    for LoadSignExtendCoreAir<NUM_CELLS, LIMB_BITS>
{
    fn width(&self) -> usize {
        LoadSignExtendCoreCols::<F, NUM_CELLS>::width()
    }
}

impl<F: Field, const NUM_CELLS: usize, const LIMB_BITS: usize> BaseAirWithPublicValues<F>
    for LoadSignExtendCoreAir<NUM_CELLS, LIMB_BITS>
{
}

impl<AB, I, const NUM_CELLS: usize, const LIMB_BITS: usize> VmCoreAir<AB, I>
    for LoadSignExtendCoreAir<NUM_CELLS, LIMB_BITS>
where
    AB: InteractionBuilder,
    I: VmAdapterInterface<AB::Expr>,
    I::Reads: From<([AB::Var; NUM_CELLS], [AB::Expr; NUM_CELLS])>,
    I::Writes: From<[[AB::Expr; NUM_CELLS]; 1]>,
    I::ProcessedInstruction: From<LoadStoreInstruction<AB::Expr>>,
{
    fn eval(
        &self,
        builder: &mut AB,
        local_core: &[AB::Var],
        _from_pc: AB::Var,
    ) -> AdapterAirContext<AB::Expr, I> {
        let cols: &LoadSignExtendCoreCols<AB::Var, NUM_CELLS> = (*local_core).borrow();
        let LoadSignExtendCoreCols::<AB::Var, NUM_CELLS> {
            shifted_read_data,
            prev_data,
            opcode_loadb_flag0: is_loadb0,
            opcode_loadb_flag1: is_loadb1,
            opcode_loadh_flag: is_loadh,
            data_most_sig_bit,
            shift_most_sig_bit,
        } = *cols;

        let flags = [is_loadb0, is_loadb1, is_loadh];

        let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
            builder.assert_bool(flag);
            acc + flag
        });

        builder.assert_bool(is_valid.clone());
        builder.assert_bool(data_most_sig_bit);
        builder.assert_bool(shift_most_sig_bit);

        let expected_opcode = (is_loadb0 + is_loadb1) * AB::F::from_canonical_u8(LOADB as u8)
            + is_loadh * AB::F::from_canonical_u8(LOADH as u8)
            + AB::Expr::from_canonical_usize(Rv32LoadStoreOpcode::CLASS_OFFSET);

        let limb_mask = data_most_sig_bit * AB::Expr::from_canonical_u32((1 << LIMB_BITS) - 1);

        // there are three parts to write_data:
        // - 1st limb is always shifted_read_data
        // - 2nd to (NUM_CELLS/2)th limbs are read_data if loadh and sign extended if loadb
        // - (NUM_CELLS/2 + 1)th to last limbs are always sign extended limbs
        let write_data: [AB::Expr; NUM_CELLS] = array::from_fn(|i| {
            if i == 0 {
                (is_loadh + is_loadb0) * shifted_read_data[i].into()
                    + is_loadb1 * shifted_read_data[i + 1].into()
            } else if i < NUM_CELLS / 2 {
                shifted_read_data[i] * is_loadh + (is_loadb0 + is_loadb1) * limb_mask.clone()
            } else {
                limb_mask.clone()
            }
        });

        // Constrain that most_sig_bit is correct
        let most_sig_limb = shifted_read_data[0] * is_loadb0
            + shifted_read_data[1] * is_loadb1
            + shifted_read_data[NUM_CELLS / 2 - 1] * is_loadh;

        self.range_bus
            .range_check(
                most_sig_limb
                    - data_most_sig_bit * AB::Expr::from_canonical_u32(1 << (LIMB_BITS - 1)),
                LIMB_BITS - 1,
            )
            .eval(builder, is_valid.clone());

        // Unshift the shifted_read_data to get the original read_data
        let read_data = array::from_fn(|i| {
            select(
                shift_most_sig_bit,
                shifted_read_data[(i + NUM_CELLS - 2) % NUM_CELLS],
                shifted_read_data[i],
            )
        });
        let load_shift_amount = shift_most_sig_bit * AB::Expr::TWO + is_loadb1;

        AdapterAirContext {
            to_pc: None,
            reads: (prev_data, read_data).into(),
            writes: [write_data].into(),
            instruction: LoadStoreInstruction {
                is_valid: is_valid.clone(),
                opcode: expected_opcode,
                is_load: is_valid,
                load_shift_amount,
                store_shift_amount: AB::Expr::ZERO,
            }
            .into(),
        }
    }

    fn start_offset(&self) -> usize {
        Rv32LoadStoreOpcode::CLASS_OFFSET
    }
}

pub struct LoadSignExtendCoreChip<const NUM_CELLS: usize, const LIMB_BITS: usize> {
    pub air: LoadSignExtendCoreAir<NUM_CELLS, LIMB_BITS>,
    pub range_checker_chip: SharedVariableRangeCheckerChip,
}

impl<const NUM_CELLS: usize, const LIMB_BITS: usize> LoadSignExtendCoreChip<NUM_CELLS, LIMB_BITS> {
    pub fn new(range_checker_chip: SharedVariableRangeCheckerChip) -> Self {
        Self {
            air: LoadSignExtendCoreAir::<NUM_CELLS, LIMB_BITS> {
                range_bus: range_checker_chip.bus(),
            },
            range_checker_chip,
        }
    }
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_CELLS: usize, const LIMB_BITS: usize>
    VmCoreChip<F, I> for LoadSignExtendCoreChip<NUM_CELLS, LIMB_BITS>
where
    I::Reads: Into<([[F; NUM_CELLS]; 2], F)>,
    I::Writes: From<[[F; NUM_CELLS]; 1]>,
{
    type Record = LoadSignExtendCoreRecord<F, NUM_CELLS>;
    type Air = LoadSignExtendCoreAir<NUM_CELLS, LIMB_BITS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        _from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let local_opcode = Rv32LoadStoreOpcode::from_usize(
            instruction
                .opcode
                .local_opcode_idx(Rv32LoadStoreOpcode::CLASS_OFFSET),
        );

        let (data, shift_amount) = reads.into();
        let shift_amount = shift_amount.as_canonical_u32();
        let write_data: [F; NUM_CELLS] = run_write_data_sign_extend::<_, NUM_CELLS, LIMB_BITS>(
            local_opcode,
            data[1],
            data[0],
            shift_amount,
        );
        let output = AdapterRuntimeContext::without_pc([write_data]);

        let most_sig_limb = match local_opcode {
            LOADB => write_data[0],
            LOADH => write_data[NUM_CELLS / 2 - 1],
            _ => unreachable!(),
        }
        .as_canonical_u32();

        let most_sig_bit = most_sig_limb & (1 << (LIMB_BITS - 1));
        self.range_checker_chip
            .add_count(most_sig_limb - most_sig_bit, LIMB_BITS - 1);

        let read_shift = shift_amount & 2;

        Ok((
            output,
            LoadSignExtendCoreRecord {
                opcode: local_opcode,
                most_sig_bit: most_sig_bit != 0,
                prev_data: data[0],
                shifted_read_data: array::from_fn(|i| {
                    data[1][(i + read_shift as usize) % NUM_CELLS]
                }),
                shift_amount,
            },
        ))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!(
            "{:?}",
            Rv32LoadStoreOpcode::from_usize(opcode - Rv32LoadStoreOpcode::CLASS_OFFSET)
        )
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let core_cols: &mut LoadSignExtendCoreCols<F, NUM_CELLS> = row_slice.borrow_mut();
        let opcode = record.opcode;
        let shift = record.shift_amount;
        core_cols.opcode_loadb_flag0 = F::from_bool(opcode == LOADB && (shift & 1) == 0);
        core_cols.opcode_loadb_flag1 = F::from_bool(opcode == LOADB && (shift & 1) == 1);
        core_cols.opcode_loadh_flag = F::from_bool(opcode == LOADH);
        core_cols.shift_most_sig_bit = F::from_canonical_u32((shift & 2) >> 1);
        core_cols.data_most_sig_bit = F::from_bool(record.most_sig_bit);
        core_cols.prev_data = record.prev_data;
        core_cols.shifted_read_data = record.shifted_read_data;
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

pub(super) fn run_write_data_sign_extend<
    F: PrimeField32,
    const NUM_CELLS: usize,
    const LIMB_BITS: usize,
>(
    opcode: Rv32LoadStoreOpcode,
    read_data: [F; NUM_CELLS],
    _prev_data: [F; NUM_CELLS],
    shift: u32,
) -> [F; NUM_CELLS] {
    let shift = shift as usize;
    let mut write_data = read_data;
    match (opcode, shift) {
        (LOADH, 0) | (LOADH, 2) => {
            let ext = read_data[NUM_CELLS / 2 - 1 + shift].as_canonical_u32();
            let ext = (ext >> (LIMB_BITS - 1)) * ((1 << LIMB_BITS) - 1);
            for cell in write_data.iter_mut().take(NUM_CELLS).skip(NUM_CELLS / 2) {
                *cell = F::from_canonical_u32(ext);
            }
            write_data[0..NUM_CELLS / 2]
                .copy_from_slice(&read_data[shift..(NUM_CELLS / 2 + shift)]);
        }
        (LOADB, 0) | (LOADB, 1) | (LOADB, 2) | (LOADB, 3) => {
            let ext = read_data[shift].as_canonical_u32();
            let ext = (ext >> (LIMB_BITS - 1)) * ((1 << LIMB_BITS) - 1);
            for cell in write_data.iter_mut().take(NUM_CELLS).skip(1) {
                *cell = F::from_canonical_u32(ext);
            }
            write_data[0] = read_data[shift];
        }
        // Currently the adapter AIR requires `ptr_val` to be aligned to the data size in bytes.
        // The circuit requires that `shift = ptr_val % 4` so that `ptr_val - shift` is a multiple of 4.
        // This requirement is non-trivial to remove, because we use it to ensure that `ptr_val - shift + 4 <= 2^pointer_max_bits`.
        _ => unreachable!(
            "unaligned memory access not supported by this execution environment: {opcode:?}, shift: {shift}"
        ),
    };
    write_data
}
