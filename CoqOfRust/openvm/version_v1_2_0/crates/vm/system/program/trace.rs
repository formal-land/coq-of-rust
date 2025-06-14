use std::{borrow::BorrowMut, sync::Arc};

use derivative::Derivative;
use itertools::Itertools;
use openvm_circuit::arch::hasher::poseidon2::Poseidon2Hasher;
use openvm_instructions::{exe::VmExe, program::Program, LocalOpcode, SystemOpcode};
use openvm_stark_backend::{
    config::{Com, Domain, StarkGenericConfig, Val},
    p3_commit::{Pcs, PolynomialSpace},
    p3_field::{Field, FieldAlgebra, PrimeField32, PrimeField64},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    p3_maybe_rayon::prelude::*,
    prover::{
        helper::AirProofInputTestHelper,
        types::{AirProofInput, AirProofRawInput, CommittedTraceData},
    },
};
use serde::{Deserialize, Serialize};

use super::{Instruction, ProgramChip, ProgramExecutionCols, EXIT_CODE_FAIL};
use crate::{
    arch::{
        hasher::{poseidon2::vm_poseidon2_hasher, Hasher},
        MemoryConfig,
    },
    system::memory::{tree::MemoryNode, AddressMap, CHUNK},
};

#[derive(Serialize, Deserialize, Derivative)]
#[serde(bound(
    serialize = "VmExe<Val<SC>>: Serialize, CommittedTraceData<SC>: Serialize",
    deserialize = "VmExe<Val<SC>>: Deserialize<'de>, CommittedTraceData<SC>: Deserialize<'de>"
))]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
pub struct VmCommittedExe<SC: StarkGenericConfig> {
    /// Raw executable.
    pub exe: VmExe<Val<SC>>,
    /// Committed program trace.
    pub committed_program: CommittedTraceData<SC>,
}

impl<SC: StarkGenericConfig> VmCommittedExe<SC>
where
    Val<SC>: PrimeField32,
{
    /// Creates [VmCommittedExe] from [VmExe] by using `pcs` to commit to the
    /// program code as a _cached trace_ matrix.
    pub fn commit(exe: VmExe<Val<SC>>, pcs: &SC::Pcs) -> Self {
        let cached_trace = generate_cached_trace(&exe.program);
        let domain = pcs.natural_domain_for_degree(cached_trace.height());
        let (commitment, pcs_data) = pcs.commit(vec![(domain, cached_trace.clone())]);
        Self {
            committed_program: CommittedTraceData {
                trace: Arc::new(cached_trace),
                commitment,
                pcs_data: Arc::new(pcs_data),
            },
            exe,
        }
    }
    pub fn get_program_commit(&self) -> Com<SC> {
        self.committed_program.commitment.clone()
    }

    /// Computes a commitment to [VmCommittedExe]. This is a Merklelized hash of:
    /// - Program code commitment (commitment of the cached trace)
    /// - Merkle root of the initial memory
    /// - Starting program counter (`pc_start`)
    ///
    /// The program code commitment is itself a commitment (via the proof system PCS) to
    /// the program code.
    ///
    /// The Merklelization uses Poseidon2 as a cryptographic hash function (for the leaves)
    /// and a cryptographic compression function (for internal nodes).
    ///
    /// **Note**: This function recomputes the Merkle tree for the initial memory image.
    pub fn compute_exe_commit(&self, memory_config: &MemoryConfig) -> Com<SC>
    where
        Com<SC>: AsRef<[Val<SC>; CHUNK]> + From<[Val<SC>; CHUNK]>,
    {
        let hasher = vm_poseidon2_hasher();
        let memory_dimensions = memory_config.memory_dimensions();
        let app_program_commit: &[Val<SC>; CHUNK] = self.committed_program.commitment.as_ref();
        let mem_config = memory_config;
        let init_memory_commit = MemoryNode::tree_from_memory(
            memory_dimensions,
            &AddressMap::from_iter(
                mem_config.as_offset,
                1 << mem_config.as_height,
                1 << mem_config.pointer_max_bits,
                self.exe.init_memory.clone(),
            ),
            &hasher,
        )
        .hash();
        Com::<SC>::from(compute_exe_commit(
            &hasher,
            app_program_commit,
            &init_memory_commit,
            Val::<SC>::from_canonical_u32(self.exe.pc_start),
        ))
    }
}

impl<F: PrimeField64> ProgramChip<F> {
    pub fn generate_air_proof_input<SC: StarkGenericConfig>(
        self,
        cached: Option<CommittedTraceData<SC>>,
    ) -> AirProofInput<SC>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        let common_trace = RowMajorMatrix::new_col(
            self.execution_frequencies
                .into_iter()
                .zip_eq(self.program.instructions_and_debug_infos.iter())
                .filter_map(|(frequency, option)| {
                    option.as_ref().map(|_| F::from_canonical_usize(frequency))
                })
                .collect::<Vec<F>>(),
        );
        if let Some(cached) = cached {
            AirProofInput {
                cached_mains_pdata: vec![(cached.commitment, cached.pcs_data)],
                raw: AirProofRawInput {
                    cached_mains: vec![cached.trace],
                    common_main: Some(common_trace),
                    public_values: vec![],
                },
            }
        } else {
            AirProofInput::cached_traces_no_pis(
                vec![generate_cached_trace(&self.program)],
                common_trace,
            )
        }
    }
}

/// Computes a Merklelized hash of:
/// - Program code commitment (commitment of the cached trace)
/// - Merkle root of the initial memory
/// - Starting program counter (`pc_start`)
///
/// The Merklelization uses [Poseidon2Hasher] as a cryptographic hash function (for the leaves)
/// and a cryptographic compression function (for internal nodes).
pub fn compute_exe_commit<F: PrimeField32>(
    hasher: &Poseidon2Hasher<F>,
    program_commit: &[F; CHUNK],
    init_memory_root: &[F; CHUNK],
    pc_start: F,
) -> [F; CHUNK] {
    let mut padded_pc_start = [F::ZERO; CHUNK];
    padded_pc_start[0] = pc_start;
    let program_hash = hasher.hash(program_commit);
    let memory_hash = hasher.hash(init_memory_root);
    let pc_hash = hasher.hash(&padded_pc_start);
    hasher.compress(&hasher.compress(&program_hash, &memory_hash), &pc_hash)
}

pub(crate) fn generate_cached_trace<F: PrimeField64>(program: &Program<F>) -> RowMajorMatrix<F> {
    let width = ProgramExecutionCols::<F>::width();
    let mut instructions = program
        .enumerate_by_pc()
        .into_iter()
        .map(|(pc, instruction, _)| (pc, instruction))
        .collect_vec();

    let padding = padding_instruction();
    while !instructions.len().is_power_of_two() {
        instructions.push((
            program.pc_base + instructions.len() as u32 * program.step,
            padding.clone(),
        ));
    }

    let mut rows = F::zero_vec(instructions.len() * width);
    rows.par_chunks_mut(width)
        .zip(instructions)
        .for_each(|(row, (pc, instruction))| {
            let row: &mut ProgramExecutionCols<F> = row.borrow_mut();
            *row = ProgramExecutionCols {
                pc: F::from_canonical_u32(pc),
                opcode: instruction.opcode.to_field(),
                a: instruction.a,
                b: instruction.b,
                c: instruction.c,
                d: instruction.d,
                e: instruction.e,
                f: instruction.f,
                g: instruction.g,
            };
        });

    RowMajorMatrix::new(rows, width)
}

pub(super) fn padding_instruction<F: Field>() -> Instruction<F> {
    Instruction::from_usize(
        SystemOpcode::TERMINATE.global_opcode(),
        [0, 0, EXIT_CODE_FAIL],
    )
}
