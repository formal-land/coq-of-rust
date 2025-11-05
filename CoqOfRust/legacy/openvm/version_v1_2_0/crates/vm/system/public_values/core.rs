use std::sync::Mutex;

use openvm_circuit_primitives::{encoder::Encoder, SubAir};
use openvm_instructions::{
    instruction::Instruction, LocalOpcode, PublishOpcode, PublishOpcode::PUBLISH,
};
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{Deserialize, Serialize};

use crate::{
    arch::{
        AdapterAirContext, AdapterRuntimeContext, BasicAdapterInterface, MinimalInstruction,
        Result, VmAdapterInterface, VmCoreAir, VmCoreChip,
    },
    system::public_values::columns::PublicValuesCoreColsView,
};
pub(crate) type AdapterInterface<F> = BasicAdapterInterface<F, MinimalInstruction<F>, 2, 0, 1, 1>;
pub(crate) type AdapterInterfaceReads<F> = <AdapterInterface<F> as VmAdapterInterface<F>>::Reads;

#[derive(Clone, Debug)]
pub struct PublicValuesCoreAir {
    /// Number of custom public values to publish.
    pub num_custom_pvs: usize,
    encoder: Encoder,
}

impl PublicValuesCoreAir {
    pub fn new(num_custom_pvs: usize, max_degree: u32) -> Self {
        Self {
            num_custom_pvs,
            encoder: Encoder::new(num_custom_pvs, max_degree, true),
        }
    }
}

impl<F: Field> BaseAir<F> for PublicValuesCoreAir {
    fn width(&self) -> usize {
        3 + self.encoder.width()
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for PublicValuesCoreAir {
    fn num_public_values(&self) -> usize {
        self.num_custom_pvs
    }
}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> VmCoreAir<AB, AdapterInterface<AB::Expr>>
    for PublicValuesCoreAir
{
    fn eval(
        &self,
        builder: &mut AB,
        local_core: &[AB::Var],
        _from_pc: AB::Var,
    ) -> AdapterAirContext<AB::Expr, AdapterInterface<AB::Expr>> {
        let cols = PublicValuesCoreColsView::<_, &AB::Var>::borrow(local_core);
        debug_assert_eq!(cols.width(), BaseAir::<AB::F>::width(self));
        let is_valid = *cols.is_valid;
        let value = *cols.value;
        let index = *cols.index;

        let vars = cols.custom_pv_vars.iter().map(|&&x| x).collect::<Vec<_>>();
        self.encoder.eval(builder, &vars);

        let flags = self.encoder.flags::<AB>(&vars);

        let mut match_public_value_index = AB::Expr::ZERO;
        let mut match_public_value = AB::Expr::ZERO;
        for (i, flag) in flags.iter().enumerate() {
            match_public_value_index += flag.clone() * AB::F::from_canonical_usize(i);
            match_public_value += flag.clone() * builder.public_values()[i].into();
        }
        builder.assert_eq(is_valid, self.encoder.is_valid::<AB>(&vars));

        let mut when_publish = builder.when(is_valid);
        when_publish.assert_eq(index, match_public_value_index);
        when_publish.assert_eq(value, match_public_value);

        AdapterAirContext {
            to_pc: None,
            reads: [[value.into()], [index.into()]],
            writes: [],
            instruction: MinimalInstruction {
                is_valid: is_valid.into(),
                opcode: AB::Expr::from_canonical_usize(PUBLISH.global_opcode().as_usize()),
            },
        }
    }

    fn start_offset(&self) -> usize {
        PublishOpcode::CLASS_OFFSET
    }
}

#[repr(C)]
#[derive(Debug, Serialize, Deserialize)]
pub struct PublicValuesRecord<F> {
    value: F,
    index: F,
}

/// ATTENTION: If a specific public value is not provided, a default 0 will be used when generating
/// the proof but in the perspective of constraints, it could be any value.
pub struct PublicValuesCoreChip<F> {
    air: PublicValuesCoreAir,
    // Mutex is to make the struct Sync. But it actually won't be accessed by multiple threads.
    custom_pvs: Mutex<Vec<Option<F>>>,
}

impl<F: PrimeField32> PublicValuesCoreChip<F> {
    /// **Note:** `max_degree` is the maximum degree of the constraint polynomials to represent the
    /// flags. If you want the overall AIR's constraint degree to be `<= max_constraint_degree`,
    /// then typically you should set `max_degree` to `max_constraint_degree - 1`.
    pub fn new(num_custom_pvs: usize, max_degree: u32) -> Self {
        Self {
            air: PublicValuesCoreAir::new(num_custom_pvs, max_degree),
            custom_pvs: Mutex::new(vec![None; num_custom_pvs]),
        }
    }
    pub fn get_custom_public_values(&self) -> Vec<Option<F>> {
        self.custom_pvs.lock().unwrap().clone()
    }
}

impl<F: PrimeField32> VmCoreChip<F, AdapterInterface<F>> for PublicValuesCoreChip<F> {
    type Record = PublicValuesRecord<F>;
    type Air = PublicValuesCoreAir;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        _instruction: &Instruction<F>,
        _from_pc: u32,
        reads: AdapterInterfaceReads<F>,
    ) -> Result<(AdapterRuntimeContext<F, AdapterInterface<F>>, Self::Record)> {
        let [[value], [index]] = reads;
        {
            let idx: usize = index.as_canonical_u32() as usize;
            let mut custom_pvs = self.custom_pvs.lock().unwrap();

            if custom_pvs[idx].is_none() {
                custom_pvs[idx] = Some(value);
            } else {
                // Not a hard constraint violation when publishing the same value twice but the
                // program should avoid that.
                panic!("Custom public value {} already set", idx);
            }
        }
        let output = AdapterRuntimeContext {
            to_pc: None,
            writes: [],
        };
        let record = Self::Record { value, index };
        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!(
            "{:?}",
            PublishOpcode::from_usize(opcode - PublishOpcode::CLASS_OFFSET)
        )
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let mut cols = PublicValuesCoreColsView::<_, &mut F>::borrow_mut(row_slice);
        debug_assert_eq!(cols.width(), BaseAir::<F>::width(&self.air));
        *cols.is_valid = F::ONE;
        *cols.value = record.value;
        *cols.index = record.index;
        let idx: usize = record.index.as_canonical_u32() as usize;
        let pt = self.air.encoder.get_flag_pt(idx);
        for (i, var) in cols.custom_pv_vars.iter_mut().enumerate() {
            **var = F::from_canonical_u32(pt[i]);
        }
    }

    fn generate_public_values(&self) -> Vec<F> {
        self.get_custom_public_values()
            .into_iter()
            .map(|x| x.unwrap_or(F::ZERO))
            .collect()
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}
