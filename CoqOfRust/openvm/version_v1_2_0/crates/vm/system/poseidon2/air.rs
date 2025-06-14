use std::{array::from_fn, borrow::Borrow, sync::Arc};

use derive_new::new;
use openvm_poseidon2_air::{
    Poseidon2SubAir, BABY_BEAR_POSEIDON2_HALF_FULL_ROUNDS, POSEIDON2_WIDTH,
};
use openvm_stark_backend::{
    air_builders::sub::SubAirBuilder,
    interaction::{InteractionBuilder, LookupBus},
    p3_air::{Air, BaseAir},
    p3_field::Field,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use super::columns::Poseidon2PeripheryCols;

/// Poseidon2 Air, VM version.
///
/// Carries the subair for subtrace generation. Sticking to the conventions, this struct carries no
/// state. `direct` determines whether direct interactions are enabled. By default they are on.
#[derive(Clone, new, Debug)]
pub struct Poseidon2PeripheryAir<F: Field, const SBOX_REGISTERS: usize> {
    pub(super) subair: Arc<Poseidon2SubAir<F, SBOX_REGISTERS>>,
    pub(super) bus: LookupBus,
}

impl<F: Field, const SBOX_REGISTERS: usize> BaseAirWithPublicValues<F>
    for Poseidon2PeripheryAir<F, SBOX_REGISTERS>
{
}
impl<F: Field, const SBOX_REGISTERS: usize> PartitionedBaseAir<F>
    for Poseidon2PeripheryAir<F, SBOX_REGISTERS>
{
}
impl<F: Field, const SBOX_REGISTERS: usize> BaseAir<F>
    for Poseidon2PeripheryAir<F, SBOX_REGISTERS>
{
    fn width(&self) -> usize {
        Poseidon2PeripheryCols::<F, SBOX_REGISTERS>::width()
    }
}

impl<AB: InteractionBuilder, const SBOX_REGISTERS: usize> Air<AB>
    for Poseidon2PeripheryAir<AB::F, SBOX_REGISTERS>
{
    fn eval(&self, builder: &mut AB) {
        let mut sub_builder =
            SubAirBuilder::<AB, Poseidon2SubAir<AB::F, SBOX_REGISTERS>, AB::F>::new(
                builder,
                0..self.subair.width(),
            );
        self.subair.eval(&mut sub_builder);

        let main = builder.main();
        let local = main.row_slice(0);
        let cols: &Poseidon2PeripheryCols<AB::Var, SBOX_REGISTERS> = (*local).borrow();

        let input: [AB::Var; POSEIDON2_WIDTH] = cols.inner.inputs;
        let output: [AB::Var; POSEIDON2_WIDTH] =
            cols.inner.ending_full_rounds[BABY_BEAR_POSEIDON2_HALF_FULL_ROUNDS - 1].post;
        let fields: [_; POSEIDON2_WIDTH + POSEIDON2_WIDTH / 2] = from_fn(|i| {
            if i < POSEIDON2_WIDTH {
                input[i]
            } else {
                output[i - POSEIDON2_WIDTH]
            }
        });
        self.bus.add_key_with_lookups(builder, fields, cols.mult);
    }
}
