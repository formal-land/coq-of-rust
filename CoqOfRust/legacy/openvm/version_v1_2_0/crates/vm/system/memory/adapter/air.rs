use std::{borrow::Borrow, mem::size_of};

use openvm_circuit_primitives::{
    is_less_than::{IsLessThanIo, IsLtSubAir},
    SubAir,
};
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::FieldAlgebra,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::system::memory::{
    adapter::columns::AccessAdapterCols, offline_checker::MemoryBus, MemoryAddress,
};

#[derive(Clone, Debug)]
pub struct AccessAdapterAir<const N: usize> {
    pub memory_bus: MemoryBus,
    pub lt_air: IsLtSubAir,
}

impl<T, const N: usize> BaseAirWithPublicValues<T> for AccessAdapterAir<N> {}
impl<T, const N: usize> PartitionedBaseAir<T> for AccessAdapterAir<N> {}
impl<T, const N: usize> BaseAir<T> for AccessAdapterAir<N> {
    fn width(&self) -> usize {
        size_of::<AccessAdapterCols<u8, N>>()
    }
}

impl<const N: usize, AB: InteractionBuilder> Air<AB> for AccessAdapterAir<N> {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let local: &AccessAdapterCols<AB::Var, N> = (*local).borrow();

        builder.assert_bool(local.is_split);
        builder.assert_bool(local.is_valid);
        builder.assert_bool(local.is_right_larger);

        // Timestamp constraints:
        // - if `is_split`, then all timestamps are equal.
        // - if `is_merge`, then parent_timestamp = max(left_timestamp, right_timestamp)

        builder
            .when(local.is_split)
            .assert_eq(local.left_timestamp, local.right_timestamp);

        self.lt_air.eval(
            builder,
            (
                IsLessThanIo {
                    x: local.left_timestamp.into(),
                    y: local.right_timestamp.into(),
                    out: local.is_right_larger.into(),
                    count: local.is_valid.into(),
                },
                &local.lt_aux,
            ),
        );

        let parent_timestamp = local.is_right_larger * local.right_timestamp
            + (AB::Expr::ONE - local.is_right_larger) * local.left_timestamp;

        // assuming valid:
        // Split = 1 => direction = 1 => receive parent with count 1, send left/right with count 1
        // Split = 0 => direction = -1 => receive parent with count -1, send left/right with count
        // -1
        let direction = local.is_valid * (AB::Expr::TWO * local.is_split - AB::Expr::ONE);

        self.memory_bus
            .receive(local.address, local.values.to_vec(), parent_timestamp)
            .eval(builder, direction.clone());

        self.memory_bus
            .send(
                local.address,
                local.values[..N / 2].to_vec(),
                local.left_timestamp,
            )
            .eval(builder, direction.clone());

        self.memory_bus
            .send(
                MemoryAddress::new(
                    local.address.address_space,
                    local.address.pointer + AB::Expr::from_canonical_usize(N / 2),
                ),
                local.values[N / 2..].to_vec(),
                local.right_timestamp,
            )
            .eval(builder, direction.clone());
    }
}
