use std::{borrow::Borrow, iter};

use openvm_stark_backend::{
    interaction::{InteractionBuilder, PermutationCheckBus},
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::{Field, FieldAlgebra},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::system::memory::merkle::{MemoryDimensions, MemoryMerkleCols, MemoryMerklePvs};

#[derive(Clone, Debug)]
pub struct MemoryMerkleAir<const CHUNK: usize> {
    pub memory_dimensions: MemoryDimensions,
    pub merkle_bus: PermutationCheckBus,
    pub compression_bus: PermutationCheckBus,
}

impl<const CHUNK: usize, F: Field> PartitionedBaseAir<F> for MemoryMerkleAir<CHUNK> {}
impl<const CHUNK: usize, F: Field> BaseAir<F> for MemoryMerkleAir<CHUNK> {
    fn width(&self) -> usize {
        MemoryMerkleCols::<F, CHUNK>::width()
    }
}
impl<const CHUNK: usize, F: Field> BaseAirWithPublicValues<F> for MemoryMerkleAir<CHUNK> {
    fn num_public_values(&self) -> usize {
        MemoryMerklePvs::<F, CHUNK>::width()
    }
}

impl<const CHUNK: usize, AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB>
    for MemoryMerkleAir<CHUNK>
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (main.row_slice(0), main.row_slice(1));
        let local: &MemoryMerkleCols<_, CHUNK> = (*local).borrow();
        let next: &MemoryMerkleCols<_, CHUNK> = (*next).borrow();

        // `expand_direction` should be -1, 0, 1
        builder.assert_eq(
            local.expand_direction,
            local.expand_direction * local.expand_direction * local.expand_direction,
        );

        builder.assert_bool(local.left_direction_different);
        builder.assert_bool(local.right_direction_different);

        // if `expand_direction` != -1, then `*_direction_different` should be 0
        builder
            .when_ne(local.expand_direction, AB::F::NEG_ONE)
            .assert_zero(local.left_direction_different);
        builder
            .when_ne(local.expand_direction, AB::F::NEG_ONE)
            .assert_zero(local.right_direction_different);

        // rows should be sorted in descending order
        // independently by `parent_height`, `height_section`, `is_root`
        builder
            .when_transition()
            .assert_bool(local.parent_height - next.parent_height);
        builder
            .when_transition()
            .assert_bool(local.height_section - next.height_section);
        builder
            .when_transition()
            .assert_bool(local.is_root - next.is_root);

        // row with greatest height should have `height_section` = 1
        builder.when_first_row().assert_one(local.height_section);
        // two rows with greatest height should have `is_root` = 1
        builder.when_first_row().assert_one(local.is_root);
        builder.when_first_row().assert_one(next.is_root);
        // row with least height should have `height_section` = 0, `is_root` = 0
        builder.when_last_row().assert_zero(local.height_section);
        builder.when_last_row().assert_zero(local.is_root);
        // `height_section` changes from 0 to 1 only when `parent_height` changes from
        // `address_height` to `address_height` + 1
        builder
            .when_transition()
            .when_ne(
                local.parent_height,
                AB::F::from_canonical_usize(self.memory_dimensions.address_height + 1),
            )
            .assert_eq(local.height_section, next.height_section);
        builder
            .when_transition()
            .when_ne(
                next.parent_height,
                AB::F::from_canonical_usize(self.memory_dimensions.address_height),
            )
            .assert_eq(local.height_section, next.height_section);
        // two adjacent rows with `is_root` = 1 should have
        // the first `expand_direction` = 1, the second `expand_direction` = -1
        builder
            .when(local.is_root)
            .when(next.is_root)
            .assert_eq(local.expand_direction - next.expand_direction, AB::F::TWO);

        // roots should have correct height
        builder.when(local.is_root).assert_eq(
            local.parent_height,
            AB::Expr::from_canonical_usize(self.memory_dimensions.overall_height()),
        );

        // constrain public values
        let &MemoryMerklePvs::<_, CHUNK> {
            initial_root,
            final_root,
        } = builder.public_values().borrow();
        for i in 0..CHUNK {
            builder
                .when_first_row()
                .assert_eq(local.parent_hash[i], initial_root[i]);
            builder
                .when_first_row()
                .assert_eq(next.parent_hash[i], final_root[i]);
        }

        self.eval_interactions(builder, local);
    }
}

impl<const CHUNK: usize> MemoryMerkleAir<CHUNK> {
    pub fn eval_interactions<AB: InteractionBuilder>(
        &self,
        builder: &mut AB,
        local: &MemoryMerkleCols<AB::Var, CHUNK>,
    ) {
        // interaction does not occur for first two rows;
        // for those, parent hash value comes from public values
        self.merkle_bus.interact(
            builder,
            [
                local.expand_direction.into(),
                local.parent_height.into(),
                local.parent_as_label.into(),
                local.parent_address_label.into(),
            ]
            .into_iter()
            .chain(local.parent_hash.into_iter().map(Into::into)),
            // count can probably be made degree 1 if necessary
            (AB::Expr::ONE - local.is_root) * local.expand_direction,
        );

        self.merkle_bus.interact(
            builder,
            [
                local.expand_direction + (local.left_direction_different * AB::F::TWO),
                local.parent_height - AB::F::ONE,
                local.parent_as_label * (AB::Expr::ONE + local.height_section),
                local.parent_address_label * (AB::Expr::TWO - local.height_section),
            ]
            .into_iter()
            .chain(local.left_child_hash.into_iter().map(Into::into)),
            -local.expand_direction.into(),
        );

        self.merkle_bus.interact(
            builder,
            [
                local.expand_direction + (local.right_direction_different * AB::F::TWO),
                local.parent_height - AB::F::ONE,
                (local.parent_as_label * (AB::Expr::ONE + local.height_section))
                    + local.height_section,
                (local.parent_address_label * (AB::Expr::TWO - local.height_section))
                    + (AB::Expr::ONE - local.height_section),
            ]
            .into_iter()
            .chain(local.right_child_hash.into_iter().map(Into::into)),
            -local.expand_direction.into(),
        );

        let compress_fields = iter::empty()
            .chain(local.left_child_hash)
            .chain(local.right_child_hash)
            .chain(local.parent_hash);
        self.compression_bus.interact(
            builder,
            compress_fields,
            local.expand_direction * local.expand_direction,
        );
    }
}
