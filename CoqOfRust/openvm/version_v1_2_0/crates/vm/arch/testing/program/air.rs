use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::Field,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use super::ProgramTester;
use crate::system::program::ProgramBus;

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct ProgramDummyAir {
    pub bus: ProgramBus,
}

impl<F: Field> BaseAirWithPublicValues<F> for ProgramDummyAir {}
impl<F: Field> PartitionedBaseAir<F> for ProgramDummyAir {}
impl<F: Field> BaseAir<F> for ProgramDummyAir {
    fn width(&self) -> usize {
        ProgramTester::<F>::width()
    }
}

impl<AB: InteractionBuilder> Air<AB> for ProgramDummyAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local = local.iter().map(|x| (*x).into()).collect::<Vec<AB::Expr>>();
        self.bus.inner.add_key_with_lookups(
            builder,
            local[..local.len() - 1].iter().cloned(),
            local[local.len() - 1].clone(),
        );
    }
}
