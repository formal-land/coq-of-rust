use p3_field::FieldAlgebra;

use super::Interaction;

/// Returns [beta^0, beta^1, ..., beta^{max_num_fields}]
/// where max_num_fields is the maximum length of `fields` in any interaction.
pub fn generate_betas<AF: FieldAlgebra, E>(
    beta: AF,
    all_interactions: &[Interaction<E>],
) -> Vec<AF> {
    let max_fields_len = all_interactions
        .iter()
        .map(|interaction| interaction.message.len())
        .max()
        .unwrap_or(0);

    beta.powers().take(max_fields_len + 1).collect()
}
