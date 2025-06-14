use std::ops::Index;

use p3_field::Field;
use thiserror::Error;

use crate::{
    poly::{
        multi::{fold_mle_evals, Mle, MultivariatePolyOracle},
        uni::Fraction,
    },
    sumcheck::{SumcheckError, SumcheckProof},
};

/// Batch GKR proof.
pub struct GkrBatchProof<F> {
    /// Sum-check proof for each layer.
    pub sumcheck_proofs: Vec<SumcheckProof<F>>,
    /// Mask for each layer for each instance.
    pub layer_masks_by_instance: Vec<Vec<GkrMask<F>>>,
    /// Column circuit outputs for each instance.
    pub output_claims_by_instance: Vec<Vec<F>>,
}

/// Values of interest obtained from the execution of the GKR protocol.
pub struct GkrArtifact<F> {
    /// Out-of-domain (OOD) point for evaluating columns in the input layer.
    pub ood_point: Vec<F>,
    /// The claimed evaluation at `ood_point` for each column in the input layer of each instance.
    pub claims_to_verify_by_instance: Vec<Vec<F>>,
    /// The number of variables that interpolate the input layer of each instance.
    pub n_variables_by_instance: Vec<usize>,
}

/// Stores two evaluations of each column in a GKR layer.
#[derive(Debug, Clone)]
pub struct GkrMask<F> {
    columns: Vec<[F; 2]>,
}

impl<F> GkrMask<F> {
    pub fn new(columns: Vec<[F; 2]>) -> Self {
        Self { columns }
    }

    pub fn columns(&self) -> &[[F; 2]] {
        &self.columns
    }
}

impl<F: Field> GkrMask<F> {
    pub fn to_rows(&self) -> [Vec<F>; 2] {
        self.columns.iter().map(|[a, b]| (a, b)).unzip().into()
    }

    /// Returns all `p_i(x)` where `p_i` interpolates column `i` of the mask on `{0, 1}`.
    pub fn reduce_at_point(&self, x: F) -> Vec<F> {
        self.columns
            .iter()
            .map(|&[v0, v1]| fold_mle_evals(x, v0, v1))
            .collect()
    }
}

/// Error encountered during GKR protocol verification.
#[derive(Error, Debug)]
pub enum GkrError<F> {
    /// The proof is malformed.
    #[error("proof data is invalid")]
    MalformedProof,
    /// Mask has an invalid number of columns.
    #[error("mask in layer {instance_layer} of instance {instance} is invalid")]
    InvalidMask {
        instance: usize,
        /// Layer of the instance (but not necessarily the batch).
        instance_layer: LayerIndex,
    },
    /// There is a mismatch between the number of instances in the proof and the number of
    /// instances passed for verification.
    #[error("provided an invalid number of instances (given {given}, proof expects {proof})")]
    NumInstancesMismatch { given: usize, proof: usize },
    /// There was an error with one of the sumcheck proofs.
    #[error("sum-check invalid in layer {layer}: {source}")]
    InvalidSumcheck {
        layer: LayerIndex,
        source: SumcheckError<F>,
    },
    /// The circuit polynomial the verifier evaluated doesn't match claim from sumcheck.
    #[error("circuit check failed in layer {layer} (calculated {output}, claim {claim})")]
    CircuitCheckFailure {
        claim: F,
        output: F,
        layer: LayerIndex,
    },
}

/// GKR layer index where 0 corresponds to the output layer.
pub type LayerIndex = usize;

/// Represents a layer in a binary tree structured GKR circuit.
///
/// Layers can contain multiple columns, for example [LogUp] which has separate columns for
/// numerators and denominators.
///
/// [LogUp]: https://eprint.iacr.org/2023/1284.pdf
#[derive(Debug, Clone)]
pub enum Layer<F> {
    GrandProduct(Mle<F>),
    LogUpGeneric {
        numerators: Mle<F>,
        denominators: Mle<F>,
    },
    LogUpMultiplicities {
        numerators: Mle<F>,
        denominators: Mle<F>,
    },
    /// All numerators implicitly equal "1".
    LogUpSingles {
        denominators: Mle<F>,
    },
}

impl<F: Field> Layer<F> {
    /// Returns the number of variables used to interpolate the layer's gate values.
    pub fn n_variables(&self) -> usize {
        match self {
            Self::GrandProduct(mle)
            | Self::LogUpSingles { denominators: mle }
            | Self::LogUpMultiplicities {
                denominators: mle, ..
            }
            | Self::LogUpGeneric {
                denominators: mle, ..
            } => mle.arity(),
        }
    }

    fn is_output_layer(&self) -> bool {
        self.n_variables() == 0
    }

    /// Produces the next layer from the current layer.
    ///
    /// The next layer is strictly half the size of the current layer.
    /// Returns [`None`] if called on an output layer.
    pub fn next_layer(&self) -> Option<Self> {
        if self.is_output_layer() {
            return None;
        }

        let next_layer = match self {
            Layer::GrandProduct(layer) => Self::next_grand_product_layer(layer),
            Layer::LogUpGeneric {
                numerators,
                denominators,
            }
            | Layer::LogUpMultiplicities {
                numerators,
                denominators,
            } => Self::next_logup_layer(MleExpr::Mle(numerators), denominators),
            Layer::LogUpSingles { denominators } => {
                Self::next_logup_layer(MleExpr::Constant(F::ONE), denominators)
            }
        };
        Some(next_layer)
    }

    fn next_grand_product_layer(layer: &Mle<F>) -> Layer<F> {
        let res = layer
            .chunks_exact(2) // Process in chunks of 2 elements
            .map(|chunk| chunk[0] * chunk[1]) // Multiply each pair
            .collect();
        Layer::GrandProduct(Mle::new(res))
    }

    fn next_logup_layer(numerators: MleExpr<'_, F>, denominators: &Mle<F>) -> Layer<F> {
        let half_n = 1 << (denominators.arity() - 1);
        let mut next_numerators = Vec::with_capacity(half_n);
        let mut next_denominators = Vec::with_capacity(half_n);

        for i in 0..half_n {
            let a = Fraction::new(numerators[i * 2], denominators[i * 2]);
            let b = Fraction::new(numerators[i * 2 + 1], denominators[i * 2 + 1]);
            let res = a + b;
            next_numerators.push(res.numerator);
            next_denominators.push(res.denominator);
        }

        Layer::LogUpGeneric {
            numerators: Mle::new(next_numerators),
            denominators: Mle::new(next_denominators),
        }
    }

    /// Returns each column output if the layer is an output layer, otherwise returns an `Err`.
    pub fn try_into_output_layer_values(self) -> Result<Vec<F>, NotOutputLayerError> {
        if !self.is_output_layer() {
            return Err(NotOutputLayerError);
        }

        Ok(match self {
            Layer::LogUpSingles { denominators } => {
                let numerator = F::ONE;
                let denominator = denominators[0];
                vec![numerator, denominator]
            }
            Layer::LogUpGeneric {
                numerators,
                denominators,
            }
            | Layer::LogUpMultiplicities {
                numerators,
                denominators,
            } => {
                let numerator = numerators[0];
                let denominator = denominators[0];
                vec![numerator, denominator]
            }
            Layer::GrandProduct(col) => {
                vec![col[0]]
            }
        })
    }

    /// Returns a transformed layer with the first variable of each column fixed to `assignment`.
    pub fn fix_first_variable(self, x0: F) -> Self {
        if self.n_variables() == 0 {
            return self;
        }

        match self {
            Self::GrandProduct(mle) => Self::GrandProduct(mle.partial_evaluation(x0)),
            Self::LogUpGeneric {
                numerators,
                denominators,
            }
            | Self::LogUpMultiplicities {
                numerators,
                denominators,
            } => Self::LogUpGeneric {
                numerators: numerators.partial_evaluation(x0),
                denominators: denominators.partial_evaluation(x0),
            },
            Self::LogUpSingles { denominators } => Self::LogUpSingles {
                denominators: denominators.partial_evaluation(x0),
            },
        }
    }
}

#[derive(Debug)]
pub struct NotOutputLayerError;

enum MleExpr<'a, F: Field> {
    Constant(F),
    Mle(&'a Mle<F>),
}

impl<F: Field> Index<usize> for MleExpr<'_, F> {
    type Output = F;

    fn index(&self, index: usize) -> &F {
        match self {
            Self::Constant(v) => v,
            Self::Mle(mle) => &mle[index],
        }
    }
}
