use openvm_circuit_primitives::{
    assert_less_than::{AssertLessThanIo, AssertLtSubAir},
    is_zero::{IsZeroIo, IsZeroSubAir},
    utils::not,
    var_range::VariableRangeCheckerBus,
    SubAir,
};
use openvm_stark_backend::{
    interaction::InteractionBuilder, p3_air::AirBuilder, p3_field::FieldAlgebra,
};

use super::bus::MemoryBus;
use crate::system::memory::{
    offline_checker::columns::{
        MemoryBaseAuxCols, MemoryReadAuxCols, MemoryReadOrImmediateAuxCols, MemoryWriteAuxCols,
    },
    MemoryAddress,
};

/// AUX_LEN is the number of auxiliary columns (aka the number of limbs that the input numbers will
/// be decomposed into) for the `AssertLtSubAir` in the `MemoryOfflineChecker`.
/// Warning: This requires that (clk_max_bits + decomp - 1) / decomp = AUX_LEN
///         in MemoryOfflineChecker (or whenever AssertLtSubAir is used)
pub(crate) const AUX_LEN: usize = 2;

/// The [MemoryBridge] is used within AIR evaluation functions to constrain logical memory
/// operations (read/write). It adds all necessary constraints and interactions.
#[derive(Clone, Copy, Debug)]
pub struct MemoryBridge {
    offline_checker: MemoryOfflineChecker,
}

impl MemoryBridge {
    /// Create a new [MemoryBridge] with the provided offline_checker.
    pub fn new(
        memory_bus: MemoryBus,
        clk_max_bits: usize,
        range_bus: VariableRangeCheckerBus,
    ) -> Self {
        Self {
            offline_checker: MemoryOfflineChecker::new(memory_bus, clk_max_bits, range_bus),
        }
    }

    /// Prepare a logical memory read operation.
    #[must_use]
    pub fn read<'a, T, V, const N: usize>(
        &self,
        address: MemoryAddress<impl Into<T>, impl Into<T>>,
        data: [impl Into<T>; N],
        timestamp: impl Into<T>,
        aux: &'a MemoryReadAuxCols<V>,
    ) -> MemoryReadOperation<'a, T, V, N> {
        MemoryReadOperation {
            offline_checker: self.offline_checker,
            address: MemoryAddress::from(address),
            data: data.map(Into::into),
            timestamp: timestamp.into(),
            aux,
        }
    }

    /// Prepare a logical memory read or immediate operation.
    #[must_use]
    pub fn read_or_immediate<'a, T, V>(
        &self,
        address: MemoryAddress<impl Into<T>, impl Into<T>>,
        data: impl Into<T>,
        timestamp: impl Into<T>,
        aux: &'a MemoryReadOrImmediateAuxCols<V>,
    ) -> MemoryReadOrImmediateOperation<'a, T, V> {
        MemoryReadOrImmediateOperation {
            offline_checker: self.offline_checker,
            address: MemoryAddress::from(address),
            data: data.into(),
            timestamp: timestamp.into(),
            aux,
        }
    }

    /// Prepare a logical memory write operation.
    #[must_use]
    pub fn write<'a, T, V, const N: usize>(
        &self,
        address: MemoryAddress<impl Into<T>, impl Into<T>>,
        data: [impl Into<T>; N],
        timestamp: impl Into<T>,
        aux: &'a MemoryWriteAuxCols<V, N>,
    ) -> MemoryWriteOperation<'a, T, V, N> {
        MemoryWriteOperation {
            offline_checker: self.offline_checker,
            address: MemoryAddress::from(address),
            data: data.map(Into::into),
            timestamp: timestamp.into(),
            aux,
        }
    }
}

/// Constraints and interactions for a logical memory read of `(address, data)` at time `timestamp`.
/// This reads `(address, data, timestamp_prev)` from the memory bus and writes
/// `(address, data, timestamp)` to the memory bus.
/// Includes constraints for `timestamp_prev < timestamp`.
///
/// The generic `T` type is intended to be `AB::Expr` where `AB` is the [AirBuilder].
/// The auxiliary columns are not expected to be expressions, so the generic `V` type is intended
/// to be `AB::Var`.
pub struct MemoryReadOperation<'a, T, V, const N: usize> {
    offline_checker: MemoryOfflineChecker,
    address: MemoryAddress<T, T>,
    data: [T; N],
    timestamp: T,
    aux: &'a MemoryReadAuxCols<V>,
}

/// The max degree of constraints is:
/// eval_timestamps: deg(enabled) + max(1, deg(self.timestamp))
/// eval_bulk_access: refer to private function MemoryOfflineChecker::eval_bulk_access
impl<F: FieldAlgebra, V: Copy + Into<F>, const N: usize> MemoryReadOperation<'_, F, V, N> {
    /// Evaluate constraints and send/receive interactions.
    pub fn eval<AB>(self, builder: &mut AB, enabled: impl Into<AB::Expr>)
    where
        AB: InteractionBuilder<Var = V, Expr = F>,
    {
        let enabled = enabled.into();

        // NOTE: We do not need to constrain `address_space != 0` since this is done implicitly by
        // the memory interactions argument together with initial/final memory chips.

        self.offline_checker.eval_timestamps(
            builder,
            self.timestamp.clone(),
            &self.aux.base,
            enabled.clone(),
        );

        self.offline_checker.eval_bulk_access(
            builder,
            self.address,
            &self.data,
            &self.data,
            self.timestamp.clone(),
            self.aux.base.prev_timestamp,
            enabled,
        );
    }
}

/// Constraints and interactions for a logical memory read of `(address, data)` at time `timestamp`,
/// supporting `address.address_space = 0` for immediates.
///
/// If `address.address_space` is non-zero, it behaves like `MemoryReadOperation`. Otherwise,
/// it constrains the immediate value appropriately.
///
/// The generic `T` type is intended to be `AB::Expr` where `AB` is the [AirBuilder].
/// The auxiliary columns are not expected to be expressions, so the generic `V` type is intended
/// to be `AB::Var`.
pub struct MemoryReadOrImmediateOperation<'a, T, V> {
    offline_checker: MemoryOfflineChecker,
    address: MemoryAddress<T, T>,
    data: T,
    timestamp: T,
    aux: &'a MemoryReadOrImmediateAuxCols<V>,
}

/// The max degree of constraints is:
/// IsZeroSubAir.subair_eval:
///         deg(enabled) + max(deg(address.address_space) + deg(aux.is_immediate),
///                           deg(address.address_space) + deg(aux.is_zero_aux))
/// is_immediate check: deg(aux.is_immediate) + max(deg(data), deg(address.pointer))
/// eval_timestamps: deg(enabled) + max(1, deg(self.timestamp))
/// eval_bulk_access: refer to private function MemoryOfflineChecker::eval_bulk_access
impl<F: FieldAlgebra, V: Copy + Into<F>> MemoryReadOrImmediateOperation<'_, F, V> {
    /// Evaluate constraints and send/receive interactions.
    pub fn eval<AB>(self, builder: &mut AB, enabled: impl Into<AB::Expr>)
    where
        AB: InteractionBuilder<Var = V, Expr = F>,
    {
        let enabled = enabled.into();

        // `is_immediate` should be an indicator for `address_space == 0` (when `enabled`).
        {
            let is_zero_io = IsZeroIo::new(
                self.address.address_space.clone(),
                self.aux.is_immediate.into(),
                enabled.clone(),
            );
            IsZeroSubAir.eval(builder, (is_zero_io, self.aux.is_zero_aux));
        }
        // When `is_immediate`, the data should be the pointer value.
        builder
            .when(self.aux.is_immediate)
            .assert_eq(self.data.clone(), self.address.pointer.clone());

        // Timestamps should be increasing (when enabled).
        self.offline_checker.eval_timestamps(
            builder,
            self.timestamp.clone(),
            &self.aux.base,
            enabled.clone(),
        );

        self.offline_checker.eval_bulk_access(
            builder,
            self.address,
            &[self.data.clone()],
            &[self.data],
            self.timestamp,
            self.aux.base.prev_timestamp,
            enabled * not(self.aux.is_immediate),
        );
    }
}

/// Constraints and interactions for a logical memory write of `(address, data)` at time
/// `timestamp`. This reads `(address, data_prev, timestamp_prev)` from the memory bus and writes
/// `(address, data, timestamp)` to the memory bus.
/// Includes constraints for `timestamp_prev < timestamp`.
///
/// **Note:** This can be used as a logical read operation by setting `data_prev = data`.
pub struct MemoryWriteOperation<'a, T, V, const N: usize> {
    offline_checker: MemoryOfflineChecker,
    address: MemoryAddress<T, T>,
    data: [T; N],
    /// The timestamp of the current read
    timestamp: T,
    aux: &'a MemoryWriteAuxCols<V, N>,
}

/// The max degree of constraints is:
/// eval_timestamps: deg(enabled) + max(1, deg(self.timestamp))
/// eval_bulk_access: refer to private function MemoryOfflineChecker::eval_bulk_access
impl<T: FieldAlgebra, V: Copy + Into<T>, const N: usize> MemoryWriteOperation<'_, T, V, N> {
    /// Evaluate constraints and send/receive interactions. `enabled` must be boolean.
    pub fn eval<AB>(self, builder: &mut AB, enabled: impl Into<AB::Expr>)
    where
        AB: InteractionBuilder<Var = V, Expr = T>,
    {
        let enabled = enabled.into();
        self.offline_checker.eval_timestamps(
            builder,
            self.timestamp.clone(),
            &self.aux.base,
            enabled.clone(),
        );

        self.offline_checker.eval_bulk_access(
            builder,
            self.address,
            &self.data,
            &self.aux.prev_data.map(Into::into),
            self.timestamp,
            self.aux.base.prev_timestamp,
            enabled,
        );
    }
}

#[derive(Clone, Copy, Debug)]
struct MemoryOfflineChecker {
    memory_bus: MemoryBus,
    timestamp_lt_air: AssertLtSubAir,
}

impl MemoryOfflineChecker {
    fn new(memory_bus: MemoryBus, clk_max_bits: usize, range_bus: VariableRangeCheckerBus) -> Self {
        Self {
            memory_bus,
            timestamp_lt_air: AssertLtSubAir::new(range_bus, clk_max_bits),
        }
    }

    /// The max degree of constraints is:
    /// deg(enabled) + max(1, deg(timestamp))
    /// Note: deg(prev_timestamp) = 1 since prev_timestamp is Var
    fn eval_timestamps<AB: InteractionBuilder>(
        &self,
        builder: &mut AB,
        timestamp: AB::Expr,
        base: &MemoryBaseAuxCols<AB::Var>,
        enabled: AB::Expr,
    ) {
        let lt_io = AssertLessThanIo::new(base.prev_timestamp, timestamp.clone(), enabled);
        self.timestamp_lt_air
            .eval(builder, (lt_io, &base.timestamp_lt_aux.lower_decomp));
    }

    /// At the core, eval_bulk_access is a bunch of push_sends and push_receives.
    /// The max constraint degree of expressions in sends/receives is:
    /// max(max_deg(data), max_deg(prev_data), max_deg(timestamp), max_deg(prev_timestamps))
    /// Also, each one of them has count with degree: deg(enabled)
    #[allow(clippy::too_many_arguments)]
    fn eval_bulk_access<AB, const N: usize>(
        &self,
        builder: &mut AB,
        address: MemoryAddress<AB::Expr, AB::Expr>,
        data: &[AB::Expr; N],
        prev_data: &[AB::Expr; N],
        timestamp: AB::Expr,
        prev_timestamp: AB::Var,
        enabled: AB::Expr,
    ) where
        AB: InteractionBuilder,
    {
        self.memory_bus
            .receive(address.clone(), prev_data.to_vec(), prev_timestamp)
            .eval(builder, enabled.clone());

        self.memory_bus
            .send(address, data.to_vec(), timestamp)
            .eval(builder, enabled);
    }
}
