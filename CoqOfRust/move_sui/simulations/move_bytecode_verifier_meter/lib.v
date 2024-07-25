Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

(* TODO(progress):
- Implement `Scope` since it's strongly related
- Write out the exact function chains from `verify_instr` 
  - Explain when will other verify functions use `verify_instr`
  - Examine further if `DummyMeter` can be safely replaced by `BoundMeter`
  - Carefully check where does `DummyMeter` apply and what properties or functions are being accessed
- Restructure the `Meter` module(not trait) as in note below
*)

(* NOTE: DRAFT: We can restructure the `Meter` into a large module, since its content are pretty few.
Currently we implement the structs separately, but the plan is:

Module Meter
  - Module BoundMeter
  - Module DummyMeter
*)

(* NOTE: 
  - We ignore `f32` since related parameters are mostly factors to be multiplied with.
    These parameters will be either ignored or treated as a sole `1`. *)

(* use crate::{Meter, Scope}; *)
(* pub struct DummyMeter; *)
Module DummyMeter.
  Record t : Set := { }.

  (* impl Meter for DummyMeter  *)
  Module Impl_move_sui_simulations_move_bytecode_verifier_meter_DummyMeter.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier_meter.DummyMeter.t.

    (* fn enter_scope(&mut self, _name: &str, _scope: Scope) {} *)
    Definition enter_scope (self : Self) (_name : str) (_scope : Scope) : unit := tt.

    (* fn transfer(&mut self, _from: Scope, _to: Scope, _factor: f32) -> PartialVMResult<()> { Ok(()) } *)
    Definition transfer (self : Self) (_from : Scope) (_to : Scope) (_factor : Z) : PartialVMResult.t unit := return?? tt.

    (* fn add(&mut self, _scope: Scope, _units: u128) -> PartialVMResult<()> { Ok(()) } *)
    Definition add (self : Self) (_scope : Scope) (_units : Z) : PartialVMResult.t unit := return?? tt.
  End Impl_move_sui_simulations_move_bytecode_verifier_meter_DummyMeter.
End DummyMeter.

(* bound.rs
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{Meter, Scope};
use move_binary_format::errors::{PartialVMError, PartialVMResult};
use move_core_types::vm_status::StatusCode;
use move_vm_config::verifier::MeterConfig;

/// Module and function level metering.

impl Bounds {
    fn add(&mut self, units: u128) -> PartialVMResult<()> {
        if let Some(max) = self.max {
            let new_units = self.units.saturating_add(units);
            if new_units > max {
                // TODO: change to a new status PROGRAM_TOO_COMPLEX once this is rolled out. For
                // now we use an existing code to avoid breaking changes on potential rollback.
                return Err(PartialVMError::new(StatusCode::CONSTRAINT_NOT_SATISFIED)
                    .with_message(format!(
                        "program too complex (in `{}` with `{} current + {} new > {} max`)",
                        self.name, self.units, units, max
                    )));
            }
            self.units = new_units;
        }
        Ok(())
    }
}

impl BoundMeter {
    pub fn new(config: MeterConfig) -> Self {
        Self {
            pkg_bounds: Bounds {
                name: "<unknown>".to_string(),
                units: 0,
                max: config.max_per_pkg_meter_units,
            },
            mod_bounds: Bounds {
                name: "<unknown>".to_string(),
                units: 0,
                max: config.max_per_mod_meter_units,
            },
            fun_bounds: Bounds {
                name: "<unknown>".to_string(),
                units: 0,
                max: config.max_per_fun_meter_units,
            },
        }
    }

    fn get_bounds_mut(&mut self, scope: Scope) -> &mut Bounds {
        match scope {
            Scope::Package => &mut self.pkg_bounds,
            Scope::Module => &mut self.mod_bounds,
            Scope::Function => &mut self.fun_bounds,
            Scope::Transaction => panic!("transaction scope unsupported."),
        }
    }

    fn get_bounds(&self, scope: Scope) -> &Bounds {
        match scope {
            Scope::Package => &self.pkg_bounds,
            Scope::Module => &self.mod_bounds,
            Scope::Function => &self.fun_bounds,
            Scope::Transaction => panic!("transaction scope unsupported."),
        }
    }

    pub fn get_usage(&self, scope: Scope) -> u128 {
        self.get_bounds(scope).units
    }

    pub fn get_limit(&self, scope: Scope) -> Option<u128> {
        self.get_bounds(scope).max
    }
}
*)
(* 
struct Bounds {
    name: String,
    units: u128,
    max: Option<u128>,
}
*)
Module Bounds.
  Record t : Set := {
    name : string;
    units : Z;
    max : option Z;
  }.
End Bounds.

(* 
pub struct BoundMeter {
    pkg_bounds: Bounds,
    mod_bounds: Bounds,
    fun_bounds: Bounds,
}
*)
Module BoundMeter.
  Record t : Set := {
    pkg_bounds : Bounds.t;
    mod_bounds : Bounds.t;
    fun_bounds : Bounds.t;
  }
  (* 
  impl Meter for BoundMeter {
  }
  *)
  Module Impl_move_sui_simulations_move_bytecode_verifier_meter_BoundMeter.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier_meter.BoundMeter.t.

    (* 
    fn get_bounds_mut(&mut self, scope: Scope) -> &mut Bounds {
        match scope {
            Scope::Package => &mut self.pkg_bounds,
            Scope::Module => &mut self.mod_bounds,
            Scope::Function => &mut self.fun_bounds,
            Scope::Transaction => panic!("transaction scope unsupported."),
        }
    }
    *)
    Definition get_bounds_mut (self : Self) (scope : Scope) : Bounds.t. Admitted.

    (* 
    fn enter_scope(&mut self, name: &str, scope: Scope) {
        let bounds = self.get_bounds_mut(scope);
        bounds.name = name.into();
        bounds.units = 0;
    }
    *)
    Definition enter_scope (self : Self) (name : str) (scope : Scope) : unit. Admitted.

    (* 
    fn transfer(&mut self, from: Scope, to: Scope, factor: f32) -> PartialVMResult<()> {
        let units = (self.get_bounds_mut(from).units as f32 * factor) as u128;
        self.add(to, units)
    }
    *)
    Definition transfer (self : Self) (from : Scope) (to : Scope) (factor : Z) : PartialVMResult.t unit. Admitted.

    (* 
    fn add(&mut self, scope: Scope, units: u128) -> PartialVMResult<()> {
        self.get_bounds_mut(scope).add(units)
    }
    *)
    Definition add (self : Self) (scope : Scope) (units : Z) : PartialVMResult.t unit. Admitted.
    
  End Impl_move_sui_simulations_move_bytecode_verifier_meter_BoundMeter.

  Module Dummy.
    (* TODO: IMPORTANT: move the `DummyMeter` struct along with its impls into this module *)
  End Dummy.

End BoundMeter.

(* TODO: Implement `Meter` trait as Coq Class *)
(* 
pub trait Meter {
    /// Indicates the begin of a new scope.
    fn enter_scope(&mut self, name: &str, scope: Scope);

    /// Transfer the amount of metering from once scope to the next. If the current scope has
    /// metered N units, the target scope will be charged with N*factor.
    fn transfer(&mut self, from: Scope, to: Scope, factor: f32) -> PartialVMResult<()>;

    /// Add the number of units to the meter, returns an error if a limit is hit.
    fn add(&mut self, scope: Scope, units: u128) -> PartialVMResult<()>;

    /// Adds the number of items.
    fn add_items(
        &mut self,
        scope: Scope,
        units_per_item: u128,
        items: usize,
    ) -> PartialVMResult<()> {
        if items == 0 {
            return Ok(());
        }
        self.add(scope, units_per_item.saturating_mul(items as u128))
    }

    /// Adds the number of items with growth factor
    fn add_items_with_growth(
        &mut self,
        scope: Scope,
        mut units_per_item: u128,
        items: usize,
        growth_factor: f32,
    ) -> PartialVMResult<()> {
        if items == 0 {
            return Ok(());
        }
        for _ in 0..items {
            self.add(scope, units_per_item)?;
            units_per_item = growth_factor.mul(units_per_item as f32) as u128;
        }
        Ok(())
    }
}
*)
Module Meter.
  Class Trait (Self : Set) : Set := { }.
End Meter.
