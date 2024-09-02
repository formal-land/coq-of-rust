Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* NOTE: 
- We can restructure the `Meter` into a large module, since its content are pretty few.
  Currently we implement the structs as the following tree:
  Module Meter
  | - Module BoundMeter
  | - Module DummyMeter
- We ignore `f32` since related parameters are mostly factors to be multiplied with.
  These parameters will be either ignored or treated as a sole Z value.
*)

(* Saturating mul & add support specifically for u128 *)
Definition u128_MAX := 340282366920938463463374607431768211455.

Definition saturating_mul (a b : Z) :=
  let result := Z.mul a b in
  if result >? u128_MAX
  then u128_MAX else result.

Definition saturating_add (a b : Z) :=
  let result := Z.add a b in
  if result >? u128_MAX
  then u128_MAX else result.

(* 
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scope {
    // Metering is for transaction level
    Transaction,
    // Metering is for package level
    Package,
    // Metering is for module level
    Module,
    // Metering is for function level
    Function,
}
*)
Module Scope.
  Inductive t :=
  | Transaction
  | Package
  | Module
  | Function
  .
End Scope.

(* bound.rs
use move_vm_config::verifier::MeterConfig;
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

  
  Definition State := t.

  Module Impl_Bounds.
    Definition Self := move_sui.simulations.move_bytecode_verifier_meter.lib.Bounds.t.

    (* 
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
    *)

    Definition add (units : Z) : MS? State string (PartialVMResult.t unit) :=
      letS? self := readS? in
      match self.(max) with
      | Some max => 
      (* TODO: IMPORTANT: replace the normal `+` below to actual bounded add
        https://doc.rust-lang.org/std/primitive.u128.html#method.saturating_add *)
        let self_units := self.(Bounds.units) in
        let new_units := saturating_add self_units self_units in
        if new_units >? max 
        then 
          returnS? $ Result.Err $ PartialVMError
            .Impl_PartialVMError
            .new StatusCode.CONSTRAINT_NOT_SATISFIED
        else 
          let self := self <| Bounds.units := units |> in
          letS? _ := writeS? self in
          returnS? $ Result.Ok tt
      | None => 
          returnS? $ Result.Ok tt
      end.
  End Impl_Bounds.
End Bounds.

(* 
pub trait Meter {
    /// Indicates the begin of a new scope.
    fn enter_scope(&mut self, name: &str, scope: Scope.t);

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

  Module DummyMeter.
    Record t : Set := { }.

    (* impl Meter for DummyMeter  *)
    Module Impl_DummyMeter.
      Definition Self := t.

      (* fn enter_scope(&mut self, _name: &str, _scope: Scope.t) {} *)
      Definition enter_scope (self : Self) (_name : string) (_scope : Scope.t) : unit := tt.

      (* fn transfer(&mut self, _from: Scope, _to: Scope, _factor: f32) -> PartialVMResult<()> { Ok(()) } *)
      Definition transfer (self : Self) (_from : Scope.t) (_to : Scope.t) (_factor : Z) : PartialVMResult.t unit := return?? tt.

      (* fn add(&mut self, _scope: Scope, _units: u128) -> PartialVMResult<()> { Ok(()) } *)
      Definition add (self : Self) (_scope : Scope.t) (_units : Z) : PartialVMResult.t unit := return?? tt.
    End Impl_DummyMeter.
  End DummyMeter.

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
    }.

    Definition State := t.

    (* 
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

        fn get_bounds(&self, scope: Scope.t) -> &Bounds {
            match scope {
                Scope::Package => &self.pkg_bounds,
                Scope::Module => &self.mod_bounds,
                Scope::Function => &self.fun_bounds,
                Scope::Transaction => panic!("transaction scope unsupported."),
            }
        }

        pub fn get_usage(&self, scope: Scope.t) -> u128 {
            self.get_bounds(scope).units
        }

        pub fn get_limit(&self, scope: Scope.t) -> Option<u128> {
            self.get_bounds(scope).max
        }
    }
    *)
    Module Impl_BoundMeter.
      Definition Self := move_sui.simulations.move_bytecode_verifier_meter.lib.Meter.BoundMeter.t.

      (* 
      fn get_bounds_mut(&mut self, scope: Scope.t) -> &mut Bounds {
          match scope {
              Scope::Package => &mut self.pkg_bounds,
              Scope::Module => &mut self.mod_bounds,
              Scope::Function => &mut self.fun_bounds,
              Scope::Transaction => panic!("transaction scope unsupported."),
          }
      }
      *)
      Definition get_bounds_mut (scope : Scope.t) :
        LensPanic.t string State Bounds.State := {|
          LensPanic.read boundmeter := 
            match scope with
            | Scope.Package     => return!? (boundmeter.(pkg_bounds))
            | Scope.Module      => return!? (boundmeter.(mod_bounds))
            | Scope.Function    => return!? (boundmeter.(fun_bounds))
            | Scope.Transaction => panic!? "transaction scope unsupported."
            end;
          LensPanic.write boundmeter bounds := 
            match scope with
            | Scope.Package     => return!? (boundmeter <| pkg_bounds := bounds |>)
            | Scope.Module      => return!? (boundmeter <| mod_bounds := bounds |>)
            | Scope.Function    => return!? (boundmeter <| fun_bounds := bounds |>)
            | Scope.Transaction => panic!? "transaction scope unsupported."
            end;
        |}.
 
      (* 
      fn enter_scope(&mut self, name: &str, scope: Scope.t) {
          let bounds = self.get_bounds_mut(scope);
          bounds.name = name.into();
          bounds.units = 0;
      }
      *)
      Definition enter_scope (name : string) (scope : Scope.t) : MS? State string unit :=
        liftS?of!? (get_bounds_mut scope) (
          letS? bounds := readS? in
          let   bounds := bounds <| Bounds.name  := name |> in
          let   bounds := bounds <| Bounds.units := 0    |> in
          letS? _ := writeS? bounds in
          returnS? tt
        ).

      (* 
      fn add(&mut self, scope: Scope, units: u128) -> PartialVMResult<()> {
          self.get_bounds_mut(scope).add(units)
      }
      *)
      Definition add (scope : Scope.t) (units : Z) 
        : MS? State string (PartialVMResult.t unit) :=
        liftS?of!? (get_bounds_mut scope) (
          letS? bounds := readS? in
          Bounds.Impl_Bounds.add 
            units
        ).

      (* 
      fn transfer(&mut self, from: Scope, to: Scope, factor: f32) -> PartialVMResult<()> {
          let units = (self.get_bounds_mut(from).units as f32 * factor) as u128;
          self.add(to, units)
      }
      *)
      Definition transfer (from : Scope.t) (to : Scope.t) (factor : Z) 
        : MS? State string (PartialVMResult.t unit) :=
        letS? bounds := liftS?of!? (get_bounds_mut from) (readS?) in 
        letS? self := readS? in
        let units := Z.mul bounds.(Bounds.units) factor in
        add to units
        .

      (* 
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
      *)
      Definition add_items (scope : Scope.t) (units_per_item items : Z) 
        : MS? State string (PartialVMResult.t unit) :=
        if items =? 0
        then returnS? $ Result.Ok tt
        else letS? self := readS? in
        add scope $ saturating_mul units_per_item items.
      
    End Impl_BoundMeter.
  End BoundMeter.
End Meter.
