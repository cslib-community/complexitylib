/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Basic
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Wiring with structured coordinates

Explicit equivalences number the input and output coordinates. A selector between those
coordinates lowers to ordinary circuit wiring, with no gates. Selectors need not be injective:
several outputs can reuse one input. Standard finite sums and products supply executable
layouts without choosing arbitrary enumerations.

## Main definitions

* `Cslib.Circuits.Circuit.wiringOn`: wiring between explicitly numbered coordinate types.

## Main results

* `Cslib.Circuits.Circuit.eval_wiringOn`: evaluation through the explicit coordinate numberings.
* `Cslib.Circuits.Circuit.cost_program_wiringOn`: structural wiring has zero weighted cost.
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {ι κ U : Type*} {n m : ℕ}

/-- Lower a coordinate selector through explicit input and output numberings. -/
def wiringOn (σ : Signature) (input : ι ≃ Fin n) (output : κ ≃ Fin m)
    (select : κ → ι) : Circuit σ n m :=
  wiring σ (input ∘ select ∘ output.symm)

/-- Each output reads the input selected in the structured coordinates. -/
@[simp] theorem eval_wiringOn (input : ι ≃ Fin n) (output : κ ≃ Fin m)
    (select : κ → ι) (I : Interpretation σ U) (x : Fin n → U) :
    (wiringOn σ input output select).eval I x = x ∘ input ∘ select ∘ output.symm := rfl

/-- Coordinate changes and fan-out introduce no weighted gate cost. -/
theorem cost_program_wiringOn (input : ι ≃ Fin n) (output : κ ≃ Fin m)
    (select : κ → ι) (cost : σ.Op → ℕ) :
    (wiringOn σ input output select).program.cost cost = 0 := rfl

/-- Structural wiring on numbered coordinates has zero gates. -/
@[simp] theorem size_wiringOn (input : ι ≃ Fin n) (output : κ ≃ Fin m)
    (select : κ → ι) : (wiringOn σ input output select).size = 0 := rfl

end Cslib.Circuits.Circuit
