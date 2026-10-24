/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Simulation

/-!
# Boolean gate cost with free constants

`nonconstantCost` charges NOT, AND and OR gates, while constants are free. This is the cost
convention used by the mass-production source; ordinary `Circuit.size` also charges constants.
The source's free identity gates are represented by native wiring.

## Main definitions

* `Cslib.Circuits.Boolean.nonconstantCost`: one for NOT, AND and OR, zero for constants.

## Main results

* `Cslib.Circuits.Program.cost_nonconstantCost_le`: this cost is at most the gate count.

## References

* Adapted from Basis/DeMorgan.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits

/-- Charge NOT, AND and OR once, and constants zero times. Designated outputs and wiring are
already free in the underlying circuit model. -/
def Boolean.nonconstantCost : Boolean.Op → ℕ
  | .const _ => 0
  | .not | .and | .or => 1

/-- Constant gates have `nonconstantCost` equal to `0`. -/
@[simp] theorem Boolean.nonconstantCost_const (b : Bool) : nonconstantCost (.const b) = 0 := rfl
/-- Negation gates have `nonconstantCost` equal to `1`. -/
@[simp] theorem Boolean.nonconstantCost_not : nonconstantCost .not = 1 := rfl
/-- Conjunction gates have `nonconstantCost` equal to `1`. -/
@[simp] theorem Boolean.nonconstantCost_and : nonconstantCost .and = 1 := rfl
/-- Disjunction gates have `nonconstantCost` equal to `1`. -/
@[simp] theorem Boolean.nonconstantCost_or : nonconstantCost .or = 1 := rfl

/-- Every De Morgan operation has `nonconstantCost` at most `1`. -/
theorem Boolean.nonconstantCost_le_one (op : Boolean.Op) : nonconstantCost op ≤ 1 := by
  cases op <;> simp

/-- Ignoring constant gates cannot increase the gate count. -/
theorem Program.cost_nonconstantCost_le {n g : ℕ} (p : Program Boolean.signature n g) :
    p.cost Boolean.nonconstantCost ≤ g := by
  simpa only [Program.cost_const, one_mul] using p.cost_mono Boolean.nonconstantCost_le_one

end Cslib.Circuits
