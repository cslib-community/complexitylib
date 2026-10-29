/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Computability.Circuit.Boolean.Unbounded

/-!
# Restrictions in the unbounded fan-in basis

A restriction (partial assignment) `ρ` of the inputs is computed in the unbounded fan-in basis by
the De Morgan substitution circuit of `ρ.toSubstitution`
(`Cslib.Circuits.Boolean.substituteCircuit`,
`Cslib.BitString.PartialAssignment.substitute_toSubstitution`), its two constants becoming the
conjunction and the disjunction of nothing (`Cslib.Circuits.Boolean.Unbounded.deMorganToUnbounded`).
Composing a circuit `C` with it computes the restriction `C ∘ ρ.fill`.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.restrictCircuit`: the circuit outputting `ρ.fill x`.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_restrictCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.size_restrictCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_restrictCircuit_le`,
  `Cslib.Circuits.Boolean.Unbounded.fanInAtMost_restrictCircuit`: it computes `ρ.fill` with two
  gates, depth at most one and fan-in at most two.
-/

public section

namespace Cslib.Circuits.Boolean.Unbounded

open BitString

variable {n : ℕ}

/-- The circuit that outputs its inputs restricted by `ρ`: the bits fixed by `ρ` replaced by their
values (`eval_restrictCircuit`). It is the De Morgan substitution circuit of `ρ.toSubstitution`, in
the unbounded fan-in basis. -/
def restrictCircuit (ρ : PartialAssignment (Fin n)) : Circuit signature n n :=
  (substituteCircuit ρ.toSubstitution).mapOp deMorganToUnbounded

/-- `restrictCircuit ρ` computes `ρ.fill`. -/
@[simp] theorem eval_restrictCircuit (ρ : PartialAssignment (Fin n)) (x : BitString n) :
    (restrictCircuit ρ).eval interpretation x = ρ.fill x := by
  rw [restrictCircuit, Circuit.eval_mapOp (I := Boolean.interpretation), eval_substituteCircuit,
    PartialAssignment.substitute_toSubstitution]

/-- `restrictCircuit ρ` has two gates, one for each constant. -/
@[simp] theorem size_restrictCircuit (ρ : PartialAssignment (Fin n)) :
    (restrictCircuit ρ).size = 2 := by
  rw [restrictCircuit, Circuit.size_mapOp, size_substituteCircuit]

/-- `restrictCircuit ρ` has depth at most one. -/
theorem depth_restrictCircuit_le (ρ : PartialAssignment (Fin n)) :
    (restrictCircuit ρ).depth ≤ 1 := by
  rw [restrictCircuit, Circuit.depth_mapOp]
  exact depth_substituteCircuit_le _

/-- `restrictCircuit ρ` has fan-in at most two. -/
theorem fanInAtMost_restrictCircuit (ρ : PartialAssignment (Fin n)) :
    (restrictCircuit ρ).FanInAtMost 2 :=
  (Circuit.fanInAtMost_mapOp _ _).2 (Circuit.fanInAtMost_two _)

end Cslib.Circuits.Boolean.Unbounded
