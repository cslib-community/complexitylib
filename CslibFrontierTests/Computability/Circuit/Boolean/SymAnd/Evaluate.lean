/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Evaluate

/-!
# Tests for the `SYM ∘ AND` evaluation algorithm

Concrete instances of `CslibFrontier.Computability.Circuit.Boolean.SymAnd.Evaluate`:

* the AND count as a zeta transform on one input;
* the truth table of `x₀ ⊕ x₁` as a `SYM ∘ AND` circuit with three AND gates and a costed
  symmetric gate, computed by the kernel together with its exact tick count, and the Evaluation
  Lemma `truthTableM_spec` applied to it (the circuit takes both values, so the conclusion is not
  vacuous);
* the truth table of the three-input majority with three fan-in-one gates;
* edge cases: a circuit without AND gates, and an evaluator that is wrong above the circuit size,
  which `truthTableM_spec` allows.
-/

namespace ComplexityTests.Computability.Circuit.Boolean.SymAnd.Evaluate

open Cslib Cslib.BitString Cslib.Circuits.Boolean Cslib.Circuits.Boolean.SymAnd
  Cslib.Algorithms.Lean

/-! ### Parity of two bits -/

/-- The AND gates `x₀`, `x₀ ∧ x₁`, `x₁`. -/
def xorGates : List (Finset (Fin 2)) := [{0}, {0, 1}, {1}]

/-- `x₀ ⊕ x₁`: exactly one of the three AND gates is satisfied. -/
def xorCircuit : SymAnd (Fin 2) where
  gates := xorGates
  out j := j == 1

/-- The symmetric gate of `xorCircuit`, charged `3` ticks per value. -/
def xorOutM (j : ℕ) : TimeM ℕ Bool := do ✓[3] pure (j == 1)

/-- At `x = (1, 1)` all three AND gates are satisfied: `∑_{S ⊆ {0, 1}} f S = 1 + 1 + 1`. -/
example : xorCircuit.count (fun i => decide (i ∈ ({0, 1} : Finset (Fin 2)))) = 3 := by
  rw [count_eq_subsetZeta]
  decide +kernel

/-- The truth table, in the order `00, 10, 01, 11` (coordinate `0` first). -/
example : (truthTableM xorGates xorOutM).ret = #v[false, true, true, false] := by decide +kernel

/-- The exact cost `13 + 8 + 16 + 4`: multiplicities, two passes, the gate table, the lookups. -/
example : (truthTableM xorGates xorOutM).time = 41 := by decide +kernel

theorem time_xorOutM (j : ℕ) : (xorOutM j).time = 3 := rfl

/-- ... as `time_truthTableM` computes it. -/
example : (truthTableM xorGates xorOutM).time = (2 + 2) * 2 ^ 2 + (2 + 2) * 3 + 1 + 4 * 3 := by
  simp only [time_truthTableM, time_xorOutM, Finset.sum_const, Finset.card_range, smul_eq_mul,
    xorGates, List.length_cons, List.length_nil]

/-- **The Evaluation Lemma, applied.** The truth table of `xorCircuit` within
`4 * (4 + 4 * 4) = 80` ticks. -/
theorem xor_spec :
    (truthTableM xorGates xorOutM).ret =
        Vector.ofFn (fun k => xorCircuit.eval ((BitString.equivFin 2).symm k)) ∧
      (truthTableM xorGates xorOutM).time ≤ (2 + 2) * (2 ^ 2 + (xorCircuit.size + 1) * (3 + 1)) :=
  truthTableM_spec xorCircuit xorGates rfl xorOutM (fun _ _ => rfl)
    (fun j _ => (time_xorOutM j).le)

/-- Non-vacuity: the circuit takes both values. -/
example : xorCircuit.eval ![true, false] = true ∧ xorCircuit.eval ![true, true] = false := by
  decide +kernel

/-! ### Majority of three bits -/

/-- Three fan-in-one gates below the threshold `≥ 2`. -/
def majGates : List (Finset (Fin 3)) := [{0}, {1}, {2}]

/-- Majority of three bits; cells in the order of `BitString.equivFin` (coordinate `0` first). -/
example : (truthTableM majGates fun j => do ✓ pure (decide (2 ≤ j))).ret =
    #v[false, false, false, true, false, true, true, true] := by decide +kernel

/-! ### Edge cases -/

/-- No AND gates: every count is `0`, so the table is constant `out 0`. -/
example : (truthTableM ([] : List (Finset (Fin 2))) fun j => pure (j == 0)).ret =
    #v[true, true, true, true] := by decide +kernel

/-- An evaluator agreeing with the symmetric gate only on `0, …, 3` (the circuit has `3` AND
gates) still yields the truth table. -/
example : (truthTableM xorGates fun j => pure (if j ≤ 3 then j == 1 else true)).ret =
    Vector.ofFn (fun k => xorCircuit.eval ((BitString.equivFin 2).symm k)) :=
  (truthTableM_spec xorCircuit xorGates rfl _ (T := 0)
    (fun j hj => by
      have : j ≤ 3 := hj
      simp only [TimeM.ret_pure, this, ite_true]
      rfl)
    (fun _ _ => le_rfl)).1

end ComplexityTests.Computability.Circuit.Boolean.SymAnd.Evaluate
