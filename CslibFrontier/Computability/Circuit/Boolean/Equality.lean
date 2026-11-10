/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Tactic.Ring

/-!
# Equality of selected Boolean inputs

The formula compares two sequences of selected inputs. Selectors may overlap or repeat;
empty sequences compare equal. An XNOR for each coordinate is conjoined with the remainder,
using six gates per coordinate and a single true constant.

## Main definitions

* `Cslib.Circuits.Formula.equalBits`: equality of two selected input sequences.
* `Cslib.Circuits.Boolean.adjacentEqualityCircuit`: shared tests for consecutive selected keys.

## Main results

* `Cslib.Circuits.Formula.eval_equalBits_iff`: equality of the selected functions.
* `Cslib.Circuits.Formula.cost_equalBits`: exact arbitrary weighted cost.
* `Cslib.Circuits.Formula.size_equalBits`: exact gate count, including the constant.
* `Cslib.Circuits.Boolean.eval_adjacentEqualityCircuit_iff`: exact incoming-link semantics.
* `Cslib.Circuits.Boolean.cost_program_adjacentEqualityCircuit`: weighted adjacent-test cost.

## References

* Adapts the equality formulas in MassProduction/Routing.lean from
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Formula

open Boolean

/-- Test equality of two selected input sequences, including empty and repeated selections. -/
def equalBits {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Fin k → Fin n) → Formula signature n
  | 0, _, _ => Formula.const true
  | _ + 1, left, right =>
    let a := Formula.input (left 0)
    let b := Formula.input (right 0)
    ((a.and b).or (a.not.and b.not)).and (equalBits (left ∘ Fin.succ) (right ∘ Fin.succ))

/-- Selected-bit equality is equality of the two selected functions. -/
@[simp] theorem eval_equalBits_iff {n k : ℕ} (left right : Fin k → Fin n) (x : BitString n) :
    (equalBits left right).eval interpretation x = true ↔ x ∘ left = x ∘ right := by
  induction k with
  | zero => simp [equalBits, Subsingleton.elim (x ∘ left) (x ∘ right)]
  | succ k ih =>
    simp only [equalBits, Formula.eval_and, Formula.eval_or, Formula.eval_not, Formula.eval_input,
      Bool.and_eq_true, ih]
    have head : (x (left 0) && x (right 0) || !x (left 0) && !x (right 0)) = true ↔
        x (left 0) = x (right 0) := by
      cases x (left 0) <;> cases x (right 0) <;> simp
    rw [head]
    constructor
    · rintro ⟨hzero, htail⟩
      funext i
      exact Fin.cases hzero (fun j => congrFun htail j) i
    · intro h
      exact ⟨congrFun h 0, funext fun j => congrFun h j.succ⟩

/-- Each coordinate uses three AND gates, two negations and one OR, after one true constant. -/
theorem cost_equalBits {n k : ℕ} (left right : Fin k → Fin n) (cost : signature.Op → ℕ) :
    (equalBits left right).cost cost =
      cost (.const true) + k * (3 * cost .and + 2 * cost .not + cost .or) := by
  induction k with
  | zero => simp [equalBits, Formula.const]
  | succ k ih =>
    simp only [equalBits, Formula.and, Formula.or, Formula.not, Formula.cost_gate,
      Formula.cost_input, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, ih]
    ring

/-- The formula has six gates per selected coordinate and one constant gate. -/
@[simp] theorem size_equalBits {n k : ℕ} (left right : Fin k → Fin n) :
    (equalBits left right).size = 6 * k + 1 := by
  have h := cost_equalBits left right (fun _ => 1)
  simpa [Formula.cost_one, Nat.mul_comm, Nat.add_comm] using h

end Cslib.Circuits.Formula


namespace Cslib.Circuits.Boolean

/-- Compare each selected key with its predecessor; the first key has no incoming link. -/
def adjacentEqualityCircuit {input count keyWidth : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) : Circuit signature input count :=
  Circuit.pi fun record => if h : 0 < record.val then
    (Formula.equalBits (key ⟨record.val - 1, by lia⟩) (key record)).toCircuit
  else (Formula.const false).toCircuit

/-- An incoming link is true precisely when the predecessor exists and has the same key. -/
theorem eval_adjacentEqualityCircuit_iff {input count keyWidth : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) (x : BitString input) (record : Fin count) :
    (adjacentEqualityCircuit key).eval interpretation x record = true ↔
      ∃ positive : 0 < record.val, x ∘ key ⟨record.val - 1, by lia⟩ = x ∘ key record := by
  by_cases h : 0 < record.val <;> simp [adjacentEqualityCircuit, h]

/-- Adjacent comparisons are computed once, with one false constant for the missing first link. -/
theorem cost_program_adjacentEqualityCircuit {input count keyWidth : ℕ}
    (key : Fin count → Fin keyWidth → Fin input) (cost : signature.Op → ℕ) :
    (adjacentEqualityCircuit key).program.cost cost = if count = 0 then 0 else
      cost (.const false) + (count - 1) *
        (cost (.const true) + keyWidth * (3 * cost .and + 2 * cost .not + cost .or)) := by
  cases count with
  | zero => simp [adjacentEqualityCircuit, Circuit.cost_program_pi]
  | succ count =>
    simp [adjacentEqualityCircuit, Circuit.cost_program_pi, Fin.sum_univ_succ,
      Formula.cost_toCircuit, Formula.cost_equalBits, Formula.const, Nat.add_comm]

end Cslib.Circuits.Boolean
