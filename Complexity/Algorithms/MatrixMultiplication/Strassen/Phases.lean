/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Strassen.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Partial Strassen accumulators for the native traversal proof

The seven operand forms and their output signs give a pointwise prefix invariant for the
explicit native stack. They are ordinary finite mathematics, not a supplied answer or run.
Every partialValue quadrant has at most four signed child contributions, including cancellation.
The definitions below serve internal execution proofs, rather than another matrix-product API.

The forms/signs are the same Strassen identities adapted in `Strassen.Defs`, from pinned
Spec/Sec3/Theorem17/Strassen.lean at revision 16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Strassen

/-- First actual mathematical operand of each of the seven native recursive children. -/
@[expose] def leftOperand (p k : ℕ) (a : ℕ → ℤ) : Fin 7 → ℕ → ℤ
  | 0 => quarter (4 ^ k * p) 0 a + quarter (4 ^ k * p) 3 a
  | 1 => quarter (4 ^ k * p) 2 a + quarter (4 ^ k * p) 3 a
  | 2 => quarter (4 ^ k * p) 0 a
  | 3 => quarter (4 ^ k * p) 3 a
  | 4 => quarter (4 ^ k * p) 0 a + quarter (4 ^ k * p) 1 a
  | 5 => quarter (4 ^ k * p) 2 a - quarter (4 ^ k * p) 0 a
  | 6 => quarter (4 ^ k * p) 1 a - quarter (4 ^ k * p) 3 a

/-- Second actual mathematical operand of each native child. -/
@[expose] def rightOperand (p k : ℕ) (b : ℕ → ℤ) : Fin 7 → ℕ → ℤ
  | 0 => quarter (4 ^ k * p) 0 b + quarter (4 ^ k * p) 3 b
  | 1 => quarter (4 ^ k * p) 0 b
  | 2 => quarter (4 ^ k * p) 1 b - quarter (4 ^ k * p) 3 b
  | 3 => quarter (4 ^ k * p) 2 b - quarter (4 ^ k * p) 0 b
  | 4 => quarter (4 ^ k * p) 3 b
  | 5 => quarter (4 ^ k * p) 0 b + quarter (4 ^ k * p) 1 b
  | 6 => quarter (4 ^ k * p) 2 b + quarter (4 ^ k * p) 3 b

/-- The already-defined finite seven-product recursion on one actual child operand pair. -/
@[expose] def childProduct (p k : ℕ) (a b : ℕ → ℤ) (t : Fin 7) : ℕ → ℤ :=
  multiply p k (leftOperand p k a t) (rightOperand p k b t)

/-- Contribution of a returned child to a selected output quadrant. -/
@[expose] def contribution : Fin 7 → Fin 4 → ℤ
  | 0, 0 | 0, 3 => 1
  | 1, 2 => 1
  | 1, 3 => -1
  | 2, 1 | 2, 3 => 1
  | 3, 0 | 3, 2 => 1
  | 4, 0 => -1
  | 4, 1 => 1
  | 5, 3 => 1
  | 6, 0 => 1
  | _, _ => 0

/-- Signed partial output after the first completed children have been accumulated. -/
@[expose] def partialValue (p k completed : ℕ) (a b : ℕ → ℤ) (quadrant : Fin 4) (r : ℕ) : ℤ :=
  ∑ t : Fin 7, if t.val < completed then contribution t quadrant * childProduct p k a b t r
    else 0

/-- No child has contributed immediately after the actual native clear. -/
@[simp] theorem partialValue_zero (p k : ℕ) (a b : ℕ → ℤ) (quadrant : Fin 4) (r : ℕ) :
    partialValue p k 0 a b quadrant r = 0 := by simp [partialValue]

/-- One returned child changes the partial sum by exactly its fixed signed contribution. -/
theorem partialValue_succ (p k : ℕ) (completed : Fin 7) (a b : ℕ → ℤ)
    (quadrant : Fin 4) (r : ℕ) :
    partialValue p k (completed.val + 1) a b quadrant r =
      partialValue p k completed.val a b quadrant r +
        contribution completed quadrant * childProduct p k a b completed r := by
  classical
  have hs : ∑ t : Fin 7, (if t = completed then
        contribution completed quadrant * childProduct p k a b completed r else 0) =
      contribution completed quadrant * childProduct p k a b completed r := by simp
  rw [← hs, partialValue, partialValue, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : t = completed
  · subst t
    simp
  · have hv : t.val ≠ completed.val := fun h => he (Fin.ext h)
    have hlt : t.val < completed.val + 1 ↔ t.val < completed.val := by omega
    simp only [he, ite_false, add_zero, hlt]

/-- Each output quarter has at most four contributions at every intermediate stage. -/
theorem contribution_weight_le_four (completed : ℕ) (hc : completed ≤ 7) (q : Fin 4) :
    (∑ t : Fin 7, if t.val < completed then (contribution t q).natAbs else 0) ≤ 4 := by
  interval_cases completed <;> fin_cases q <;> decide

/-- Every partial accumulator fits the four-term envelope, without assuming a sparse result. -/
theorem partialValue_natAbs_le {p k completed r C : ℕ} (a b : ℕ → ℤ) (q : Fin 4)
    (hc : completed ≤ 7) (hchild : ∀ t, (childProduct p k a b t r).natAbs ≤ C) :
    (partialValue p k completed a b q r).natAbs ≤ 4 * C := by
  calc
    _ ≤ ∑ t : Fin 7, (if t.val < completed then
          contribution t q * childProduct p k a b t r else 0).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ t : Fin 7, (if t.val < completed then (contribution t q).natAbs else 0) * C := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs <;> simp only [Int.natAbs_mul, Int.natAbs_zero, zero_mul, le_refl]
      exact Nat.mul_le_mul_left _ (hchild t)
    _ = (∑ t : Fin 7, if t.val < completed then (contribution t q).natAbs else 0) * C :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 4 * C := Nat.mul_le_mul_right _ (contribution_weight_le_four completed hc q)

/-- Each concrete operand form has at most twice the original coefficient magnitude. -/
theorem operands_natAbs_le {p k A r : ℕ} (a : ℕ → ℤ) (t : Fin 7)
    (ha : ∀ j < 4 ^ (k + 1) * p, (a j).natAbs ≤ A) (hr : r < 4 ^ k * p) :
    (leftOperand p k a t r).natAbs ≤ 2 * A ∧
      (rightOperand p k a t r).natAbs ≤ 2 * A := by
  have hs : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  have hq (s : ℕ) (hs' : s < 4) : (quarter (4 ^ k * p) s a r).natAbs ≤ A :=
    quarter_natAbs_le (by simpa only [← hs] using ha) hs' hr
  have h₀ := hq 0 (by decide)
  have h₁ := hq 1 (by decide)
  have h₂ := hq 2 (by decide)
  have h₃ := hq 3 (by decide)
  fin_cases t <;> constructor <;> simp only [leftOperand, rightOperand, Pi.add_apply, Pi.sub_apply]
  all_goals first
    | exact (Int.natAbs_add_le _ _).trans (by omega)
    | omega

/-- Child coefficient bounds come from the already-proved finite recursion, rather than
an assumed child result bound. -/
theorem childProduct_natAbs_le {p k A B r : ℕ} (a b : ℕ → ℤ) (t : Fin 7)
    (ha : ∀ j < 4 ^ (k + 1) * p, (a j).natAbs ≤ A)
    (hb : ∀ j < 4 ^ (k + 1) * p, (b j).natAbs ≤ B) (hr : r < 4 ^ k * p) :
    (childProduct p k a b t r).natAbs ≤ p * ((2 * A) * (2 * B)) * 16 ^ k :=
  multiply_natAbs_le k _ _ (fun _ hj => (operands_natAbs_le a t ha hj).1)
    (fun _ hj => (operands_natAbs_le b t hb hj).2) hr

/-- The four completed output expressions are exactly the usual Strassen combinations. -/
theorem partialValue_seven (p k : ℕ) (a b : ℕ → ℤ) (q : Fin 4) (r : ℕ) :
    partialValue p k 7 a b q r = match q with
    | 0 => childProduct p k a b 0 r + childProduct p k a b 3 r - childProduct p k a b 4 r +
        childProduct p k a b 6 r
    | 1 => childProduct p k a b 2 r + childProduct p k a b 4 r
    | 2 => childProduct p k a b 1 r + childProduct p k a b 3 r
    | 3 => childProduct p k a b 0 r - childProduct p k a b 1 r + childProduct p k a b 2 r +
        childProduct p k a b 5 r := by
  fin_cases q <;> norm_num [partialValue, contribution, Fin.sum_univ_succ] <;> ring

/-- The completed native-style partial invariant agrees with the existing finite multiply
specification on every real coefficient of each output quadrant. -/
theorem multiply_eq_partialValue {p k r : ℕ} (hp : 0 < p) (a b : ℕ → ℤ)
    (t : Fin 4) (hr : r < 4 ^ k * p) :
    multiply p (k + 1) a b (t.val * (4 ^ k * p) + r) = partialValue p k 7 a b t r := by
  have hq : 0 < 4 ^ k * p := Nat.mul_pos (by positivity) hp
  have hm : t.val * (4 ^ k * p) + r = (4 ^ k * p) * t.val + r := by ring
  rw [multiply, assemble, hm, Nat.mul_add_div hq, Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr, partialValue_seven]
  fin_cases t <;> rfl

end Cslib.Algorithms.MatrixMultiplication.Strassen
