/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows
import Mathlib.Tactic.Linarith

/-!
# Fourth-root errors of concrete polynomial row outputs

The shared discrepancy compares the actual polynomial outputs of two row states, using each
state's own default-padded rank. Each entry's root error has magnitude at most one. The sum of
its fourth powers over retained endpoints is at most `2 * K`, independently of the row width
and all entry magnitudes. These are the range and support facts used in the false-overflow
charge and the relative-stability comparison in [OpenAI2026LogSpace, Sections 8.3--8.4].

## Main definitions

* `Cslib.PolynomialAtomRow.stateRootError`: the actual fourth-root output discrepancy.

## Main results

* `Cslib.PolynomialAtomRow.abs_stateRootError_le_one`: the pointwise range bound.
* `Cslib.PolynomialAtomRow.sum_stateRootError_pow_four_le`: the width-independent support bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 8.3--8.4, bounded-output comparisons for row functions
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression
open scoped BigOperators

variable {ι : Type*} (kind : PolynomialAtomRow)

/-- The actual fourth-root discrepancy of two row states, with their own padded ranks. -/
@[expose] noncomputable def stateRootError (θ : ℝ) (S : Finset ι) (K : ℕ)
    (a b : State ι) (y : ι) : ℝ :=
  kind.eval θ (a.row y 0) (firstRank S K a.defaultValue a.row) ^ (4⁻¹ : ℝ) -
    kind.eval θ (b.row y 0) (firstRank S K b.defaultValue b.row) ^ (4⁻¹ : ℝ)

/-- Both actual output roots lie in `[0,1]`, for every input row and default. -/
theorem abs_stateRootError_le_one (θ : ℝ) (S : Finset ι) (K : ℕ)
    (a b : State ι) (y : ι) : |kind.stateRootError θ S K a b y| ≤ 1 := by
  have ha0 := Real.rpow_nonneg (kind.eval_nonneg θ (a.row y 0)
    (firstRank S K a.defaultValue a.row)) (4⁻¹ : ℝ)
  have hb0 := Real.rpow_nonneg (kind.eval_nonneg θ (b.row y 0)
    (firstRank S K b.defaultValue b.row)) (4⁻¹ : ℝ)
  have ha1 := Real.rpow_le_one (kind.eval_nonneg θ (a.row y 0) _)
    (kind.eval_le_one θ (a.row y 0) (firstRank S K a.defaultValue a.row))
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hb1 := Real.rpow_le_one (kind.eval_nonneg θ (b.row y 0) _)
    (kind.eval_le_one θ (b.row y 0) (firstRank S K b.defaultValue b.row))
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  unfold stateRootError
  apply abs_sub_le_iff.mpr
  constructor <;> linarith

/-- The discrepancy is supported on the union of the two actual supports. Neither the
ambient cardinality nor a bound on the row entries occurs in its fourth-power sum. -/
theorem sum_stateRootError_pow_four_le {θ : ℝ} (hθ : 0 < θ) (S : Finset ι) {K : ℕ}
    (hK : 0 < K) (a b : State ι) :
    ∑ y ∈ S, |kind.stateRootError θ S K a b y| ^ 4 ≤ 2 * (K : ℝ) := by
  classical
  let A := {y ∈ S | kind.eval θ (a.row y 0) (firstRank S K a.defaultValue a.row) ≠ 0}
  let B := {y ∈ S | kind.eval θ (b.row y 0) (firstRank S K b.defaultValue b.row) ≠ 0}
  let D := {y ∈ S | kind.stateRootError θ S K a b y ≠ 0}
  have hsub : D ⊆ A ∪ B := by
    intro y hy
    obtain ⟨hyS, hy⟩ := mem_filter.mp hy
    by_cases ha : kind.eval θ (a.row y 0) (firstRank S K a.defaultValue a.row) = 0
    · apply mem_union_right
      refine mem_filter.mpr ⟨hyS, fun hb => hy ?_⟩
      simp [stateRootError, ha, hb]
    · exact mem_union_left _ (mem_filter.mpr ⟨hyS, ha⟩)
  have hcard : #D ≤ 2 * K := by
    have hA : #A < K := kind.card_filter_eval_ne_zero_lt hθ hK
    have hB : #B < K := kind.card_filter_eval_ne_zero_lt hθ hK
    have h := (card_le_card hsub).trans (card_union_le A B)
    omega
  rw [← sum_filter_of_ne (p := fun y => kind.stateRootError θ S K a b y ≠ 0)
    fun y _ h hy => h (by rw [hy, abs_zero, zero_pow (by decide)])]
  calc
    _ ≤ ∑ _y ∈ D, (1 : ℝ) := by
      refine sum_le_sum fun y _ => ?_
      simpa using pow_le_pow_left₀ (abs_nonneg (kind.stateRootError θ S K a b y))
        (kind.abs_stateRootError_le_one θ S K a b y) 4
    _ = (#D : ℝ) := by simp
    _ ≤ 2 * (K : ℝ) := by exact_mod_cast hcard

end Cslib.PolynomialAtomRow
