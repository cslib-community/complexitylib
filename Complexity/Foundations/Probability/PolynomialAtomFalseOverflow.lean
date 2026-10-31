/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.RootError
public import Complexity.Foundations.Probability.HeavyCount
public import Complexity.Foundations.Probability.RootMetric
public import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual polynomial row errors on false first overflows

The computed and true polynomial row outputs are in `[0,1]`, and each has fewer than `K`
retained nonzero entries. Their fourth-root discrepancy therefore has summed fourth power
at most `2 * K`, independently of the row width, default, and later compression states.
At a false first overflow, the existing actual-prefix charge pays for this bounded error.

The resulting normalized bound uses the final state of the real compression recursion and
the raw prefix at `j + 1`. The environment may jointly determine the increments, initial
states, true rows, retained endpoints, and first overflow. No independence is assumed.

This is the bounded-output integration of `buf-false-charge` in the proof of
[OpenAI2026LogSpace, Section 8.4, Proposition 8.5], on the fourth-moment route of issue #1721.
It does not supply prefix mean/noise budgets, sum their geometric costs, prove post-overflow
relative stability, or assert the complete integrated compression estimate.

## Main results

* `Cslib.PolynomialAtomRow.rowNormPow_falseFirstOverflow_le`: the normalized false-overflow
  output charge at a specified group.
* `Cslib.PolynomialAtomRow.rowNormPow_falseFirstOverflowBefore_le`: the finite union over
  possible first-overflow groups, with no additional factor from their number.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, equations labelled `buf-false-charge` and `buf-false-sum`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression Probability
open scoped BigOperators

variable {ι : Type*} (kind : PolynomialAtomRow)

private theorem sum_stateRootError_pow_four_le_of_false {θ η : ℝ} (hθ : 0 < θ)
    {S : Finset ι} {n : ℕ → ℕ} {K : ℕ} (hK : 0 < K)
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : a.defaultValue = 0)
    (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (hover : IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j)
    (hfirst : ∀ y ∈ S, 0 ≤ truth y 0)
    (hsecond : ∀ y ∈ S, truth y 0 ≤ dyadicFloor η m j / 4 → truth y 1 = 0)
    (hheavy : 2 * #{y ∈ S | dyadicFloor η m j / 4 < truth y 0} < n j)
    (b : State ι) :
    ∑ y ∈ S, |kind.stateRootError θ S K b ⟨0, truth⟩ y| ^ 4 ≤
      (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        ∑ y ∈ S, |clippedError (truth y 0) (truth y 1)
          (uncompressedRow Δ a.row (j + 1) y)| ^ 4 := by
  have hcharge := one_le_sum_clippedError_pow_of_firstOverflow_dyadic hη hη1 ha
    m j hj hn hover hfirst hsecond hheavy 4
  have he (y : ι) : |clippedError (truth y 0) (truth y 1)
      (uncompressedRow Δ a.row (j + 1) y)| =
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (j + 1) y) :=
    abs_of_nonneg (clippedError_nonneg _ _ _)
  calc
    _ ≤ 2 * (K : ℝ) := kind.sum_stateRootError_pow_four_le hθ S hK _ _
    _ = (2 * (K : ℝ)) * 1 := by ring
    _ ≤ (2 * (K : ℝ)) * ((2 : ℝ) ^ (4 + 1) /
        ((n j : ℝ) * dyadicFloor η m j ^ 4) *
          ∑ y ∈ S, clippedError (truth y 0) (truth y 1)
            (uncompressedRow Δ a.row (j + 1) y) ^ 4) :=
      mul_le_mul_of_nonneg_left hcharge (by positivity)
    _ = _ := by simp only [he]; norm_num; ring

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

open Classical in
/-- The final actual polynomial outputs on a specified false-first-overflow event are paid
for by the raw-prefix moment at `j + 1`. Every random quantity may share the environment. -/
theorem rowNormPow_falseFirstOverflow_le {θ η N u : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (K : ℕ) (hK : 0 < K) (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if F σ x then kind.stateRootError θ (S σ) K (b σ x) ⟨0, truth σ x⟩ y else 0) ≤
      (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  dsimp only
  unfold rowNormPow
  have hc : 0 ≤ 64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4) := by positivity
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
          ∑ y ∈ ({y | Y σ y} : Finset V),
            |clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      refine sum_le_sum fun x hx => ?_
      have hx' := (mem_filter.mp hx).2
      dsimp only
      split_ifs with hF
      · apply kind.sum_stateRootError_pow_four_le_of_false hθ hK hη hη1 (ha σ x hx')
          m j hj hn hF.1
        · intro y hy
          exact hfirst σ x y hx' (mem_filter.mp hy).2
        · intro y hy
          exact hsecond σ x y hx' (mem_filter.mp hy).2
        · simpa only [heavyCountEvent, filter_filter] using Nat.lt_of_not_ge hF.2
      · simp only [abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero]
        exact mul_nonneg hc (sum_nonneg fun _ _ => by positivity)
    _ = _ := by simp only [← mul_sum, ← mul_expect]; ring

open Classical in
/-- **The false-type contribution to actual final output error.** Taking the union of the
possible false first overflows gives the sum of their raw-prefix charges. Both sides use the
same `RootMetric` normalization, and no independence or final-output error premise is required. -/
theorem rowNormPow_falseFirstOverflowBefore_le {θ η N u : ℝ} (hθ : 0 < θ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (K : ℕ) (hK : 0 < K) (m : ℕ) (hn : ∀ j < m, 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ j < m, ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if ∃ j < m, F j σ x then kind.stateRootError θ (S σ) K (b σ x) ⟨0, truth σ x⟩ y else 0) ≤
      ∑ j ∈ range m, (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  let S := fun σ => ({y | Y σ y} : Finset V)
  let b := fun σ x => iterate (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) m
  let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => K)
    (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
      ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
  let D := fun σ x y => kind.stateRootError θ (S σ) K (b σ x) ⟨0, truth σ x⟩ y
  change rowNormPow 4 N u X Y (fun σ x y => if ∃ j < m, F j σ x then D σ x y else 0) ≤ _
  have hgroup (j : ℕ) (hj : j ∈ range m) :
      rowNormPow 4 N u X Y (fun σ x y => if F j σ x then D σ x y else 0) ≤
        (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
          rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) :=
    kind.rowNormPow_falseFirstOverflow_le hθ hη hη1 hNu X Y n K hK m j
      (mem_range.mp hj) (hn j (mem_range.mp hj)) Δ a truth ha hfirst (hsecond j (mem_range.mp hj))
  refine le_trans ?_ (sum_le_sum hgroup)
  have hpoint (σ : Ω) (x y : V) :
      |if ∃ j < m, F j σ x then D σ x y else 0| ^ 4 ≤
        ∑ j ∈ range m, |if F j σ x then D σ x y else 0| ^ 4 := by
    by_cases hF : ∃ j < m, F j σ x
    · obtain ⟨j, hj, hjF⟩ := hF
      have hsome : ∃ i < m, F i σ x := ⟨j, hj, hjF⟩
      have hsingle := single_le_sum (s := range m)
        (f := fun i => |if F i σ x then D σ x y else 0| ^ 4)
        (fun _ _ => by positivity) (mem_range.mpr hj)
      simpa only [hsome, hjF, ↓reduceIte] using hsingle
    · simp only [hF, ↓reduceIte, abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0)]
      exact sum_nonneg fun _ _ => by positivity
  have hswap (σ : Ω) :
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        ∑ j ∈ range m, |if F j σ x then D σ x y else 0| ^ 4) =
      ∑ j ∈ range m, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), |if F j σ x then D σ x y else 0| ^ 4 := by
    simp_rw [sum_comm (s := ({y | Y σ y} : Finset V)) (t := range m)]
    rw [sum_comm]
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), ∑ j ∈ range m,
          |if F j σ x then D σ x y else 0| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ => hpoint σ x y
    _ = _ := by simp only [hswap, expect_sum_comm, mul_sum]

end Cslib.PolynomialAtomRow
