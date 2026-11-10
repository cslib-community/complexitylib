/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.LogSpaceDerandomization.HeavyCount
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FalseOverflow
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generic false-overflow fourth-moment charges on normalized row norms

This module factors out the row-error-agnostic false-first-overflow fourth-moment charge and the
finite-union mask bound used to bound normalized fourth-power row norms from
`Cslib.RowCompression.one_le_sum_clippedError_pow_of_firstOverflow_dyadic`, together with the
three-budget integration step that the compression assemblies combine with that charge.

## Main results

* `Cslib.RowCompression.sum_err_pow_four_le_of_false`: pointwise fourth-power false-overflow
  charge for any bounded endpoint error.
* `Cslib.RowCompression.rowNormPow_falseFirstOverflow_le_of_bound`: normalized false-overflow
  output charge at a specified group for any row-wise bounded error.
* `Cslib.rowNormPow_ite_exists_le_sum`: bounds a fourth-power row norm under an existential mask
  over `range m` by the sum of the single-index masked norms.
* `Cslib.rowNormPow_le_three_budgets_add_ite`: rows outside an event, with a `2K`-support
  three-budget fourth-moment bound, pay the integrated budgets; rows on the event remain as a
  masked norm.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, equations (8.12) on p. 48 and (8.16) on p. 49 (source labels
  `buf-false-charge` and `buf-false-sum`)
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib

open Finset Probability
open scoped BigOperators

section ExistentialMask

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

/-- The fourth-power row norm on an existential event over `j < m` is at most the sum of the
single-index masked norms. -/
theorem rowNormPow_ite_exists_le_sum {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (m : ℕ) (F : ℕ → Ω → V → Prop) [∀ j σ x, Decidable (F j σ x)]
    (D : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => if ∃ j < m, F j σ x then D σ x y else 0) ≤
      ∑ j ∈ range m, rowNormPow 4 N u X Y (fun σ x y => if F j σ x then D σ x y else 0) := by
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

end ExistentialMask

section BudgetAssembly

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

private theorem add_add_pow_four_le (a b c : ℝ) :
    (a + b + c) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h4 : Even 4 := ⟨2, rfl⟩
  have h1 := h4.add_pow_le (a := a + b) (b := c)
  have h2 := h4.add_pow_le (a := a) (b := b)
  norm_num at h1 h2
  nlinarith [h4.pow_nonneg c]

/-- Rows outside an event `F` whose fourth moment is at most `2 * K` times the fourth power of
a three-budget envelope `A * Pre + C * No + C * Tail` pay the integrated budgets; rows on `F`
are kept as an `F`-masked remainder. -/
theorem rowNormPow_le_three_budgets_add_ite {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (F : Ω → V → Prop) [∀ σ x, Decidable (F σ x)] (D : Ω → V → V → ℝ) (K : ℕ) (A C : ℝ)
    (Pre No Tail : Ω → V → ℝ)
    (hD : ∀ σ x, X σ x → ¬F σ x →
      ∑ y ∈ ({y | Y σ y} : Finset V), |D σ x y| ^ 4 ≤
        2 * (K : ℝ) * (A * Pre σ x + C * No σ x + C * Tail σ x) ^ 4) :
    rowNormPow 4 N u X Y D ≤
      128 * (K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
        C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
      rowNormPow 4 N u X Y (fun σ x y => if F σ x then D σ x y else 0) := by
  have hrow (σ : Ω) (x : V) (hx : X σ x) :
      ∑ y ∈ ({y | Y σ y} : Finset V), |D σ x y| ^ 4 ≤
        128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
          C ^ 4 * |Tail σ x| ^ 4) +
        ∑ y ∈ ({y | Y σ y} : Finset V), |if F σ x then D σ x y else 0| ^ 4 := by
    by_cases hf : F σ x
    · simp only [hf, ↓reduceIte, le_add_iff_nonneg_left]
      positivity
    · simp only [hf, ↓reduceIte, abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero,
        add_zero]
      refine (hD σ x hx hf).trans ?_
      have hS := add_add_pow_four_le (A * Pre σ x) (C * No σ x) (C * Tail σ x)
      have h4 : Even 4 := ⟨2, rfl⟩
      rw [h4.pow_abs, h4.pow_abs, h4.pow_abs, ← mul_pow, ← mul_pow, ← mul_pow]
      exact (mul_le_mul_of_nonneg_left hS (by positivity)).trans_eq (by ring)
  unfold rowNormPow vertexNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        (128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
          C ^ 4 * |Tail σ x| ^ 4) +
          ∑ y ∈ ({y | Y σ y} : Finset V), |if F σ x then D σ x y else 0| ^ 4) := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      exact sum_le_sum fun x hx => hrow σ x (mem_filter.mp hx).2
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, expect_add_distrib, ← mul_expect]
      ring

end BudgetAssembly

namespace RowCompression

/-- Any endpoint error function whose summed fourth power is at most `2 * K * M` is charged at
a false first overflow by the fourth moment of the uncompressed raw prefix at `j + 1`. -/
theorem sum_err_pow_four_le_of_false {ι : Type*} {η : ℝ}
    {S : Finset ι} {n : ℕ → ℕ} {K : ℕ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {truth : ι → Fin 2 → ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (ha : a.defaultValue = 0)
    (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (hover : IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j)
    (hfirst : ∀ y ∈ S, 0 ≤ truth y 0)
    (hsecond : ∀ y ∈ S, truth y 0 ≤ dyadicFloor η m j / 4 → truth y 1 = 0)
    (hheavy : 2 * #{y ∈ S | dyadicFloor η m j / 4 < truth y 0} < n j)
    {err : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∑ y ∈ S, |err y| ^ 4 ≤ 2 * (K : ℝ) * M) :
    ∑ y ∈ S, |err y| ^ 4 ≤
      (64 * (K : ℝ) * M / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        ∑ y ∈ S, |clippedError (truth y 0) (truth y 1)
          (uncompressedRow Δ a.row (j + 1) y)| ^ 4 := by
  have hcharge := one_le_sum_clippedError_pow_of_firstOverflow_dyadic hη hη1 ha
    m j hj hn hover hfirst hsecond hheavy 4
  have he (y : ι) : |clippedError (truth y 0) (truth y 1)
      (uncompressedRow Δ a.row (j + 1) y)| =
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (j + 1) y) :=
    abs_of_nonneg (clippedError_nonneg _ _ _)
  calc
    _ ≤ 2 * (K : ℝ) * M := hbound
    _ = (2 * (K : ℝ) * M) * 1 := by ring
    _ ≤ (2 * (K : ℝ) * M) * ((2 : ℝ) ^ (4 + 1) /
        ((n j : ℝ) * dyadicFloor η m j ^ 4) *
          ∑ y ∈ S, clippedError (truth y 0) (truth y 1)
            (uncompressedRow Δ a.row (j + 1) y) ^ 4) :=
      mul_le_mul_of_nonneg_left hcharge (by positivity)
    _ = _ := by simp only [he]; norm_num; ring

section NormalizedNorm

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

open Classical in
/-- Normalized false-first-overflow charge at a specified group `j` for any row error `err`
whose row-wise fourth-power sum is at most `2 * K * M`. -/
theorem rowNormPow_falseFirstOverflow_le_of_bound {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (K m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (err : Ω → V → V → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (herr : ∀ σ x, X σ x →
      ∑ y ∈ ({y | Y σ y} : Finset V), |err σ x y| ^ 4 ≤ 2 * (K : ℝ) * M)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let F := fun σ x => IsFirstOverflow (S σ) n (fun _ => K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y => if F σ x then err σ x y else 0) ≤
      (64 * (K : ℝ) * M / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  dsimp only
  unfold rowNormPow
  have hc : 0 ≤ 64 * (K : ℝ) * M / ((n j : ℝ) * dyadicFloor η m j ^ 4) := by positivity
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        (64 * (K : ℝ) * M / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
          ∑ y ∈ ({y | Y σ y} : Finset V),
            |clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      refine sum_le_sum fun x hx => ?_
      have hx' := (mem_filter.mp hx).2
      dsimp only
      split_ifs with hF
      · apply sum_err_pow_four_le_of_false hη hη1 (ha σ x hx') m j hj hn hF.1
        · intro y hy
          exact hfirst σ x y hx' (mem_filter.mp hy).2
        · intro y hy
          exact hsecond σ x y hx' (mem_filter.mp hy).2
        · simpa only [heavyCountEvent, filter_filter] using Nat.lt_of_not_ge hF.2
        · exact hM
        · exact herr σ x hx'
      · simp only [abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero]
        exact mul_nonneg hc (sum_nonneg fun _ _ => by positivity)
    _ = _ := by simp only [← mul_sum, ← mul_expect]; ring

end NormalizedNorm

end RowCompression

end Cslib
