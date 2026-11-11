/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.MachineLearning.Rademacher.Margin
import CslibFrontier.Probability.BitString.Massart
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Checks for Talagrand contraction and margin generalization bounds

Exercises `CslibFrontier.MachineLearning.Rademacher.Contraction` and
`CslibFrontier.MachineLearning.Rademacher.Margin`:

* **Equality and strict cases of Talagrand contraction:** on the two-vector family
  `b ↦ (signVal b)` in `ℝ¹`, the Rademacher average is `1`; composing with the non-centered
  `3`-Lipschitz map `u ↦ 5 - 3 u` (`φ 0 = 5 ≠ 0`) achieves the exact contraction bound `3`, while
  composing with the `1`-Lipschitz map `abs` collapses the average to `0`.
* **`marginLoss` values and Lipschitz constant:** checks negative, zero, ramp, threshold, and
  large-margin values at `ρ = 1 / 2`, the `NNReal` Lipschitz constant `2`, and a two-example
  `empiricalMarginLoss` calculation against `empiricalMarginLoss_le_count_div`.
* **Nonvacuous margin generalization bounds:** instantiates both the population Massart margin bound
  `margin_bound_of_finset` (gap `3 / 25 = 0.12`) and the data-dependent margin bound
  `empiricalRademacherComplexity_margin_bound` (gap `23 / 100 = 0.23`) at `ρ = 1 / 2`,
  `m = 10000`, and `δ = 1 / 20` on a two-hypothesis real scoring class on `Bool`.
-/

public section

namespace CslibFrontierTests.RademacherMargin

open Cslib.MachineLearning Cslib.BitString
open scoped BigOperators NNReal

/-! ### Equality and strict cases of Talagrand contraction -/

/-- Two-element vector family `false ↦ (1)`, `true ↦ (-1)` in `ℝ¹`. -/
@[expose] noncomputable def signVec (b : Bool) (_ : Fin 1) : ℝ := signVal b

theorem rademacherAverage_signVec : rademacherAverage signVec = 1 := by
  have hsup (σ : Fin 1 → Bool) : (⨆ b : Bool, 𝔼 i : Fin 1, signVal (σ i) * signVec b i) = 1 := by
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.expect_singleton, signVec]
    refine le_antisymm (ciSup_le fun b => by cases σ 0 <;> cases b <;> norm_num) ?_
    exact le_ciSup_of_le (Finite.bddAbove_range _) (σ 0) (by rw [signVal_mul_self])
  rw [rademacherAverage_def]
  simp only [hsup, Finset.expect_const, Finset.univ_nonempty]

/-- Non-centered `3`-Lipschitz map `u ↦ 5 - 3 u` (`φ 0 = 5 ≠ 0`). -/
@[expose] def shiftedScale (u : ℝ) : ℝ := 5 - 3 * u

theorem lipschitzWith_shiftedScale : LipschitzWith 3 shiftedScale := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, shiftedScale, shiftedScale,
    show (5 - 3 * x) - (5 - 3 * y) = -3 * (x - y) by ring, abs_mul]
  norm_num

/-- **Equality case of Talagrand contraction** (`φ 0 = 5 ≠ 0`): composing `signVec` with
`shiftedScale` attains the exact `3 * rademacherAverage signVec = 3` contraction bound. -/
theorem rademacherAverage_shiftedScale_signVec :
    rademacherAverage (fun b i => shiftedScale (signVec b i)) = 3 ∧
      rademacherAverage (fun b i => shiftedScale (signVec b i)) =
        (3 : ℝ≥0) * rademacherAverage signVec := by
  have hle : rademacherAverage (fun b i => shiftedScale (signVec b i)) ≤ 3 := by
    have hc := rademacherAverage_comp_le (a := signVec) (B := 1) (fun b _ => (abs_signVal b).le)
      (fun _ => lipschitzWith_shiftedScale)
    rw [rademacherAverage_signVec] at hc
    norm_num at hc
    exact hc
  have hge : (3 : ℝ) ≤ rademacherAverage (fun b i => shiftedScale (signVec b i)) := by
    have haff := rademacherAverage_add_mul_signVal_mul (a := signVec) (B := 1)
      (fun b _ => (abs_signVal b).le) (fun _ => 5) (fun _ => true) (by norm_num : (0 : ℝ) ≤ 3)
    have hfun : (fun b i => (5 : ℝ) + 3 * (signVal true * signVec b i)) =
        fun b i => shiftedScale (signVec b i) := by
      funext b i
      simp only [signVal_true, shiftedScale]
      ring
    rw [hfun, rademacherAverage_signVec, mul_one] at haff
    exact haff.symm.le
  have heq : rademacherAverage (fun b i => shiftedScale (signVec b i)) = 3 := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  rw [heq, rademacherAverage_signVec]
  norm_num

/-- **Strict contraction case:** `abs` is `1`-Lipschitz and maps both vectors of `signVec` to `1`,
collapsing the Rademacher average from `1` to `0`. -/
example : rademacherAverage (fun b i => |signVec b i|) = 0 := by
  have hconst : (fun b (i : Fin 1) => |signVec b i|) = fun _ _ => 1 := by
    funext b _
    exact abs_signVal b
  rw [hconst]
  exact (rademacherAverage_eq_of_forall_exists (b := fun (_ : Unit) (_ : Fin 1) => (1 : ℝ))
    (B := 1) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ => ⟨(), rfl⟩) (fun _ => ⟨false, rfl⟩)).trans (rademacherAverage_unique _)

/-! ### `marginLoss` boundary values, Lipschitz constant, and empirical loss -/

example : marginLoss (1 / 2) (-1) = 1 :=
  marginLoss_of_nonpos (by norm_num) (by norm_num)

example : marginLoss (1 / 2) 0 = 1 :=
  marginLoss_of_nonpos (by norm_num) le_rfl

example : marginLoss (1 / 2) (1 / 8) = 3 / 4 := by
  rw [marginLoss_of_mem_Icc (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num

example : marginLoss (1 / 2) (1 / 4) = 1 / 2 := by
  rw [marginLoss_of_mem_Icc (by norm_num) ⟨by norm_num, by norm_num⟩]
  norm_num

example : marginLoss (1 / 2) (1 / 2) = 0 :=
  marginLoss_of_ge (by norm_num) le_rfl

example : marginLoss (1 / 2) 2 = 0 :=
  marginLoss_of_ge (by norm_num) (by norm_num)

example : LipschitzWith 2 (marginLoss (1 / 2)) := by
  simpa using lipschitzWith_marginLoss_nnreal (1 / 2 : ℝ≥0)

/-- On two labeled examples `(false, false)` (`y = +1`) and `(true, true)` (`y = -1`), the scorer
`b ↦ if b then -1/4 else 1` has signed margins `1` and `1 / 4`, so its empirical `(1 / 2)`-margin
loss is `(0 + 1 / 2) / 2 = 1 / 4`, strictly below the `1 / 2` margin-violation fraction bound of
`empiricalMarginLoss_le_count_div`. -/
example :
    empiricalMarginLoss (1 / 2) (fun b : Bool => if b then (-1 / 4 : ℝ) else 1)
      ![(false, false), (true, true)] = 1 / 4 := by
  rw [empiricalMarginLoss_def, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    signVal_false, signVal_true, Bool.false_eq_true, ↓reduceIte]
  have h0 : marginLoss (1 / 2) (1 * 1) = 0 :=
    marginLoss_of_ge (by norm_num) (by norm_num)
  have h1 : marginLoss (1 / 2) (-1 * (-1 / 4)) = 1 / 2 := by
    rw [show (-1 : ℝ) * (-1 / 4) = 1 / 4 by norm_num,
      marginLoss_of_mem_Icc (by norm_num) ⟨by norm_num, by norm_num⟩]
    norm_num
  rw [h0, h1]
  norm_num

/-! ### Nonvacuous finite-class margin generalization bounds via Massart -/

/-- Two opposite `±1` real-valued scorers on `Bool`. -/
@[expose] noncomputable def twoScorers : Finset (Bool → ℝ) :=
  {fun b => signVal b, fun b => -signVal b}

theorem card_twoScorers : twoScorers.card = 2 :=
  Finset.card_pair fun h => by
    have := congrFun h false
    norm_num at this

theorem abs_le_one_of_mem_twoScorers {h : Bool → ℝ} (hh : h ∈ twoScorers) (x : Bool) :
    |h x| ≤ 1 := by
  simp only [twoScorers, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl <;> simp

private theorem sqrt_div_le {a b c : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (hab : a ≤ b * c ^ 2) :
    √(a / b) ≤ c :=
  (Real.sqrt_le_sqrt ((div_le_iff₀ hb).2 (by linarith))).trans_eq (Real.sqrt_sq hc)

/-- **Population Massart margin bound** (`margin_bound_of_finset`, MRT Theorems 3.7 and 5.8 (5.39))
with `ρ = 1 / 2`, `m = 10000`, and `δ = 1 / 20`: with probability at least `19 / 20`, every scorer
`h ∈ twoScorers` has true misclassification error at most `empiricalMarginLoss (1 / 2) h S + 3 / 25`
(`0.12 < 1`, strictly nonvacuous). -/
example (D : PMF (Bool × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 10000 => D).toOuterMeasure
      {S | ∃ h ∈ twoScorers, empiricalMarginLoss (1 / 2) h S + 3 / 25 <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ 1 / 20 := by
  have h1 : √(2 * Real.log (twoScorers.card : ℝ) / (10000 : ℕ)) ≤ 2 / 100 := by
    rw [card_twoScorers]
    refine sqrt_div_le (by norm_num) (by norm_num) ?_
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast
    linarith
  have h2 : √(Real.log (1 / (1 / 20)) / (2 * (10000 : ℕ))) ≤ 4 / 100 := by
    refine sqrt_div_le (by norm_num) (by norm_num) ?_
    rw [one_div_one_div]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
    push_cast
    linarith
  refine le_trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (margin_bound_of_finset D (m := 10000) (by norm_num) (B := 1) zero_le_one
      (fun h hh => abs_le_one_of_mem_twoScorers hh) (ρ := 1 / 2) (by norm_num)
      (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨h, hh, hlt⟩
  exact ⟨h, hh, by linarith⟩

/-- **Data-dependent margin bound** (`empiricalRademacherComplexity_margin_bound`, MRT Theorem 5.8
(5.40)) with `ρ = 1 / 2`, `m = 10000`, and `δ = 1 / 20`: bounding `R̂_{S_X}(twoScorers)` from the
sample by Massart's lemma yields excess risk at most `23 / 100` (`0.23 < 1`) with probability at
least `19 / 20`. -/
example (D : PMF (Bool × Bool)) :
    ((Cslib.Probability.PMF.pi fun _ : Fin 10000 => D).toOuterMeasure
      {S | ∃ h ∈ twoScorers, empiricalMarginLoss (1 / 2) h S + 23 / 100 <
        (D.toOuterMeasure {p | signVal p.2 * h p.1 ≤ 0}).toReal}).toReal ≤ 1 / 20 := by
  have hR (S : Fin 10000 → Bool × Bool) :
      empiricalRademacherComplexity (twoScorers : Set (Bool → ℝ)) (fun i => (S i).1) ≤ 2 / 100 := by
    refine (empiricalRademacherComplexity_le_of_finset (B := 1) zero_le_one
      (fun h hh => abs_le_one_of_mem_twoScorers hh) (fun i => (S i).1)).trans ?_
    rw [one_mul, card_twoScorers]
    refine sqrt_div_le (by norm_num) (by norm_num) ?_
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast
    linarith
  have hε : √(Real.log (2 / (1 / 20)) / (2 * (10000 : ℕ))) ≤ 5 / 100 := by
    refine sqrt_div_le (by norm_num) (by norm_num) ?_
    norm_num only
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40)
    linarith
  refine le_trans (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (empiricalRademacherComplexity_margin_bound D (m := 10000) (by norm_num)
      (H := (twoScorers : Set (Bool → ℝ))) (B := 1) (fun h hh => abs_le_one_of_mem_twoScorers hh)
      (ρ := 1 / 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 20))
  rintro S ⟨h, hh, hlt⟩
  exact ⟨h, hh, by linarith [hR S]⟩

end CslibFrontierTests.RademacherMargin

end
