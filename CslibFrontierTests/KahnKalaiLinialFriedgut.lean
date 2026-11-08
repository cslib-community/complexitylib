/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta

/-! Instances and non-vacuity witnesses for the Kahn–Kalai–Linial theorem, Talagrand's
inequality and Friedgut's junta theorem. -/

namespace ComplexityTests.KahnKalaiLinialFriedgut

open Cslib Cslib.BitString Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Kahn–Kalai–Linial theorem -/

-- The statement for `f : (Fin n → Bool) → Bool`, `n ≥ 1`: some coordinate has influence at
-- least `Var[F] log n / (12 n)`.
example {n : ℕ} [NeZero n] (f : (Fin n → Bool) → Bool) :
    ∃ i, (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * Real.log n / (12 * n) ≤
      influence i (fun x => signVal (f x)) := by
  simpa only [Fintype.card_fin] using exists_expect_sub_expect_sq_mul_log_card_div_le_influence f

-- The total influence form with `δ` the largest influence.
example [Nonempty ι] (f : (ι → Bool) → Bool) :
    (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) *
        Real.log (univ.sup' univ_nonempty fun i => influence i fun x => signVal (f x))⁻¹ ≤
      6 * totalInfluence (fun x => signVal (f x)) :=
  expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence f fun i =>
    le_sup' (fun i => influence i fun x => signVal (f x)) (mem_univ i)

/-! ### Talagrand's inequality -/

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

-- Its influences are less than one: at the all-`false` point no single flip changes it.
theorem influence_and₂_lt_one (i : Fin 2) : influence i (fun x => signVal (and₂ x)) < 1 := by
  rw [influence_signVal]
  calc 𝔼 x, (if and₂ (Function.update x i !x i) = and₂ x then (0 : ℝ) else 1)
      < 𝔼 _x : Fin 2 → Bool, (1 : ℝ) := by
        refine expect_lt_expect (fun x _ => by split_ifs <;> norm_num) ⟨0, mem_univ _, ?_⟩
        have h : and₂ (Function.update 0 i !(0 : Fin 2 → Bool) i) = and₂ 0 := by
          fin_cases i <;> decide
        rw [ite_eq_left h]
        exact one_pos
    _ = 1 := expect_const univ_nonempty 1

-- So the hypothesis of Talagrand's inequality is satisfiable by a nonconstant function.
example : 𝔼 x, (signVal (and₂ x) - 𝔼 y, signVal (and₂ y)) ^ 2 ≤
    6 * ∑ i, influence i (fun x => signVal (and₂ x)) /
      Real.log (influence i fun x => signVal (and₂ x))⁻¹ :=
  expect_sub_expect_sq_le_six_mul_sum_influence_div_log and₂ influence_and₂_lt_one

/-! ### Friedgut's junta theorem -/

-- The bound on the total influence can be the total influence itself: every Boolean function is
-- `ε`-close to a function of at most `4 I ^ 3 / (9 ε ^ 2) · 81 ^ (I / ε)` coordinates.
example (f : (ι → Bool) → Bool) {ε : ℝ} (hε : 0 < ε) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 4 * totalInfluence (fun x => signVal (f x)) ^ 3 / (9 * ε ^ 2) *
        81 ^ (totalInfluence (fun x => signVal (f x)) / ε) ∧
      DependsOn g (J : Set ι) ∧ (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε :=
  exists_dependsOn_hammingDist_div_le_of_totalInfluence_le f hε le_rfl

-- The exponential form at `ε = 1 / 4` for a function of `n` bits of total influence at most `2`:
-- it is `1/4`-close to a function of at most `3 · 2 ^ 64` coordinates.
example {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : totalInfluence (fun x => signVal (f x)) ≤ 2) :
    ∃ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      (#J : ℝ) ≤ 3 * 2 ^ (8 * 2 / (1 / 4) : ℝ) ∧ DependsOn g (J : Set (Fin n)) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card (Fin n) ≤ 1 / 4 :=
  exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le f (by norm_num) (by norm_num) hf

-- The hypothesis of the exponential form is satisfiable by a nonconstant function: the
-- conjunction of two bits has total influence at most two.
example : totalInfluence (fun x => signVal (and₂ x)) ≤ 2 := by
  have h := totalInfluence_le_mul_expect_sq (fun x => signVal (and₂ x))
  simp only [sq, signVal_mul_self, Fintype.card_fin, Nat.cast_ofNat] at h
  rw [expect_const univ_nonempty] at h
  linarith

-- With `J = ∅` the weight outside the subsets of `J` is the variance: every Boolean function is
-- `Var[F]`-close to a constant.
example (f : (ι → Bool) → Bool) :
    ∃ g : (ι → Bool) → Bool, DependsOn g ((∅ : Finset ι) : Set ι) ∧
      (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤
        𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 := by
  obtain ⟨g, hg, hfg⟩ := exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f ∅
  refine ⟨g, hg, hfg.trans_eq ?_⟩
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  simp only [subset_empty]

end ComplexityTests.KahnKalaiLinialFriedgut
