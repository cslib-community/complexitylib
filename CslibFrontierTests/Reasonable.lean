/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.Probability.Multilinear.Bonami
import CslibFrontier.Probability.BitString.Rademacher
import Mathlib.Probability.UniformOn

/-! # Tests for reasonable random variables

The moments of a standard Gaussian and of a uniformly random sign; reasonableness (O'Donnell,
Definition 9.1) of standard Gaussians, of uniformly random signs realized as coordinates of a
product measure, of the unnormalized Gaussians `2 g`, and of a sign as a function on `Bool`, by
finite averages; Hypothesis 11.65 from reasonableness; a uniform bit read as `0` or `1`, which
is not `1`-reasonable; and the Bonami Lemma (O'Donnell, Corollary 9.6) for a sparse sign, which is
`10`-reasonable but not `9`-reasonable, in degrees `1` and `2`, where the degree-`2` bound is
sharp. -/

namespace CslibFrontierTests.Reasonable

open MeasureTheory ProbabilityTheory Cslib.BitString

/-! ### Standard Gaussians -/

/-- The law of independent standard Gaussians on `Fin n → ℝ`. -/
noncomputable abbrev gaussians (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- Each coordinate of `gaussians n` is a standard Gaussian. -/
theorem hasLaw_gaussians (n : ℕ) (i : Fin n) :
    HasLaw (fun x : Fin n → ℝ => x i) (gaussianReal 0 1) (gaussians n) :=
  (measurePreserving_eval (fun _ => gaussianReal 0 1) i).hasLaw

/-- A coordinate of `gaussians n` is `3`-reasonable with moments `0`, `1` and `0`. -/
example (n : ℕ) (i : Fin n) : IsReasonable 3 (fun x : Fin n → ℝ => x i) (gaussians n) ∧
    ∫ x, x i ∂gaussians n = 0 ∧ ∫ x, x i ^ 2 ∂gaussians n = 1 ∧ ∫ x, x i ^ 3 ∂gaussians n = 0 :=
  ⟨(hasLaw_gaussians n i).isReasonable_three_of_gaussianReal,
    (hasLaw_gaussians n i).integral_eq_zero_of_gaussianReal,
    (hasLaw_gaussians n i).integral_sq_eq_one_of_gaussianReal,
    (hasLaw_gaussians n i).integral_pow_three_eq_zero_of_gaussianReal⟩

/-- Reasonableness does not see the scale: `2 g` is still `3`-reasonable, though `E[(2 g)²] = 4`.
-/
example (n : ℕ) (i : Fin n) : IsReasonable 3 (fun x : Fin n → ℝ => 2 * x i) (gaussians n) :=
  (hasLaw_gaussians n i).isReasonable_three_of_gaussianReal.const_mul 2

/-- A `3`-reasonable variable is `9`-reasonable. -/
example : IsReasonable 9 id (gaussianReal 0 1) :=
  isReasonable_id_gaussianReal.mono (by norm_num)

/-- Hypothesis 11.65 for a standard Gaussian, from its reasonableness and its moments. -/
example : HasInvarianceMoments (gaussianReal 0 1) :=
  hasInvarianceMoments_iff.2 ⟨isReasonable_id_gaussianReal.mono (by norm_num),
    integral_id_gaussianReal, integral_sq_gaussianReal, integral_pow_three_gaussianReal⟩

/-! ### Uniformly random signs -/

/-- The law of independent uniformly random bits on `Fin n → Bool`. -/
noncomputable abbrev bits (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi fun _ => uniformOn Set.univ

/-- Each sign of `bits n` is `1`-reasonable. -/
theorem isReasonable_bits (n : ℕ) (i : Fin n) :
    IsReasonable 1 (fun ω : Fin n → Bool => signVal (ω i)) (bits n) :=
  isReasonable_one_of_sq_eq_one ((measurable_of_countable _).aemeasurable)
    (ae_of_all _ fun ω => signVal_sq (ω i))

/-- Each sign of `bits n` has mean `0`. -/
theorem integral_bits (n : ℕ) (i : Fin n) : ∫ ω, signVal (ω i) ∂bits n = 0 := by
  have h : ∫ b, signVal b ∂(uniformOn (Set.univ : Set Bool)) = 0 := by
    rw [integral_fintype .of_finite, Fintype.sum_bool, measureReal_def, measureReal_def,
      uniformOn_univ, uniformOn_univ]
    simp
  rw [← h]
  exact ((measurePreserving_eval (fun _ => uniformOn (Set.univ : Set Bool)) i).hasLaw).integral_comp
    (f := signVal) (measurable_of_countable _).aestronglyMeasurable

/-- Each sign of `bits n` has second moment `1` and third moment `0`. -/
example (n : ℕ) (i : Fin n) :
    ∫ ω, signVal (ω i) ^ 2 ∂bits n = 1 ∧ ∫ ω, signVal (ω i) ^ 3 ∂bits n = 0 :=
  ⟨integral_sq_eq_one_of_sq_eq_one (ae_of_all _ fun ω => signVal_sq (ω i)),
    (integral_pow_three_eq_integral_of_sq_eq_one
      (X := fun ω : Fin n → Bool => signVal (ω i)) (ae_of_all _ fun ω => signVal_sq (ω i))).trans
      (integral_bits n i)⟩

/-- Reasonableness transfers along a law: the sign of a uniform bit, pushed forward to `ℝ`. -/
example : IsReasonable 1 id ((uniformOn (Set.univ : Set Bool)).map signVal) := by
  have hX : HasLaw signVal ((uniformOn (Set.univ : Set Bool)).map signVal)
      (uniformOn (Set.univ : Set Bool)) :=
    ⟨(measurable_of_countable _).aemeasurable, rfl⟩
  refine hX.isReasonable_iff.1 ?_
  rw [isReasonable_uniformOn_univ_iff]
  simp only [Finset.expect_eq_sum_div_card, Fintype.sum_bool, Finset.card_univ,
    Fintype.card_bool]
  norm_num

/-- A uniform bit read as `0` or `1` is not `1`-reasonable: `𝔼 X ^ 4 = 1 / 2` exceeds
`(𝔼 X ^ 2) ^ 2 = 1 / 4`. (It is `2`-reasonable.) -/
example : ¬ IsReasonable 1 (fun b : Bool => if b then (1 : ℝ) else 0)
      (uniformOn (Set.univ : Set Bool)) ∧
    IsReasonable 2 (fun b : Bool => if b then (1 : ℝ) else 0)
      (uniformOn (Set.univ : Set Bool)) := by
  simp only [isReasonable_uniformOn_univ_iff, Finset.expect_eq_sum_div_card, Fintype.sum_bool,
    Finset.card_univ, Fintype.card_bool]
  norm_num

/-! ### The Bonami Lemma for a `10`-reasonable variable -/

/-- A sparse sign: `1` and `-1` with probability `1 / 20` each and `0` otherwise, as a function of
a uniformly random point of `Fin 20`. -/
noncomputable def sparseSign (x : Fin 20) : ℝ := if x = 0 then 1 else if x = 1 then -1 else 0

/-- The law of `sparseSign` on `ℝ`. -/
noncomputable abbrev sparseSignLaw : Measure ℝ :=
  (uniformOn (Set.univ : Set (Fin 20))).map sparseSign

theorem hasLaw_sparseSign : HasLaw sparseSign sparseSignLaw (uniformOn Set.univ) :=
  ⟨(measurable_of_countable _).aemeasurable, rfl⟩

/-- The sparse sign has `E[z²] = 1 / 10` and `E[z⁴] = 1 / 10 = 10 E[z²] ^ 2`: it is
`10`-reasonable but not `9`-reasonable, so Hypothesis 11.65 does not apply. -/
theorem isReasonable_sparseSign :
    IsReasonable 10 id sparseSignLaw ∧ ¬ IsReasonable 9 id sparseSignLaw := by
  simp only [← hasLaw_sparseSign.isReasonable_iff, isReasonable_uniformOn_univ_iff,
    Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, Finset.card_univ, Fintype.card_fin,
    sparseSign]
  norm_num

/-- The sparse sign has mean `0` and third moment `0`. -/
theorem integral_sparseSign :
    ∫ z, z ∂sparseSignLaw = 0 ∧ ∫ z, z ^ 3 ∂sparseSignLaw = 0 := by
  rw [← hasLaw_sparseSign.integral_comp (f := fun z => z) (by fun_prop),
    ← hasLaw_sparseSign.integral_comp (f := fun z => z ^ 3) (by fun_prop),
    integral_uniformOn_univ, integral_uniformOn_univ]
  norm_num [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, sparseSign]

/-- **Corollary 9.6** with `B = 10 > 9`: every polynomial in two independent sparse signs, which
has degree at most `2`, is `max(10, 9) ^ 2 = 100`-reasonable. -/
example (c : Finset (Fin 2) → ℝ) :
    IsReasonable 100 (multilinearEval c) (Measure.pi fun _ => sparseSignLaw) := by
  have h := isReasonable_multilinearEval (fun _ : Fin 2 => sparseSignLaw)
    (fun _ => isReasonable_sparseSign.1) (fun _ => integral_sparseSign.1)
    (fun _ => integral_sparseSign.2) (k := 2) (c := c)
    (fun S hS => absurd (S.card_le_univ.trans_lt hS) (by simp))
  norm_num at h
  exact h

/-- **Corollary 9.6** in degree `1`: the sum `z₁ + ⋯ + zₙ` of `n` independent sparse signs is
`10`-reasonable. -/
example (n : ℕ) :
    IsReasonable 10 (fun z : Fin n → ℝ => ∑ i, z i) (Measure.pi fun _ => sparseSignLaw) := by
  have h := isReasonable_multilinearEval (fun _ : Fin n => sparseSignLaw)
    (fun _ => isReasonable_sparseSign.1) (fun _ => integral_sparseSign.1)
    (fun _ => integral_sparseSign.2) (k := 1)
    (c := fun S => if S.card = 1 then 1 else 0) (fun S hS => by simp [hS.ne'])
  have hf : multilinearEval (fun S : Finset (Fin n) => if S.card = 1 then 1 else 0) =
      fun z => ∑ i, z i := funext fun z => by
    simp only [multilinearEval_def, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.univ_filter_card_eq, Finset.powersetCard_one,
      Finset.sum_map]
    simp
  rw [hf] at h
  norm_num at h
  exact h

/-- The degree-`2` bound is sharp for the sparse sign: `z₀ z₁` has `E[(z₀ z₁)⁴] = 1 / 100` and
`E[(z₀ z₁)²] = 1 / 100`, so it is `100`-reasonable but not `99`-reasonable. -/
example : ¬ IsReasonable 99 (fun z : Fin 2 → ℝ => z 0 * z 1)
    (Measure.pi fun _ => sparseSignLaw) := by
  have hmom (p : ℕ) : ∫ z : Fin 2 → ℝ, (z 0 * z 1) ^ p ∂Measure.pi (fun _ => sparseSignLaw) =
      (∫ x, x ^ p ∂sparseSignLaw) ^ 2 := by
    simpa [Fin.prod_univ_two, mul_pow] using
      integral_fintype_prod_eq_pow (ι := Fin 2) (μ := sparseSignLaw) (fun x : ℝ => x ^ p)
  have hp (p : ℕ) (hp : p = 2 ∨ p = 4) : ∫ x, x ^ p ∂sparseSignLaw = 1 / 10 := by
    rw [← hasLaw_sparseSign.integral_comp (f := fun x => x ^ p) (by fun_prop),
      integral_uniformOn_univ]
    rcases hp with rfl | rfl <;>
      simp only [Finset.expect_eq_sum_div_card, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
      norm_num [sparseSign]
  intro h
  have h4 := h.integral_pow_four_le
  simp only [hmom, hp 4 (.inr rfl), hp 2 (.inl rfl)] at h4
  norm_num at h4

end CslibFrontierTests.Reasonable
