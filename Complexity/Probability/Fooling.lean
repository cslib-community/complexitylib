/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Degree
public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.SmallBias
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Complexity.Probability.PMF

/-!
# Fooling functions on the cube, and `k`-wise independence

A distribution `X` on the cube `ι → Bool` *`ε`-fools* a real function `F` on the cube
(`Cslib.BitString.Fools`) if the expectation of `F` under `X` is within `ε` of its expectation
under the uniform distribution. A distribution is *`k`-wise independent*
(`Cslib.BitString.IsKWiseIndependent`) if every `k` of its coordinates are uniformly distributed;
in terms of biases, its bias at every nonempty set of at most `k` coordinates vanishes, and this is
how the abbreviation is defined, as `IsKWiseSmallBias k 0`. A uniformly seeded `k`-wise
independent family of bit strings, such as one built from `Cslib.Probability.polynomialHash`,
induces a `k`-wise independent distribution
(`Cslib.Probability.IsKWiseIndependentHash.isKWiseIndependent_map`).

The expectation of `F` under `X` is the sum of the Fourier coefficients of `F` weighted by the
biases of `X` (`Cslib.BitString.sum_mul_eq_sum_fourierCoeff_mul_bias`). A function of degree at
most `k` has no Fourier weight above level `k`, so a `k`-wise independent distribution fools it
exactly [Braverman, Proposition 6][Braverman2010]
(`Cslib.BitString.IsKWiseIndependent.fools_of_mem_lowDegree`).

A Boolean function is fooled once both it and its negation have one-sided lower bounds
(`Cslib.BitString.fools_bitVal_of_le`), which is how [Braverman][Braverman2010] obtains the
two-sided bound of his Main Theorem from the one-sided Lemma 12.

## Main definitions

* `Cslib.BitString.Fools`: `X` `ε`-fools `F`.
* `Cslib.BitString.IsKWiseIndependent`: `k`-wise independent distributions on the cube.

## Main results

* `Cslib.BitString.sum_mul_eq_sum_fourierCoeff_mul_bias`: expectations through Fourier
  coefficients and biases.
* `Cslib.BitString.IsKWiseIndependent.fools_of_mem_lowDegree`: `k`-wise independence fools
  degree-`k` functions exactly.
* `Cslib.Probability.IsKWiseIndependentHash.isKWiseIndependent_map`: seeded `k`-wise independent
  families induce `k`-wise independent distributions.
* `Cslib.BitString.isKWiseIndependent_uniformOfFintype`: the uniform distribution is `k`-wise
  independent for every `k`.
* `Cslib.BitString.fools_bitVal_of_le`: two one-sided bounds fool a Boolean function.

## References

* [M. Braverman, *Polylogarithmic independence fools `AC⁰` circuits*][Braverman2010]
-/

public section

namespace Cslib.BitString

open Finset Probability
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A distribution `X` on the cube *`ε`-fools* a real function `F` if the expectation of `F` under
`X` is within `ε` of its expectation under the uniform distribution. -/
@[expose] def Fools (X : PMF (ι → Bool)) (ε : ℝ) (F : (ι → Bool) → ℝ) : Prop :=
  |∑ x, (X x).toReal * F x - 𝔼 x, F x| ≤ ε

/-- The expectation under the uniform distribution is the average. -/
theorem sum_uniformOfFintype_mul (F : (ι → Bool) → ℝ) :
    ∑ x, ((PMF.uniformOfFintype (ι → Bool)) x).toReal * F x = 𝔼 x, F x := by
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.expect_eq_sum_div_card, inv_mul_eq_div, sum_div]

/-- The uniform distribution fools every function exactly. -/
theorem fools_uniformOfFintype (F : (ι → Bool) → ℝ) :
    Fools (PMF.uniformOfFintype (ι → Bool)) 0 F := by
  rw [Fools, sum_uniformOfFintype_mul, sub_self, abs_zero]

/-- Fooling with error `ε` implies fooling with any larger error. -/
theorem Fools.mono {X : PMF (ι → Bool)} {ε δ : ℝ} {F : (ι → Bool) → ℝ} (h : Fools X ε F)
    (hεδ : ε ≤ δ) : Fools X δ F :=
  h.trans hεδ

/-- **Two one-sided bounds fool a Boolean function**: if the expectations under `X` of a Boolean
function `F` and of its negation are each at least their uniform expectation minus `ε`, then `X`
`ε`-fools `F` [Braverman, after Lemma 12][Braverman2010]. -/
theorem fools_bitVal_of_le {X : PMF (ι → Bool)} {ε : ℝ} {F : (ι → Bool) → Bool}
    (h : 𝔼 x, bitVal ℝ (F x) - ε ≤ ∑ x, (X x).toReal * bitVal ℝ (F x))
    (hn : 𝔼 x, bitVal ℝ (!F x) - ε ≤ ∑ x, (X x).toReal * bitVal ℝ (!F x)) :
    Fools X ε fun x => bitVal ℝ (F x) := by
  have hne : (univ : Finset (ι → Bool)).Nonempty := univ_nonempty
  simp only [bitVal_not, mul_sub, mul_one, sum_sub_distrib, Probability.PMF.sum_toReal,
    expect_sub_distrib, expect_const hne] at hn
  rw [Fools, abs_le]
  constructor <;> linarith

/-- A distribution on the cube is *`k`-wise independent* if every `k` of its coordinates are
independent and uniform; equivalently, its bias at every nonempty set of at most `k` coordinates
vanishes (`IsKWiseSmallBias.dist_map_restrict_le`), which is the definition used here. -/
abbrev IsKWiseIndependent (k : ℕ) (X : PMF (ι → Bool)) : Prop :=
  IsKWiseSmallBias k 0 X

/-- The expectation of `f` under `X` is the sum over sets `S` of the Fourier coefficient of `f` at
`S` times the bias of `X` at `S`. -/
theorem sum_mul_eq_sum_fourierCoeff_mul_bias (X : PMF (ι → Bool)) (f : (ι → Bool) → ℝ) :
    ∑ x, (X x).toReal * f x = ∑ S, fourierCoeff f S * bias X S := by
  calc ∑ x, (X x).toReal * f x
      = ∑ x, (X x).toReal * ∑ S, fourierCoeff f S * chi ℝ S x := by
        simp only [sum_fourierCoeff_mul_chi]
    _ = ∑ S, fourierCoeff f S * bias X S := by
        simp only [bias, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun S _ => sum_congr rfl fun x _ => by ring

/-- The uniform distribution is `k`-wise independent for every `k`. -/
theorem isKWiseIndependent_uniformOfFintype (k : ℕ) :
    IsKWiseIndependent k (PMF.uniformOfFintype (ι → Bool)) := fun S hS _ => by
  rw [bias_uniformOfFintype, ite_eq_right hS.ne_empty, abs_zero]

namespace IsKWiseIndependent

variable {k : ℕ} {X : PMF (ι → Bool)} {P : (ι → Bool) → ℝ}

/-- A `k`-wise independent distribution gives a function of degree at most `k` its uniform
expectation [Braverman, Proposition 6][Braverman2010]. -/
theorem sum_mul_eq_expect_of_mem_lowDegree (hX : IsKWiseIndependent k X)
    (hP : P ∈ lowDegree ℝ ι k) : ∑ x, (X x).toReal * P x = 𝔼 x, P x := by
  rw [sum_mul_eq_sum_fourierCoeff_mul_bias, ← fourierCoeff_empty, sum_eq_single ∅]
  · rw [bias_empty, mul_one]
  · intro S _ hS
    by_cases hk : #S ≤ k
    · rw [abs_nonpos_iff.1 (hX S (nonempty_iff_ne_empty.2 hS) hk), mul_zero]
    · rw [fourierCoeff_eq_zero_of_mem_lowDegree hP (not_le.1 hk), zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- **`k`-wise independence fools degree-`k` functions exactly**
[Braverman, Proposition 6][Braverman2010]. -/
theorem fools_of_mem_lowDegree (hX : IsKWiseIndependent k X) (hP : P ∈ lowDegree ℝ ι k) :
    Fools X 0 P := by
  rw [Fools, hX.sum_mul_eq_expect_of_mem_lowDegree hP, sub_self, abs_zero]

end IsKWiseIndependent

end Cslib.BitString

namespace Cslib.Probability

open Finset Cslib.BitString
open scoped BigOperators

/-- **Seeded `k`-wise independent families are `k`-wise independent distributions**: a uniformly
random member of a `k`-wise independent family of bit strings is a `k`-wise independent
distribution on the cube. -/
theorem IsKWiseIndependentHash.isKWiseIndependent_map {ι Seed : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype Seed] [Nonempty Seed] {k : ℕ} {h : Seed → ι → Bool}
    (hh : IsKWiseIndependentHash k h) :
    IsKWiseIndependent k ((PMF.uniformOfFintype Seed).map h) := by
  intro S hS hSk
  obtain ⟨i, hi⟩ := hS
  have hzero : 𝔼 b : Bool, signVal b = 0 := by
    simp only [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, signVal_true, signVal_false]
    norm_num
  rw [bias_uniformOfFintype_map]
  simp only [chi_eq_prod_signVal]
  rw [hh.expect_prod hSk fun _ b => signVal b, prod_eq_zero hi hzero, abs_zero]

end Cslib.Probability
