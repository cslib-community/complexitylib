/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.MachineLearning.StatisticalQuery.Basic
public import Complexity.Probability.PMF
public import Mathlib.Algebra.BigOperators.Expect
import Complexity.Foundations.BooleanAnalysis.Fourier
import Complexity.MachineLearning.StatisticalQuery.LowerBound

/-!
# Parities are not learnable from statistical queries

Under the uniform distribution on the cube `ι → Bool`, distinct parities `parityOn S` and
`parityOn T` are uncorrelated: their `±1` values are the characters of `S` and `T`, which are
orthonormal (`Cslib.BitString.expect_chi_mul_chi`). With the `2 ^ n` parities as the almost
orthogonal family, `γ = 0`, the statistical query lower bound
(`StatisticalQuery.LearnsStateless.card_le_of_abs_corr_le`) gives the following. A learner that
learns a class containing the parities on `n` bits under the uniform distribution, with
tolerance `τ > 0` and error `ε ∈ [0, 1/2)`, using at most `q` queries, has
`2 ^ n ≤ q / τ ^ 2 + 1 / (1 - 2 ε) ^ 2`
(`StatisticalQuery.LearnsStateless.two_pow_card_le_of_parityOn_mem`). So it needs `2 ^ {Ω(n)}`
queries or tolerance `2 ^ {-Ω(n)}`. This is Kearns's theorem that parities are not efficiently
learnable from statistical queries [Kearns1998, Theorem 5], in the quantitative form of
[BlumEtAl1994].

## Main results

* `Cslib.MachineLearning.StatisticalQuery.corr_uniformOfFintype`: the correlation under the
  uniform distribution as an average.
* `Cslib.MachineLearning.StatisticalQuery.corr_uniformOfFintype_parityOn`: distinct parities are
  uncorrelated.
* `Cslib.MachineLearning.StatisticalQuery.LearnsStateless.two_pow_card_le_of_parityOn_mem`: the
  lower bound for parities.

## References

* [M. Kearns, *Efficient noise-tolerant learning from statistical queries*][Kearns1998]
* [A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour, S. Rudich, *Weakly learning DNF and
  characterizing statistical query learning using Fourier analysis*][BlumEtAl1994]
-/

public section

namespace Cslib.MachineLearning.StatisticalQuery

open Finset Cslib.Probability
open scoped BigOperators

/-- The correlation under the uniform distribution on the cube is the average of the product of
the `±1` values. -/
theorem corr_uniformOfFintype {ι : Type} [Fintype ι] [DecidableEq ι] (f g : (ι → Bool) → Bool) :
    corr (PMF.uniformOfFintype (ι → Bool)) f g =
      𝔼 x, BitString.signVal (f x) * BitString.signVal (g x) := by
  simp only [corr, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.expect_eq_sum_div_card, ← mul_sum, div_eq_inv_mul]

/-- Under the uniform distribution, distinct parities are uncorrelated and a parity has
correlation `1` with itself. -/
theorem corr_uniformOfFintype_parityOn {ι : Type} [Fintype ι] [DecidableEq ι] (S T : Finset ι) :
    corr (PMF.uniformOfFintype (ι → Bool)) (parityOn S) (parityOn T) = if S = T then 1 else 0 := by
  rw [corr_uniformOfFintype]
  simp only [← BitString.chi_eq_signVal_parityOn, BitString.expect_chi_mul_chi]

/-- **Parities are not learnable from statistical queries** [Kearns1998, Theorem 5]
[BlumEtAl1994]. A learner that learns, under the uniform distribution
on `n`-bit strings, a class containing every parity `parityOn S`, with tolerance `τ > 0` and error
`ε ∈ [0, 1/2)` using at most `q` queries, has `2 ^ n ≤ q / τ ^ 2 + 1 / (1 - 2 ε) ^ 2`. -/
theorem LearnsStateless.two_pow_card_le_of_parityOn_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {A : Algorithm (ι → Bool)} {τ ε : ℝ}
    (hA : LearnsStateless A (PMF.uniformOfFintype (ι → Bool)) C τ ε) {q : ℕ}
    (hq : A.IsQueryBounded q) (hC : ∀ S : Finset ι, parityOn S ∈ C) (hτ : 0 < τ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) :
    (2 : ℝ) ^ Fintype.card ι ≤ q / τ ^ 2 + 1 / (1 - 2 * ε) ^ 2 := by
  have hcorr : ∀ S T : Finset ι, S ≠ T →
      |corr (PMF.uniformOfFintype (ι → Bool)) (parityOn S) (parityOn T)| ≤ 0 := by
    intro S T hST
    rw [corr_uniformOfFintype_parityOn, ite_eq_right hST, abs_zero]
  have hβ : 0 < 1 - 2 * ε := by linarith
  have h := hA.card_le_of_abs_corr_le (f := fun S : Finset ι => parityOn S) hq hC hcorr hτ.le
    hε0 hε.le (by positivity) (by positivity)
  calc (2 : ℝ) ^ Fintype.card ι = (Fintype.card (Finset ι) : ℝ) := by
        rw [Fintype.card_finset, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ _ := h
    _ = _ := by rw [sub_zero, sub_zero, sub_zero, mul_one_div]

end Cslib.MachineLearning.StatisticalQuery
