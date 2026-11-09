/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.SignApproximation
public import CslibFrontier.MachineLearning.UniformLearning.Basic
public import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import CslibFrontier.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The low-degree algorithm

The **low-degree algorithm** of Linial, Mansour and Nisan [LinialMansourNisan1993]
[O'Donnell, Section 3.4][ODonnell2014] learns from uniform random examples every Boolean function
whose Fourier spectrum is concentrated on the sets of at most `t` coordinates. From `m` examples
`(x_j, y_j)` it estimates each Fourier coefficient `f̂(S)` with `#S ≤ t` by the empirical average
`c̃(S) = (1 / m) ∑_j y_j χ_S(x_j)`, reading the labels as signs (`UniformLearning.empiricalCoeff`),
and outputs the sign of the truncated expansion `∑_{#S ≤ t} c̃(S) χ_S`
(`UniformLearning.lowDegreeHypothesis`, `UniformLearning.lowDegreeLearner`).

Each `c̃(S)` is an average of `m` independent values in `[-1, 1]` with mean `f̂(S)`, so by
Hoeffding's inequality (`Probability.PMF.uniform_abs_sum_div_sub_expect_ge_le`) it is off by at
least `γ` with probability at most `2 exp (-m γ² / 2)`
(`UniformLearning.uniform_abs_empiricalCoeff_sub_ge_le`). Let `N` be the number of sets of at most
`t` coordinates, at most `(n + 1) ^ t` for `n` coordinates (`BitString.card_filter_card_le_le_pow`).
By the union bound, all `N` estimates are within `γ = √(ε / (2 N))` of their coefficients except
with probability at most `2 N exp (-m ε / (4 N))`, and then rounding the truncated expansion
misclassifies at most a fraction `N γ² + W = ε / 2 + W` of the points, where `W` is the Fourier
weight of `f` above degree `t` (`BitString.hammingDist_signRound_sum_mul_chi_div_le`, by rounding
to the sign as in [O'Donnell, Proposition 3.31][ODonnell2014]). So if `W ≤ ε / 2`, the hypothesis
has error above `ε` with probability at most `2 N exp (-m ε / (4 N))`
(`UniformLearning.uniform_lt_uniformError_lowDegreeHypothesis_le`), which is at most `δ` once
`m ≥ (4 N / ε) log (2 N / δ)` (`UniformLearning.lowDegreeLearner_learns`). The whole argument is
[O'Donnell, Theorem 3.29][ODonnell2014] for the family of sets of at most `t` coordinates.

**Cost.** The algorithm uses `m` examples, computes `N` empirical coefficients, each an average of
`m` characters `χ_S(x_j)` of sets of at most `t` coordinates, so `O (N m t)` arithmetic operations
on the examples, and evaluates its hypothesis at a point with `O (N t)` operations. This count is
informal: the running time is not certified by a machine model here, and the theorems below bound
only the number of examples.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.empiricalCoeff`: the empirical Fourier coefficient of a
  sample of examples.
* `Cslib.MachineLearning.UniformLearning.lowDegreeHypothesis`,
  `Cslib.MachineLearning.UniformLearning.lowDegreeLearner`: the low-degree algorithm.

## Main results

* `Cslib.MachineLearning.UniformLearning.uniform_abs_empiricalCoeff_sub_ge_le`: estimating one
  Fourier coefficient.
* `Cslib.MachineLearning.UniformLearning.uniform_lt_uniformError_lowDegreeHypothesis_le`: the
  failure probability of the low-degree algorithm.
* `Cslib.MachineLearning.UniformLearning.lowDegreeLearner_learns`: the low-degree algorithm learns
  the functions with Fourier weight at most `ε / 2` above degree `t` from
  `(4 N / ε) log (2 N / δ)` examples.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning Cslib.Probability
open scoped BigOperators ENNReal

variable {ι : Type*} {m : ℕ}

/-! ### The algorithm -/

variable [Fintype ι] [DecidableEq ι]

/-- The empirical Fourier coefficient on `S` of a sample of labelled examples `(x_j, y_j)`: the
average of `y_j χ_S(x_j)` over the examples, reading the labels as signs. -/
noncomputable def empiricalCoeff (e : LabeledSample (ι → Bool) Bool m) (S : Finset ι) : ℝ :=
  (∑ j, signVal (e j).2 * chi ℝ S (e j).1) / m

/-- The hypothesis of the low-degree algorithm of degree `t`: the sign of the empirical Fourier
expansion `∑_{#S ≤ t} c̃(S) χ_S` truncated at degree `t`. -/
noncomputable def lowDegreeHypothesis (t : ℕ) (e : LabeledSample (ι → Bool) Bool m) :
    (ι → Bool) → Bool :=
  signRound fun x => ∑ S with #S ≤ t, empiricalCoeff e S * chi ℝ S x

variable (ι) in
/-- **The low-degree algorithm** of degree `t` from `m` examples: estimate the Fourier
coefficients on the sets of at most `t` coordinates empirically, and output the sign of the
truncated expansion. It is a deterministic learner. -/
noncomputable def lowDegreeLearner (t m : ℕ) : Learner (ι → Bool) Bool m :=
  lowDegreeHypothesis t

/-- **Estimating a Fourier coefficient** [O'Donnell, Proposition 3.30][ODonnell2014]: from `m`
uniform random examples of `f`, the empirical coefficient on `S` is off from `f̂(S)` by at least
`γ` with probability at most `2 exp (-m γ² / 2)`, by Hoeffding's inequality. -/
theorem uniform_abs_empiricalCoeff_sub_ge_le (f : (ι → Bool) → Bool) (S : Finset ι)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
      {x | γ ≤ |empiricalCoeff (examples f x) S - fourierCoeff (fun x => signVal (f x)) S|} ≤
        ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) :=
  PMF.uniform_abs_sum_div_sub_expect_ge_le (fun x => signVal (f x) * chi ℝ S x)
    (fun x => by rw [abs_mul, abs_signVal, abs_chi, one_mul]) hγ

/-! ### The low-degree algorithm -/

/-- **The failure probability of the low-degree algorithm.** If the Fourier weight of `f`, read as
signs, on the sets of more than `t` coordinates is at most `ε / 2`, then from `m` uniform random
examples the low-degree hypothesis of degree `t` has error above `ε` with probability at most
`2 N exp (-m ε / (4 N))`, where `N` is the number of sets of at most `t` coordinates. -/
theorem uniform_lt_uniformError_lowDegreeHypothesis_le (f : (ι → Bool) → Bool) (t m : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf : ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2) :
    (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
      {x | ε < uniformError f (lowDegreeHypothesis t (examples f x))} ≤
        ENNReal.ofReal (2 * #{S : Finset ι | #S ≤ t} *
          Real.exp (-(m * ε) / (4 * #{S : Finset ι | #S ≤ t}))) := by
  set T : Finset (Finset ι) := {S : Finset ι | #S ≤ t} with hT
  set N : ℝ := (#T : ℝ)
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (card_filter_card_le_pos t)
  have hN : 0 < N := one_pos.trans_le hN1
  set μ := (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
  set γ := Real.sqrt (ε / (2 * N))
  have hγ : 0 ≤ γ := Real.sqrt_nonneg _
  have hγsq : γ ^ 2 = ε / (2 * N) := Real.sq_sqrt (by positivity)
  -- the samples on which the estimate of the coefficient on `S` is off by at least `γ`
  set bad : Finset ι → Set (Fin m → ι → Bool) := fun S =>
    {x | γ ≤ |empiricalCoeff (examples f x) S - fourierCoeff F S|}
  -- if every estimate is within `γ`, the hypothesis has error at most `ε`
  have hsub :
      {x : Fin m → ι → Bool | ε < uniformError f (lowDegreeHypothesis t (examples f x))} ⊆
        ⋃ S ∈ T, bad S := by
    intro x hx
    by_contra hgood
    simp only [bad, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hgood
    have herr := hammingDist_signRound_sum_mul_chi_div_le f T (empiricalCoeff (examples f x))
    have hcompl : Tᶜ = ({S : Finset ι | t < #S} : Finset (Finset ι)) := by
      rw [hT, compl_filter]
      simp only [not_le]
    rw [hcompl] at herr
    have hest : ∑ S ∈ T, (fourierCoeff F S - empiricalCoeff (examples f x) S) ^ 2 ≤ ε / 2 := by
      calc ∑ S ∈ T, (fourierCoeff F S - empiricalCoeff (examples f x) S) ^ 2
          ≤ ∑ _S ∈ T, γ ^ 2 := sum_le_sum fun S hS => by
            rw [← sq_abs, abs_sub_comm]
            exact pow_le_pow_left₀ (abs_nonneg _) (hgood S hS).le 2
        _ = ε / 2 := by
            rw [sum_const, nsmul_eq_mul, hγsq]
            change N * (ε / (2 * N)) = ε / 2
            field_simp
    have : uniformError f (lowDegreeHypothesis t (examples f x)) ≤ ε := by
      refine herr.trans ?_
      linarith
    exact absurd hx (not_lt.2 this)
  -- the union bound over the `N` estimates
  have hone (S : Finset ι) :
      μ (bad S) ≤ ENNReal.ofReal (2 * Real.exp (-(m * ε) / (4 * N))) := by
    refine (uniform_abs_empiricalCoeff_sub_ge_le f S hγ).trans_eq ?_
    rw [hγsq]
    congr 3
    field_simp
    ring
  calc μ {x : Fin m → ι → Bool | ε < uniformError f (lowDegreeHypothesis t (examples f x))}
      ≤ μ (⋃ S ∈ T, bad S) := μ.mono hsub
    _ ≤ ∑ S ∈ T, μ (bad S) := MeasureTheory.measure_biUnion_finset_le T _
    _ ≤ ∑ _S ∈ T, ENNReal.ofReal (2 * Real.exp (-(m * ε) / (4 * N))) :=
        sum_le_sum fun S _ => hone S
    _ = ENNReal.ofReal (2 * N * Real.exp (-(m * ε) / (4 * N))) := by
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The low-degree algorithm** [LinialMansourNisan1993], [O'Donnell, Section 3.4][ODonnell2014]:
let `N` be the number of sets of at most `t` coordinates (at most `(n + 1) ^ t`,
`BitString.card_filter_card_le_le_pow`). The low-degree algorithm of degree `t` from
`m ≥ (4 N / ε) log (2 N / δ)` uniform random examples learns, with error `ε` and confidence
`1 - δ`, every class of Boolean functions whose Fourier weight, read as signs, on the sets of more
than `t` coordinates is at most `ε / 2`. -/
theorem lowDegreeLearner_learns {t m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : 4 * #{S : Finset ι | #S ≤ t} / ε * Real.log (2 * #{S : Finset ι | #S ≤ t} / δ) ≤ m)
    {C : ConceptClass (ι → Bool) Bool}
    (hC : ∀ f ∈ C, ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ ε / 2) :
    Learns (lowDegreeLearner ι t m) C ε δ := by
  rw [learns_iff]
  intro f hf
  refine (uniform_lt_uniformError_lowDegreeHypothesis_le f t m hε.le (hC f hf)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set N : ℝ := (#{S : Finset ι | #S ≤ t} : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 (card_filter_card_le_pos t)
  have hlog : Real.log (2 * N / δ) ≤ m * ε / (4 * N) := by
    rw [le_div_iff₀ (by positivity)]
    have := (div_mul_eq_mul_div (4 * N) ε (Real.log (2 * N / δ))).symm.trans_le hm
    rw [div_le_iff₀ hε] at this
    linarith
  have hexp : Real.exp (-(m * ε) / (4 * N)) ≤ δ / (2 * N) := by
    calc Real.exp (-(m * ε) / (4 * N)) = Real.exp (-(m * ε / (4 * N))) := by ring_nf
      _ ≤ Real.exp (-Real.log (2 * N / δ)) := Real.exp_le_exp.2 (neg_le_neg hlog)
      _ = δ / (2 * N) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc 2 * N * Real.exp (-(m * ε) / (4 * N)) ≤ 2 * N * (δ / (2 * N)) := by gcongr
    _ = δ := by field_simp

end Cslib.MachineLearning.UniformLearning
