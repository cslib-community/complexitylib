/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
import CslibFrontier.Foundations.BooleanAnalysis.FourierDegree

/-!
# Low-degree Boolean functions have few relevant coordinates

A coordinate `i` is *relevant* to a Boolean function `f` when flipping bit `i` changes the value of
`f` on some input; read as signs, this is exactly when the influence of `i` on `f` is nonzero
(`BitString.influence_signVal_ne_zero_iff`). A Boolean function of degree at most `d` has at most
`d * 2 ^ (d - 1)` relevant coordinates (`BitString.card_filter_influence_ne_zero_le`,
`BitString.card_filter_exists_update_ne_le`) [NisanSzegedy1994]
[O'Donnell, Chapter 3][ODonnell2014]. The other bound of the same paper, `bs(f) ≤ 2 deg(f)²`, is
`QueryComplexity.blockSensitivity_le_two_mul_degree_sq`.

The degree hypothesis is that `f`, read as signs, lies in `BitString.lowDegree ℝ ι d`, equivalently
that its Fourier coefficients vanish on the sets of more than `d` coordinates
(`BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`). For `f : BooleanFunction n` it holds with
`d = QueryComplexity.degree f` (`QueryComplexity.degree_le_iff_mem_lowDegree`,
`BitString.signVal_comp_mem_lowDegree_iff`), and for a function computed by a decision tree of
depth `d` (`DecisionTree.comp_eval_mem_lowDegree`).

The influence of `i` is the density of the points where the derivative in `i` is nonzero
(`BitString.influence_signVal_eq_dens`), and this derivative has degree at most `d - 1`. By
Schwartz–Zippel on the cube, a nonzero influence is therefore at least `2 ^ (1 - d)`
(`BitString.one_le_two_pow_mul_influence_of_degree`), while the influences sum to at most `d`
(`BitString.totalInfluence_signVal_le_of_degree`).

## Main results

* `Cslib.BitString.one_le_two_pow_mul_influence_of_degree`,
  `Cslib.BitString.one_le_two_pow_mul_influence_of_fourierCoeff_eq_zero`: granularity of the
  influences of a low-degree Boolean function.
* `Cslib.BitString.card_filter_influence_ne_zero_le`,
  `Cslib.BitString.card_filter_influence_ne_zero_le_of_fourierCoeff_eq_zero`,
  `Cslib.BitString.card_filter_exists_update_ne_le`,
  `Cslib.BitString.card_filter_exists_update_ne_le_of_fourierCoeff_eq_zero`: the Nisan–Szegedy bound
  on the number of relevant coordinates.

## References

* [N. Nisan and M. Szegedy, *On the Degree of Boolean Functions as Real
  Polynomials*][NisanSzegedy1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Granularity of influences**, Fourier-coefficient form: a nonzero influence of a Boolean
function whose Fourier coefficients, read as signs, vanish above degree `d` is at least
`2 ^ (1 - d)`. -/
theorem one_le_two_pow_mul_influence_of_fourierCoeff_eq_zero (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) (i : ι)
    (hi : influence i (fun x => signVal (f x)) ≠ 0) :
    1 ≤ 2 ^ (d - 1) * influence i (fun x => signVal (f x)) := by
  have hdeg' (T : Finset ι) (hT : d - 1 < #T) :
      fourierCoeff (derivative i fun x => signVal (f x)) T = 0 := by
    rw [fourierCoeff_derivative]
    split_ifs with hiT
    · rfl
    · exact hdeg _ (by rw [card_insert_of_notMem hiT]; omega)
  have hne : derivative i (fun x => signVal (f x)) ≠ 0 := by
    intro h0
    apply hi
    simp [influence, h0]
  rw [influence_signVal_eq_dens]
  exact one_le_two_pow_mul_dens_ne_zero_of_fourierCoeff_eq_zero _ hdeg' hne

/-- **Granularity of influences**: a nonzero influence of a Boolean function of degree at most `d`,
read as signs, is at least `2 ^ (1 - d)`. -/
theorem one_le_two_pow_mul_influence_of_degree (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : (fun x => signVal (f x)) ∈ lowDegree ℝ ι d) (i : ι)
    (hi : influence i (fun x => signVal (f x)) ≠ 0) :
    1 ≤ 2 ^ (d - 1) * influence i (fun x => signVal (f x)) :=
  one_le_two_pow_mul_influence_of_fourierCoeff_eq_zero f
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hdeg) i hi

/-- **The Nisan–Szegedy bound**, in terms of influences: a Boolean function of degree at most `d`,
read as signs, has at most `d * 2 ^ (d - 1)` coordinates of nonzero influence [NisanSzegedy1994]. -/
theorem card_filter_influence_ne_zero_le (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : (fun x => signVal (f x)) ∈ lowDegree ℝ ι d) :
    #{i | influence i (fun x => signVal (f x)) ≠ 0} ≤ d * 2 ^ (d - 1) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set R : Finset ι := {i | influence i F ≠ 0}
  have hpow : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
  have h : (#R : ℝ) ≤ d * 2 ^ (d - 1) :=
    calc (#R : ℝ) = ∑ i ∈ R, (1 : ℝ) := by rw [sum_const, nsmul_one]
      _ ≤ ∑ i ∈ R, 2 ^ (d - 1) * influence i F :=
          sum_le_sum fun i hi => one_le_two_pow_mul_influence_of_degree f hdeg i (mem_filter.1 hi).2
      _ ≤ ∑ i, 2 ^ (d - 1) * influence i F :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ =>
            mul_nonneg hpow (influence_nonneg i F)
      _ = 2 ^ (d - 1) * totalInfluence F := by rw [totalInfluence, mul_sum]
      _ ≤ 2 ^ (d - 1) * d :=
          mul_le_mul_of_nonneg_left (totalInfluence_signVal_le_of_degree f hdeg) hpow
      _ = d * 2 ^ (d - 1) := mul_comm _ _
  exact_mod_cast h

/-- **The Nisan–Szegedy bound**, in terms of influences and Fourier coefficients: a Boolean
function whose Fourier coefficients, read as signs, vanish above degree `d` has at most
`d * 2 ^ (d - 1)` coordinates of nonzero influence [NisanSzegedy1994]. -/
theorem card_filter_influence_ne_zero_le_of_fourierCoeff_eq_zero (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) :
    #{i | influence i (fun x => signVal (f x)) ≠ 0} ≤ d * 2 ^ (d - 1) :=
  card_filter_influence_ne_zero_le f (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hdeg)

/-- **The Nisan–Szegedy bound on relevant coordinates**: a Boolean function of degree at most `d`,
read as signs, has at most `d * 2 ^ (d - 1)` coordinates whose flip changes its value on some input
[NisanSzegedy1994]. -/
theorem card_filter_exists_update_ne_le (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : (fun x => signVal (f x)) ∈ lowDegree ℝ ι d) :
    #{i | ∃ x, f (update x i !x i) ≠ f x} ≤ d * 2 ^ (d - 1) := by
  rw [filter_congr fun i _ => (influence_signVal_ne_zero_iff f i).symm]
  exact card_filter_influence_ne_zero_le f hdeg

/-- **The Nisan–Szegedy bound on relevant coordinates**, Fourier-coefficient form: a Boolean
function whose Fourier coefficients, read as signs, vanish above degree `d` has at most
`d * 2 ^ (d - 1)` coordinates whose flip changes its value on some input [NisanSzegedy1994]. -/
theorem card_filter_exists_update_ne_le_of_fourierCoeff_eq_zero (f : (ι → Bool) → Bool) {d : ℕ}
    (hdeg : ∀ S : Finset ι, d < #S → fourierCoeff (fun x => signVal (f x)) S = 0) :
    #{i | ∃ x, f (update x i !x i) ≠ f x} ≤ d * 2 ^ (d - 1) :=
  card_filter_exists_update_ne_le f (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hdeg)

end Cslib.BitString
