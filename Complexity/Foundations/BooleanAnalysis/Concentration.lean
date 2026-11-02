/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Noise
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Low-degree spectral concentration

The Fourier weight of a function above degree `t` controls how well the low-degree algorithm
learns it (`UniformLearning.lowDegreeLearner_learns`). Two simple quantities bound that weight
[O'Donnell, Section 3.1][ODonnell2014].

**Total influence.** Since `I[f] = ∑_S |S| f̂(S) ^ 2`
(`BitString.totalInfluence_eq_sum_card_mul_fourierCoeff_sq`), the weight above degree `t` is at
most `I[f] / (t + 1)`
(`BitString.add_one_mul_sum_fourierCoeff_sq_le_totalInfluence`), so a function is
`ε`-concentrated up to degree `I[f] / ε` (`BitString.sum_fourierCoeff_sq_le_of_totalInfluence_le`)
[O'Donnell, Proposition 3.2][ODonnell2014].

**Noise sensitivity.** For a Boolean function read as signs `F` and a noise rate `0 ≤ δ ≤ 1/2`,
`NS_δ[f] = ∑_S (1 - (1 - 2 δ) ^ |S|) / 2 F̂(S) ^ 2` (`BitString.noiseSensitivity_eq_sum`), and
above degree `1 / δ` each coefficient's factor is at least `(1 - e⁻²) / 2 ≥ 1 / 3`; so the weight
above degree `t` is at most `3 NS_δ[f]` once `δ (t + 1) ≥ 1`
(`BitString.sum_fourierCoeff_sq_le_three_mul_noiseSensitivity`)
[O'Donnell, Proposition 3.3][ODonnell2014].

## Main results

* `Cslib.BitString.add_one_mul_sum_fourierCoeff_sq_le_totalInfluence`,
  `Cslib.BitString.sum_fourierCoeff_sq_le_of_totalInfluence_le`: concentration from total
  influence.
* `Cslib.BitString.sum_fourierCoeff_sq_le_three_mul_noiseSensitivity`: concentration from noise
  sensitivity.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The weight above degree `t` is at most `I[f] / (t + 1)`**: `t + 1` times the Fourier weight
of `f` on the sets of more than `t` coordinates is at most its total influence. -/
theorem add_one_mul_sum_fourierCoeff_sq_le_totalInfluence (f : (ι → Bool) → ℝ) (t : ℕ) :
    (t + 1) * ∑ S with t < #S, fourierCoeff f S ^ 2 ≤ totalInfluence f := by
  rw [totalInfluence_eq_sum_card_mul_fourierCoeff_sq, mul_sum]
  calc ∑ S with t < #S, (t + 1 : ℝ) * fourierCoeff f S ^ 2
      ≤ ∑ S with t < #S, (#S : ℝ) * fourierCoeff f S ^ 2 :=
        sum_le_sum fun S hS => mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.succ_le_of_lt (mem_filter.1 hS).2) (sq_nonneg _)
    _ ≤ ∑ S, (#S : ℝ) * fourierCoeff f S ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **Concentration from total influence**: if `I[f] ≤ K ≤ ε (t + 1)`, then the Fourier weight of
`f` above degree `t` is at most `ε`; that is, `f` is `ε`-concentrated up to degree `I[f] / ε`
[O'Donnell, Proposition 3.2][ODonnell2014]. -/
theorem sum_fourierCoeff_sq_le_of_totalInfluence_le {f : (ι → Bool) → ℝ} {K ε : ℝ} {t : ℕ}
    (hK : totalInfluence f ≤ K) (ht : K ≤ ε * (t + 1)) :
    ∑ S with t < #S, fourierCoeff f S ^ 2 ≤ ε := by
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < t + 1)
  rw [mul_comm _ ε]
  exact (add_one_mul_sum_fourierCoeff_sq_le_totalInfluence f t).trans (hK.trans ht)

/-- **Concentration from noise sensitivity**: for a Boolean function read as signs and a noise
rate `δ ≤ 1 / 2` with `δ (t + 1) ≥ 1`, the Fourier weight above degree `t` is at most
`3 NS_δ[f]`; that is, `f` is `3 NS_δ[f]`-concentrated up to degree `1 / δ`
[O'Donnell, Proposition 3.3][ODonnell2014]. The book's sharper constant `2 / (1 - e⁻²)` in place
of `3` is not stated separately. -/
theorem sum_fourierCoeff_sq_le_three_mul_noiseSensitivity {δ : ℝ} (hδ : δ ≤ 1 / 2) {t : ℕ}
    (ht : 1 ≤ δ * (t + 1)) (f : (ι → Bool) → Bool) :
    ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤ 3 * noiseSensitivity δ f := by
  have hδ0 : 0 ≤ δ := by nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have h0 : 0 ≤ 1 - 2 * δ := by linarith
  have h1 : 1 - 2 * δ ≤ 1 := by linarith
  have hexp : Real.exp (-2) ≤ 1 / 3 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 2) (by norm_num)]
    linarith [Real.add_one_le_exp 2]
  have key (S : Finset ι) (hS : t < #S) : (1 - 2 * δ) ^ #S ≤ 1 / 3 := by
    calc (1 - 2 * δ) ^ #S ≤ (1 - 2 * δ) ^ (t + 1) :=
          pow_le_pow_of_le_one h0 h1 (Nat.succ_le_of_lt hS)
      _ ≤ Real.exp (-(2 * δ)) ^ (t + 1) :=
          pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (-(2 * δ))]) _
      _ = Real.exp ((t + 1 : ℕ) * -(2 * δ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-2) := Real.exp_le_exp.2 (by push_cast; nlinarith)
      _ ≤ 1 / 3 := hexp
  rw [noiseSensitivity_eq_sum, mul_sum]
  calc ∑ S with t < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2
      ≤ ∑ S with t < #S,
          3 * ((1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2) :=
        sum_le_sum fun S hS => by
          have hk := key S (mem_filter.1 hS).2
          calc fourierCoeff (fun x => signVal (f x)) S ^ 2
              ≤ 3 * (1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2 :=
                le_mul_of_one_le_left (sq_nonneg _) (by linarith)
            _ = 3 * ((1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2) := by
                ring
    _ ≤ ∑ S, 3 * ((1 - (1 - 2 * δ) ^ #S) / 2 * fourierCoeff (fun x => signVal (f x)) S ^ 2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ =>
          mul_nonneg (by norm_num) (mul_nonneg
            (div_nonneg (sub_nonneg.2 (pow_le_one₀ h0 h1)) (by norm_num)) (sq_nonneg _))

end Cslib.BitString
