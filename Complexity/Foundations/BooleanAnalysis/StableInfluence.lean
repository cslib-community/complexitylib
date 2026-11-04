/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Noise
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith

/-!
# Stable influences

The `ρ`-*stable influence* of coordinate `i` on a real function `f` is the noise stability of its
derivative, `Infᵢ^{(ρ)}[f] = Stab_ρ[Dᵢ f]` (`BitString.stableInfluence`), and the total
`ρ`-stable influence is their sum (`BitString.totalStableInfluence`)
[O'Donnell, Definition 2.52][ODonnell2014]. In Fourier terms,
`Infᵢ^{(ρ)}[f] = ∑_{S ∋ i} ρ ^ (|S| - 1) f̂(S) ^ 2` (`BitString.stableInfluence_eq_sum`) and
`I^{(ρ)}[f] = ∑_S |S| ρ ^ (|S| - 1) f̂(S) ^ 2` (`BitString.totalStableInfluence_eq_sum`)
[O'Donnell, Fact 2.53][ODonnell2014], so at `ρ = 1` they are the influence and the total
influence (`BitString.stableInfluence_one`, `BitString.totalStableInfluence_one`).

Damping the high degrees caps the total: since `k δ (1 - δ) ^ (k - 1) ≤ 1` for every `k`
[O'Donnell, Exercise 2.45][ODonnell2014], `δ I^{(1 - δ)}[f] ≤ Var[f]` for `0 ≤ δ ≤ 1`
(`BitString.mul_totalStableInfluence_le`). Hence `δ ε N ≤ Var[f]`, where `N` counts the
coordinates of `(1 - δ)`-stable influence at least `ε`
(`BitString.mul_card_filter_le_stableInfluence_le`); for a function of variance at most one, such
as a Boolean function read as signs, at most `1 / (δ ε)` coordinates have `(1 - δ)`-stable
influence at least `ε` [O'Donnell, Proposition 2.54][ODonnell2014], in contrast with ordinary
influences, which can all be large at once.

## Main definitions

* `Cslib.BitString.stableInfluence`, `Cslib.BitString.totalStableInfluence`: the stable
  influences.

## Main results

* `Cslib.BitString.stableInfluence_eq_sum`, `Cslib.BitString.totalStableInfluence_eq_sum`: their
  Fourier formulas.
* `Cslib.BitString.stableInfluence_one`, `Cslib.BitString.totalStableInfluence_one`: at `ρ = 1`
  they are the influence and the total influence.
* `Cslib.BitString.mul_totalStableInfluence_le`,
  `Cslib.BitString.mul_totalStableInfluence_signVal_le_one`: `δ I^{(1 - δ)}[f] ≤ Var[f]`, which is
  at most one for Boolean `f`.
* `Cslib.BitString.mul_card_filter_le_stableInfluence_le`,
  `Cslib.BitString.mul_card_filter_le_stableInfluence_signVal_le_one`: few coordinates have large
  stable influence.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ρ`-stable influence `Infᵢ^{(ρ)}[f] = Stab_ρ[Dᵢ f]` of coordinate `i` on `f`
[O'Donnell, Definition 2.52][ODonnell2014]. -/
noncomputable def stableInfluence (ρ : ℝ) (i : ι) (f : (ι → Bool) → ℝ) : ℝ :=
  noiseStability ρ (derivative i f)

/-- The total `ρ`-stable influence `I^{(ρ)}[f] = ∑ᵢ Infᵢ^{(ρ)}[f]`
[O'Donnell, Definition 2.52][ODonnell2014]. -/
noncomputable def totalStableInfluence (ρ : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ i, stableInfluence ρ i f

/-- **The Fourier formula for the stable influence**:
`Infᵢ^{(ρ)}[f] = ∑_{S ∋ i} ρ ^ (|S| - 1) f̂(S) ^ 2` [O'Donnell, Definition 2.52][ODonnell2014]. -/
theorem stableInfluence_eq_sum (ρ : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    stableInfluence ρ i f = ∑ S with i ∈ S, ρ ^ (#S - 1) * fourierCoeff f S ^ 2 := by
  rw [stableInfluence, noiseStability_eq_sum, sum_filter_mem_eq_sum_filter_notMem i, sum_filter]
  refine sum_congr rfl fun T _ => ?_
  rw [fourierCoeff_derivative]
  split_ifs with hT
  · simp
  · rw [card_insert_of_notMem hT, Nat.add_sub_cancel]

/-- At `ρ = 1` the stable influence is the influence. -/
theorem stableInfluence_one (i : ι) (f : (ι → Bool) → ℝ) :
    stableInfluence 1 i f = influence i f := by
  rw [stableInfluence, noiseStability_one, influence]

/-- Stable influences at a nonnegative rate are nonnegative. -/
theorem stableInfluence_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ι) (f : (ι → Bool) → ℝ) :
    0 ≤ stableInfluence ρ i f := by
  rw [stableInfluence_eq_sum]
  exact sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hρ _) (sq_nonneg _)

/-- At `ρ = 1` the total stable influence is the total influence. -/
theorem totalStableInfluence_one (f : (ι → Bool) → ℝ) :
    totalStableInfluence 1 f = totalInfluence f := by
  simp only [totalStableInfluence, stableInfluence_one, totalInfluence]

/-- The total stable influence at a nonnegative rate is nonnegative. -/
theorem totalStableInfluence_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (f : (ι → Bool) → ℝ) :
    0 ≤ totalStableInfluence ρ f :=
  sum_nonneg fun i _ => stableInfluence_nonneg hρ i f

/-- **The Fourier formula for the total stable influence**:
`I^{(ρ)}[f] = ∑_S |S| ρ ^ (|S| - 1) f̂(S) ^ 2`, the second equality of
[O'Donnell, Fact 2.53][ODonnell2014] written per set rather than per degree. -/
theorem totalStableInfluence_eq_sum (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    totalStableInfluence ρ f = ∑ S, (#S : ℝ) * ρ ^ (#S - 1) * fourierCoeff f S ^ 2 := by
  simp only [totalStableInfluence, stableInfluence_eq_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  ring

/-- `k δ (1 - δ) ^ (k - 1) ≤ 1` for `0 ≤ δ ≤ 1` [O'Donnell, Exercise 2.45][ODonnell2014]: the
`k` terms of the geometric sum `δ ∑_{j < k} (1 - δ) ^ j = 1 - (1 - δ) ^ k` are each at least
`δ (1 - δ) ^ (k - 1)`. -/
private theorem natCast_mul_mul_pow_le_one {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (k : ℕ) :
    k * δ * (1 - δ) ^ (k - 1) ≤ 1 := by
  rcases k with _ | k
  · simp
  have hgeom : (∑ j ∈ range (k + 1), (1 - δ) ^ j) * δ = 1 - (1 - δ) ^ (k + 1) := by
    simpa only [sub_sub_cancel] using geom_sum_mul_neg (1 - δ) (k + 1)
  have hsum : ((k + 1 : ℕ) : ℝ) * (1 - δ) ^ k ≤ ∑ j ∈ range (k + 1), (1 - δ) ^ j := by
    have := sum_le_sum fun j (hj : j ∈ range (k + 1)) =>
      pow_le_pow_of_le_one (by linarith : (0 : ℝ) ≤ 1 - δ) (by linarith)
        (Nat.lt_succ_iff.1 (mem_range.1 hj))
    simpa only [sum_const, card_range, nsmul_eq_mul] using this
  have hpow : 0 ≤ (1 - δ) ^ (k + 1) := pow_nonneg (by linarith) _
  rw [Nat.add_sub_cancel]
  nlinarith [mul_le_mul_of_nonneg_right hsum h₀]

/-- **Damping caps the total stable influence**: for `0 ≤ δ ≤ 1`, `δ I^{(1 - δ)}[f]` is at most the
variance of `f` [O'Donnell, proof of Proposition 2.54][ODonnell2014]. -/
theorem mul_totalStableInfluence_le {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (f : (ι → Bool) → ℝ) :
    δ * totalStableInfluence (1 - δ) f ≤ 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [totalStableInfluence_eq_sum, mul_sum, expect_sub_expect_sq_eq_sum_fourierCoeff_sq, sum_filter]
  refine sum_le_sum fun S _ => ?_
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [hS, ne_eq, not_false_eq_true, ↓reduceIte]
    calc δ * (#S * (1 - δ) ^ (#S - 1) * fourierCoeff f S ^ 2)
        = #S * δ * (1 - δ) ^ (#S - 1) * fourierCoeff f S ^ 2 := by ring
      _ ≤ fourierCoeff f S ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) (natCast_mul_mul_pow_le_one h₀ h₁ _)

/-- **Damping caps the total stable influence of a Boolean function**: read as signs, with
`0 ≤ δ ≤ 1`, `δ I^{(1 - δ)}[f] ≤ 1` [O'Donnell, proof of Proposition 2.54][ODonnell2014]. -/
theorem mul_totalStableInfluence_signVal_le_one {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1)
    (f : (ι → Bool) → Bool) :
    δ * totalStableInfluence (1 - δ) (fun x => signVal (f x)) ≤ 1 :=
  (mul_totalStableInfluence_le h₀ h₁ _).trans (expect_sub_expect_sq_signVal_le_one f)

/-- **Few coordinates have large stable influence**: for `0 ≤ δ ≤ 1` and any `ε`, the number `N`
of coordinates of `(1 - δ)`-stable influence at least `ε` satisfies `δ ε N ≤ Var[f]`. For
`δ, ε > 0` and `Var[f] ≤ 1` this is [O'Donnell, Proposition 2.54][ODonnell2014], `N ≤ 1 / (δ ε)`,
under weaker hypotheses on `δ` and `ε`. -/
theorem mul_card_filter_le_stableInfluence_le {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (ε : ℝ)
    (f : (ι → Bool) → ℝ) :
    δ * ε * #{i | ε ≤ stableInfluence (1 - δ) i f} ≤ 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  have hcount : (#{i | ε ≤ stableInfluence (1 - δ) i f} : ℝ) * ε ≤ totalStableInfluence (1 - δ) f :=
    card_filter_mul_le_sum _ _ _ (fun i _ => stableInfluence_nonneg (sub_nonneg.2 h₁) i f)
      fun _ _ h => h
  calc δ * ε * #{i | ε ≤ stableInfluence (1 - δ) i f}
      = δ * (#{i | ε ≤ stableInfluence (1 - δ) i f} * ε) := by ring
    _ ≤ δ * totalStableInfluence (1 - δ) f := mul_le_mul_of_nonneg_left hcount h₀
    _ ≤ 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := mul_totalStableInfluence_le h₀ h₁ f

/-- **Few coordinates have large stable influence on a Boolean function**: read as signs, with
`0 ≤ δ ≤ 1`, the number `N` of coordinates of `(1 - δ)`-stable influence at least `ε` satisfies
`δ ε N ≤ 1`, so `N ≤ 1 / (δ ε)` for `δ, ε > 0` [O'Donnell, Proposition 2.54][ODonnell2014]. -/
theorem mul_card_filter_le_stableInfluence_signVal_le_one {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1)
    (ε : ℝ) (f : (ι → Bool) → Bool) :
    δ * ε * #{i | ε ≤ stableInfluence (1 - δ) i (fun x => signVal (f x))} ≤ 1 :=
  (mul_card_filter_le_stableInfluence_le h₀ h₁ ε _).trans (expect_sub_expect_sq_signVal_le_one f)

end Cslib.BitString
