/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Probability.BitString.Massart

/-!
# Dudley's chaining bound for Rademacher sums

Massart's lemma (`Cslib.BitString.expect_ciSup_sum_mul_signVal_le`) bounds the expected maximum of
the correlations of `N` vectors of norm at most `r` with a uniformly random sign vector by
`r √(2 log N)`. *Chaining* [ShalevShwartzBenDavid2014, Lemma 27.4] [Vershynin2018, Section 8.1]
replaces the single application by one per scale. Approximate each vector `a j` by points of
finite sets `T 0, T 1, …` with error at most `r / 2 ^ n` at level `n`, and write `a j` as its
level-`0` approximation, plus the differences of consecutive approximations, plus the error at
level `K`. A difference at level `n` has norm at most `2 r / 2 ^ n` and ranges over at most
`|T (n + 1)| |T n|` vectors, so Massart's lemma bounds its contribution by
`2 r / 2 ^ n · √(2 log (|T (n + 1)| |T n|))`. The error at level `K` correlates with the signs by at
most `r / 2 ^ K · √|κ|`, by Cauchy–Schwarz.

When the sets `T n` have size polynomial in `2 ^ n`, the terms decay geometrically, so the bound
does not grow with the number of vectors. This is how VC classes obtain Rademacher complexity
`O(√(d / m))` without a logarithmic factor.

## Main results

* `Cslib.BitString.expect_ciSup_sum_mul_signVal_le_chaining`: the truncated chaining bound.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Lemma 27.4
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.1
* [R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian
  processes*][Dudley1967]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.BitString

/-- `(x - y) ^ 2 ≤ 2 (a - x) ^ 2 + 2 (a - y) ^ 2`: the distance between two approximations of `a`
is controlled by their errors. -/
private theorem sq_sub_le_two_mul_sq_add_two_mul_sq (a x y : ℝ) :
    (x - y) ^ 2 ≤ 2 * (a - x) ^ 2 + 2 * (a - y) ^ 2 := by
  nlinarith [sq_nonneg (a - x + (a - y))]

/-- **Dudley's chaining bound** [ShalevShwartzBenDavid2014, Lemma 27.4]: let the vectors
`a j : κ → ℝ`, `j : ι`, have Euclidean norm at most `r`, and let every `a j` lie within Euclidean
distance `r / 2 ^ n` of a point of the finite set `T n`, for every level `n`. Then for every
`K`, the expected maximum of their correlations with a uniformly random sign vector is at most
`2 r √(2 log |T 0|) + ∑_{n < K} 2 r / 2 ^ n · √(2 log (|T (n + 1)| |T n|)) + r / 2 ^ K · √|κ|`.

The index type `ι` need not be finite; only the sets `T n` are. The source takes `T 0 = {0}`, so
that its first term vanishes, and bounds the differences at level `n` by `3 r / 2 ^ n` through the
triangle inequality. -/
theorem expect_ciSup_sum_mul_signVal_le_chaining {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : ι → κ → ℝ) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ r ^ 2)
    (T : ℕ → Finset (κ → ℝ))
    (hT : ∀ n j, ∃ u ∈ T n, ∑ i, (a j i - u i) ^ 2 ≤ (r / 2 ^ n) ^ 2) (K : ℕ) :
    𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i) ≤
      2 * r * √(2 * Real.log (T 0).card) +
        ∑ n ∈ range K, 2 * r / 2 ^ n * √(2 * Real.log ((T (n + 1)).card * (T n).card)) +
          r / 2 ^ K * √(Fintype.card κ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty, expect_const_zero]
    have h2 : ∀ n : ℕ, 0 ≤ 2 * r / 2 ^ n := fun n => by positivity
    exact add_nonneg (add_nonneg (by positivity)
      (sum_nonneg fun n _ => mul_nonneg (h2 n) (Real.sqrt_nonneg _))) (by positivity)
  have j₀ : ι := Classical.arbitrary ι
  choose p hpT hpa using hT
  -- The level-`0` approximations, and the differences of consecutive approximations, as finite
  -- families of vectors of controlled norm.
  set L₀ : Finset (κ → ℝ) := (T 0).filter fun u => ∑ i, u i ^ 2 ≤ (2 * r) ^ 2
  set L : ℕ → Finset ((κ → ℝ) × (κ → ℝ)) := fun n =>
    (T (n + 1) ×ˢ T n).filter fun q => ∑ i, (q.1 i - q.2 i) ^ 2 ≤ (2 * r / 2 ^ n) ^ 2
  have hp0 : ∀ j, p 0 j ∈ L₀ := by
    intro j
    refine mem_filter.2 ⟨hpT 0 j, ?_⟩
    have h0 := hpa 0 j
    rw [pow_zero, div_one] at h0
    calc ∑ i, p 0 j i ^ 2 ≤ ∑ i, (2 * (a j i - p 0 j i) ^ 2 + 2 * a j i ^ 2) :=
          sum_le_sum fun i _ => by
            simpa using sq_sub_le_two_mul_sq_add_two_mul_sq (a j i) (p 0 j i) 0
      _ = 2 * ∑ i, (a j i - p 0 j i) ^ 2 + 2 * ∑ i, a j i ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ (2 * r) ^ 2 := by linarith [h0, ha j]
  have hpL : ∀ n j, (p (n + 1) j, p n j) ∈ L n := by
    intro n j
    refine mem_filter.2 ⟨mem_product.2 ⟨hpT (n + 1) j, hpT n j⟩, ?_⟩
    calc ∑ i, (p (n + 1) j i - p n j i) ^ 2
        ≤ ∑ i, (2 * (a j i - p (n + 1) j i) ^ 2 + 2 * (a j i - p n j i) ^ 2) :=
          sum_le_sum fun i _ => sq_sub_le_two_mul_sq_add_two_mul_sq _ _ _
      _ = 2 * ∑ i, (a j i - p (n + 1) j i) ^ 2 + 2 * ∑ i, (a j i - p n j i) ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ 2 * ((r / 2 ^ n) ^ 2 / 4) + 2 * (r / 2 ^ n) ^ 2 := by
          have hX : (r / 2 ^ (n + 1)) ^ 2 = (r / 2 ^ n) ^ 2 / 4 := by ring
          linarith [hpa (n + 1) j, hpa n j]
      _ ≤ (2 * r / 2 ^ n) ^ 2 := by
          rw [show (2 * r / 2 ^ n) ^ 2 = 4 * (r / 2 ^ n) ^ 2 by ring]
          linarith [sq_nonneg (r / 2 ^ n)]
  -- The maxima over the level-`0` family and over the families of differences.
  set A : (κ → Bool) → ℝ := fun σ => ⨆ u : L₀, ∑ i, (u : κ → ℝ) i * signVal (σ i) with hA
  set B : ℕ → (κ → Bool) → ℝ := fun n σ =>
    ⨆ q : L n, ∑ i, ((q : (κ → ℝ) × (κ → ℝ)).1 i - (q : (κ → ℝ) × (κ → ℝ)).2 i) *
      signVal (σ i) with hB
  have hA_le (σ : κ → Bool) (j : ι) : ∑ i, p 0 j i * signVal (σ i) ≤ A σ :=
    le_ciSup (f := fun u : L₀ => ∑ i, (u : κ → ℝ) i * signVal (σ i))
      (Set.finite_range _).bddAbove ⟨p 0 j, hp0 j⟩
  have hB_le (n : ℕ) (σ : κ → Bool) (j : ι) :
      ∑ i, (p (n + 1) j i - p n j i) * signVal (σ i) ≤ B n σ :=
    le_ciSup (f := fun q : L n =>
        ∑ i, ((q : (κ → ℝ) × (κ → ℝ)).1 i - (q : (κ → ℝ) × (κ → ℝ)).2 i) * signVal (σ i))
      (Set.finite_range _).bddAbove ⟨(p (n + 1) j, p n j), hpL n j⟩
  -- The error at level `K`, by Cauchy–Schwarz.
  have hres (σ : κ → Bool) (j : ι) :
      ∑ i, (a j i - p K j i) * signVal (σ i) ≤ r / 2 ^ K * √(Fintype.card κ) := by
    have hs : ∑ i, signVal (σ i) ^ 2 = Fintype.card κ := by simp [sq, signVal_mul_self]
    calc ∑ i, (a j i - p K j i) * signVal (σ i)
        ≤ √(∑ i, (a j i - p K j i) ^ 2) * √(∑ i, signVal (σ i) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ √((r / 2 ^ K) ^ 2) * √(Fintype.card κ) := by
          rw [hs]
          gcongr
          exact hpa K j
      _ = r / 2 ^ K * √(Fintype.card κ) := by rw [Real.sqrt_sq (by positivity)]
  -- Each correlation splits along the chain.
  have hdecomp (σ : κ → Bool) (j : ι) : ∑ i, a j i * signVal (σ i) =
      ∑ i, p 0 j i * signVal (σ i) +
        ∑ n ∈ range K, ∑ i, (p (n + 1) j i - p n j i) * signVal (σ i) +
          ∑ i, (a j i - p K j i) * signVal (σ i) := by
    have htel := sum_range_sub (fun n => ∑ i, p n j i * signVal (σ i)) K
    simp only [sub_mul, sum_sub_distrib] at htel ⊢
    linarith
  have hpt (σ : κ → Bool) : ⨆ j, ∑ i, a j i * signVal (σ i) ≤
      A σ + ∑ n ∈ range K, B n σ + r / 2 ^ K * √(Fintype.card κ) :=
    ciSup_le fun j => (hdecomp σ j).trans_le <| add_le_add (add_le_add (hA_le σ j)
      (sum_le_sum fun n _ => hB_le n σ j)) (hres σ j)
  -- Massart's lemma at each level.
  have hEA : 𝔼 σ : κ → Bool, A σ ≤ 2 * r * √(2 * Real.log (T 0).card) := by
    refine (expect_ciSup_sum_mul_signVal_le (fun u : L₀ => (u : κ → ℝ)) (by positivity)
      fun u => (mem_filter.1 u.2).2).trans ?_
    have hlog : Real.log (Fintype.card L₀) ≤ Real.log (T 0).card := by
      rw [Fintype.card_coe]
      exact Real.log_le_log (by exact_mod_cast card_pos.2 ⟨_, hp0 j₀⟩)
        (by exact_mod_cast card_filter_le _ _)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)
  have hEB (n : ℕ) : 𝔼 σ : κ → Bool, B n σ ≤
      2 * r / 2 ^ n * √(2 * Real.log ((T (n + 1)).card * (T n).card)) := by
    refine (expect_ciSup_sum_mul_signVal_le
      (fun q : L n => fun i => (q : (κ → ℝ) × (κ → ℝ)).1 i - (q : (κ → ℝ) × (κ → ℝ)).2 i)
      (by positivity) fun q => (mem_filter.1 q.2).2).trans ?_
    have hlog : Real.log (Fintype.card (L n)) ≤ Real.log ((T (n + 1)).card * (T n).card) := by
      rw [Fintype.card_coe]
      refine Real.log_le_log (by exact_mod_cast card_pos.2 ⟨_, hpL n j₀⟩) ?_
      exact_mod_cast (card_filter_le _ _).trans (card_product _ _).le
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity)
  calc 𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i)
      ≤ 𝔼 σ : κ → Bool, (A σ + ∑ n ∈ range K, B n σ + r / 2 ^ K * √(Fintype.card κ)) :=
        expect_le_expect fun σ _ => hpt σ
    _ = 𝔼 σ : κ → Bool, A σ + ∑ n ∈ range K, 𝔼 σ : κ → Bool, B n σ +
          r / 2 ^ K * √(Fintype.card κ) := by
        rw [expect_add_distrib, expect_add_distrib, expect_sum_comm, expect_const univ_nonempty]
    _ ≤ _ := add_le_add (add_le_add hEA (sum_le_sum fun n _ => hEB n)) le_rfl

end Cslib.BitString
