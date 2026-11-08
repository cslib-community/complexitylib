/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PropertyTesting.Distribution.ClosenessCollision
public import Complexity.Probability.Split
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Probability.PMF

/-!
# The closeness tester by flattening

Testing whether two unknown distributions `p, q` on `n` points are equal or at statistical distance
at least `ε` takes `Θ(n^{2/3} ε^{-4/3} + √n ε^{-2})` samples [Chan–Diakonikolas–Valiant–Valiant]
[ChanDiakonikolasValiantValiant2014]. This file proves the upper bound with explicit constants by
the flattening reduction of [Diakonikolas–Kane, Proposition 2.10][DiakonikolasKane2016]
(numbering of arXiv:1601.05557v1): split both distributions along the occurrences of a first batch
of samples, which makes both of their collision probabilities small
(`Complexity.Probability.Split`), then run the `ℓ₂` closeness tester `closenessTester` on the split
distributions.

`closenessFlatteningTester m k ε` draws `m + k` samples `x, y` of each distribution. The first `m`
samples `x₁, y₁` of each fix the counts `c a = N_a(x₁) + N_a(y₁)` (`flatteningCount`), so that
`∑ c = 2m` and the split domain `Σ a, Fin (c a + 1)` has `n + 2m` points. The other `k` samples of
each are passed independently through the split kernel and tested by
`closenessTester k (2 ε / √(n + 2m))` (`splitClosenessTester`).

* Conditioned on `x₁, y₁`, the tester accepts with the probability that the `ℓ₂` tester accepts the
  split distributions (`acceptProb₂_closenessFlatteningTester`); splitting preserves statistical
  distance, and Cauchy–Schwarz on `n + 2m` points turns statistical distance `ε` into squared
  `ℓ₂` distance `4 ε² / (n + 2m)`.
* The collision probability of `split p c` is at most that of the split along `x₁` alone, which has
  expectation at most `1 / (m + 1)`; likewise for `q` and `y₁`. Markov's inequality at the level
  `16 / (m + 1)` costs probability `1 / 16` for each.
* On the good event, the `ℓ₂` tester with `b = 16 / (m + 1)` and error `δ = 5 / 24` needs
  `36 √b ≤ (k - 1) (4 ε² / (n + 2m)) δ`, which is `864 (n + 2m) ≤ 5 (k - 1) ε² √(m + 1)`.
  The total error is then at most `5 / 24 + 1 / 8 = 1 / 3`
  (`isClosenessTester_closenessFlatteningTester`).

Taking `m = ⌈t⌉` for `t = min(n, n^{2/3} ε^{-4/3})` gives
`m + k ≤ 520 max(n^{2/3} ε^{-4/3}, √n ε^{-2}) + 3`
(`exists_isClosenessTester_closenessFlatteningTester`).

The tester deviates from [Diakonikolas–Kane, Proposition 2.10][DiakonikolasKane2016] in two ways,
both to stay within the fixed-sample model of `acceptProb₂`. It takes a fixed number `m` of
flattening samples instead of a Poisson number. It also flattens with samples of both `p` and `q`
rather than of `q` alone, so that both split collision probabilities are small. This replaces
[Diakonikolas–Kane, Lemma 2.3][DiakonikolasKane2016], which needs only one of the two norms to be
small but estimates both norms first. Statistical distance `dist` is half the `ℓ₁` distance, so
proximity `ε` here is `‖p - q‖₁ ≥ 2 ε` in the notation of the paper.

## Main definitions

* `Cslib.DistributionTesting.flatteningCount`: the split counts from both flattening samples.
* `Cslib.DistributionTesting.splitClosenessTester`: the `ℓ₂` closeness tester on split samples.
* `Cslib.DistributionTesting.closenessFlatteningTester`: the closeness tester by flattening.

## Main results

* `Cslib.DistributionTesting.acceptProb₂_closenessFlatteningTester`: the acceptance probability
  as an average over the flattening samples.
* `Cslib.DistributionTesting.isClosenessTester_closenessFlatteningTester`: the tester is a
  closeness tester once `864 (n + 2m) ≤ 5 (k - 1) ε² √(m + 1)`.
* `Cslib.DistributionTesting.isClosenessTester_closenessFlatteningTester_ceil`: the parameters
  `m = ⌈t⌉`, `k = ⌈2592 n / (5 ε² √t)⌉ + 1` for any `0 < t ≤ n`.
* `Cslib.DistributionTesting.exists_isClosenessTester_closenessFlatteningTester`: the sample
  complexity `O(n^{2/3} ε^{-4/3} + √n ε^{-2})`.

## References

* [S.-O. Chan, I. Diakonikolas, G. Valiant and P. Valiant, *Optimal algorithms for testing
  closeness of discrete distributions*][ChanDiakonikolasValiantValiant2014]
* [I. Diakonikolas and D. M. Kane, *A new approach for testing properties of discrete
  distributions*][DiakonikolasKane2016]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The flattening counts: the number of occurrences of `a` in the flattening samples `x` and `y`
together. -/
def flatteningCount {m : ℕ} (x y : Fin m → α) (a : α) : ℕ :=
  occurrenceCount x a + occurrenceCount y a

omit [Fintype α] in
/-- Unfolding lemma for `flatteningCount`. -/
theorem flatteningCount_apply {m : ℕ} (x y : Fin m → α) (a : α) :
    flatteningCount x y a = occurrenceCount x a + occurrenceCount y a := by
  rw [flatteningCount]

/-- The flattening counts add up to `2 m`. -/
theorem sum_flatteningCount {m : ℕ} (x y : Fin m → α) : ∑ a, flatteningCount x y a = 2 * m := by
  simp only [flatteningCount, sum_add_distrib, sum_occurrenceCount]
  ring

omit [DecidableEq α] in
variable (α) in
/-- The `ℓ₂` proximity `2 ε / √(n + 2m)` on the split domain of `n + 2m` points. -/
noncomputable def flatteningProximity (m : ℕ) (ε : ℝ) : ℝ :=
  2 * ε / Real.sqrt (Fintype.card α + 2 * m)

omit [DecidableEq α] in
/-- Unfolding lemma for `flatteningProximity`. -/
theorem flatteningProximity_eq (m : ℕ) (ε : ℝ) :
    flatteningProximity α m ε = 2 * ε / Real.sqrt (Fintype.card α + 2 * m) := by
  rw [flatteningProximity]

/-- The `ℓ₂` closeness tester run on the samples passed independently through the split kernel. -/
noncomputable def splitClosenessTester (c : α → ℕ) (k : ℕ) (ε : ℝ) :
    (Fin k → α) → (Fin k → α) → PMF Bool := fun x y =>
  (pi fun i => splitKernel c (x i)).bind fun x' =>
    (pi fun i => splitKernel c (y i)).bind fun y' => closenessTester k ε x' y'

/-- The split tester accepts `p, q` with the probability that the `ℓ₂` tester accepts the split
distributions. -/
theorem acceptProb₂_splitClosenessTester (c : α → ℕ) (k : ℕ) (ε : ℝ) (p q : PMF α) :
    acceptProb₂ (splitClosenessTester c k ε) p q =
      acceptProb₂ (closenessTester k ε) (split p c) (split q c) := by
  rw [split_eq_bind, split_eq_bind, ← acceptProb₂_bind_pi]
  rfl

/-- **The closeness tester by flattening.** Of the `m + k` samples of each distribution, the first
`m` of both fix the split counts, and the other `k` of each are split and tested by the `ℓ₂`
closeness tester with proximity `2 ε / √(n + 2m)`. -/
noncomputable def closenessFlatteningTester (m k : ℕ) (ε : ℝ) :
    (Fin (m + k) → α) → (Fin (m + k) → α) → PMF Bool := fun x y =>
  splitClosenessTester (flatteningCount (fun j => x (Fin.castAdd k j))
      (fun j => y (Fin.castAdd k j))) k (flatteningProximity α m ε)
    (fun i => x (Fin.natAdd m i)) (fun i => y (Fin.natAdd m i))

/-- Unfolding lemma for `closenessFlatteningTester`. -/
theorem closenessFlatteningTester_apply (m k : ℕ) (ε : ℝ) (x y : Fin (m + k) → α) :
    closenessFlatteningTester m k ε x y =
      splitClosenessTester (flatteningCount (fun j => x (Fin.castAdd k j))
          (fun j => y (Fin.castAdd k j))) k (flatteningProximity α m ε)
        (fun i => x (Fin.natAdd m i)) (fun i => y (Fin.natAdd m i)) := by
  rw [closenessFlatteningTester]

/-- The acceptance probability of the flattening tester averages, over the flattening samples
`x₁, y₁`, the acceptance probability of the `ℓ₂` tester on the distributions split along `x₁, y₁`.
-/
theorem acceptProb₂_closenessFlatteningTester (m k : ℕ) (ε : ℝ) (p q : PMF α) :
    acceptProb₂ (closenessFlatteningTester m k ε) p q =
      ∑ x₁, ∑ y₁, (iid p m x₁).toReal * (iid q m y₁).toReal *
        acceptProb₂ (closenessTester k (flatteningProximity α m ε))
          (split p (flatteningCount x₁ y₁)) (split q (flatteningCount x₁ y₁)) := by
  rw [acceptProb₂_append]
  refine sum_congr rfl fun x₁ _ => ?_
  refine sum_congr rfl fun y₁ _ => ?_
  rw [← acceptProb₂_splitClosenessTester]
  simp only [closenessFlatteningTester_apply, Fin.append_left, Fin.append_right]

section Averaging

variable {m : ℕ} (p q : PMF α)

omit [DecidableEq α] in
private theorem sum_sum_iid_mul_add (R S : (Fin m → α) → ℝ) :
    ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * (R x + S y) =
      ∑ x, (iid p m x).toReal * R x + ∑ y, (iid q m y).toReal * S y := by
  simp only [mul_add, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun x _ => ?_
    rw [← sum_mul, ← mul_sum, sum_toReal, mul_one]
  · rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_mul, ← sum_mul, sum_toReal, one_mul]

omit [DecidableEq α] in
private theorem sum_sum_iid_mul_sub_div (a b : ℝ) (T : (Fin m → α) → (Fin m → α) → ℝ) :
    ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * (a - T x y / b) =
      a - (∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * T x y) / b := by
  have h1 : ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * a = a := by
    simp only [← sum_mul, ← mul_sum, sum_toReal, mul_one, one_mul]
  conv_rhs => rw [← h1]
  rw [sum_div, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_div, ← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq α] in
/-- Markov's inequality for a pointwise lower bound `a - (R x + S y) / b`. -/
private theorem le_sum_sum (A : (Fin m → α) → (Fin m → α) → ℝ) (R S : (Fin m → α) → ℝ)
    {a b r s : ℝ} (hb : 0 < b) (hR : ∑ x, (iid p m x).toReal * R x ≤ r)
    (hS : ∑ y, (iid q m y).toReal * S y ≤ s) (hA : ∀ x y, a - (R x + S y) / b ≤ A x y) :
    a - (r + s) / b ≤ ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * A x y := by
  calc a - (r + s) / b
      ≤ a - (∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * (R x + S y)) / b := by
        rw [sum_sum_iid_mul_add]
        gcongr
    _ = ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * (a - (R x + S y) / b) :=
        (sum_sum_iid_mul_sub_div p q a b _).symm
    _ ≤ _ := sum_le_sum fun x _ => sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hA x y) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

omit [DecidableEq α] in
/-- Markov's inequality for a pointwise upper bound `a + (R x + S y) / b`. -/
private theorem sum_sum_le (A : (Fin m → α) → (Fin m → α) → ℝ) (R S : (Fin m → α) → ℝ)
    {a b r s : ℝ} (hb : 0 < b) (hR : ∑ x, (iid p m x).toReal * R x ≤ r)
    (hS : ∑ y, (iid q m y).toReal * S y ≤ s) (hA : ∀ x y, A x y ≤ a + (R x + S y) / b) :
    ∑ x, ∑ y, (iid p m x).toReal * (iid q m y).toReal * A x y ≤ a + (r + s) / b := by
  have h := le_sum_sum p q (fun x y => -A x y) R S hb hR hS (a := -a)
    (fun x y => by have := hA x y; linarith)
  simp only [mul_neg, sum_neg_distrib] at h
  linarith

end Averaging

/-- Completeness after flattening, pointwise in the flattening samples: the `ℓ₂` tester accepts
`split p c` against itself with probability at least `1 - δ`, unless a split collision probability
exceeds `b`. -/
private theorem le_acceptProb₂_split {m k : ℕ} {ε δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hk : 36 * Real.sqrt b ≤ (k - 1) * flatteningProximity α m ε ^ 2 * δ) (p : PMF α)
    (x y : Fin m → α) :
    1 - δ - (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split p (occurrenceCount y))) / b ≤
      acceptProb₂ (closenessTester k (flatteningProximity α m ε))
        (split p (flatteningCount x y)) (split p (flatteningCount x y)) := by
  have hx : collisionProbability (split p (flatteningCount x y)) ≤
      collisionProbability (split p (occurrenceCount x)) :=
    collisionProbability_split_antitone p fun i => Nat.le_add_right _ _
  have hx0 := collisionProbability_pos (split p (occurrenceCount x))
  have hy0 := collisionProbability_pos (split p (occurrenceCount y))
  by_cases h : collisionProbability (split p (flatteningCount x y)) ≤ b
  · have h1 := le_acceptProb₂_closenessTester hδ h h hk
      (by simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sum_const_zero]; positivity)
    have h2 : 0 ≤ (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split p (occurrenceCount y))) / b := by positivity
    linarith
  · have h1 : 1 < (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split p (occurrenceCount y))) / b := by
      rw [lt_div_iff₀ hb]
      linarith [not_le.mp h]
    have := acceptProb₂_nonneg (closenessTester k (flatteningProximity α m ε))
      (split p (flatteningCount x y)) (split p (flatteningCount x y))
    linarith

/-- Soundness after flattening, pointwise in the flattening samples: for `p, q` at statistical
distance at least `ε`, the `ℓ₂` tester accepts the split distributions with probability at most
`δ`, unless a split collision probability exceeds `b`. -/
private theorem acceptProb₂_split_le {m k : ℕ} {ε δ b : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hb : 0 < b) (hk : 36 * Real.sqrt b ≤ (k - 1) * flatteningProximity α m ε ^ 2 * δ)
    {p q : PMF α} (hpq : ε ≤ dist p q) (x y : Fin m → α) :
    acceptProb₂ (closenessTester k (flatteningProximity α m ε))
        (split p (flatteningCount x y)) (split q (flatteningCount x y)) ≤
      δ + (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split q (occurrenceCount y))) / b := by
  have hx : collisionProbability (split p (flatteningCount x y)) ≤
      collisionProbability (split p (occurrenceCount x)) :=
    collisionProbability_split_antitone p fun i => Nat.le_add_right _ _
  have hy : collisionProbability (split q (flatteningCount x y)) ≤
      collisionProbability (split q (occurrenceCount y)) :=
    collisionProbability_split_antitone q fun i => Nat.le_add_left _ _
  have hx0 := collisionProbability_pos (split p (occurrenceCount x))
  have hy0 := collisionProbability_pos (split q (occurrenceCount y))
  by_cases h : collisionProbability (split p (flatteningCount x y)) ≤ b ∧
      collisionProbability (split q (flatteningCount x y)) ≤ b
  · have hN : (0 : ℝ) < Fintype.card α + 2 * m := by
      have : Nonempty α := ⟨p.support_nonempty.some⟩
      have := Fintype.card_pos (α := α)
      positivity
    -- Cauchy–Schwarz on the `n + 2m` points of the split domain.
    have hcs := four_mul_dist_sq_le_card_mul_sum_sq (split p (flatteningCount x y))
      (split q (flatteningCount x y))
    rw [dist_split, card_sigma_split, sum_flatteningCount] at hcs
    push_cast at hcs
    have h1 := acceptProb₂_closenessTester_le hδ h.1 h.2 hk (by
      rw [flatteningProximity_eq, div_pow, Real.sq_sqrt hN.le, div_le_iff₀ hN]
      have : ε ^ 2 ≤ dist p q ^ 2 := pow_le_pow_left₀ hε hpq 2
      nlinarith)
    have h2 : 0 ≤ (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split q (occurrenceCount y))) / b := by positivity
    linarith
  · have h1 : 1 < (collisionProbability (split p (occurrenceCount x)) +
        collisionProbability (split q (occurrenceCount y))) / b := by
      rw [lt_div_iff₀ hb]
      rcases not_and_or.mp h with h | h <;> linarith [not_le.mp h]
    have := acceptProb₂_le_one (closenessTester k (flatteningProximity α m ε))
      (split p (flatteningCount x y)) (split q (flatteningCount x y))
    linarith

/-- **The closeness tester by flattening**, a fixed-sample, two-sided variant of
[Diakonikolas–Kane, Proposition 2.10][DiakonikolasKane2016]: on a domain of size `n`, with `m`
flattening samples and `k` testing samples of each distribution, `closenessFlatteningTester m k ε`
is a closeness tester with proximity `ε` whenever `0 < ε` and
`864 (n + 2m) ≤ 5 (k - 1) ε² √(m + 1)`. -/
theorem isClosenessTester_closenessFlatteningTester {m k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 864 * ((Fintype.card α : ℝ) + 2 * m) ≤ 5 * (k - 1) * ε ^ 2 * Real.sqrt (m + 1)) :
    IsClosenessTester (closenessFlatteningTester (α := α) m k ε) ε := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hb : (0 : ℝ) < 16 / (m + 1) := by positivity
  have hrs : (1 / (m + 1) + 1 / (m + 1) : ℝ) / (16 / (m + 1)) = 1 / 8 := by
    field_simp
    norm_num
  -- The `ℓ₂` tester's hypothesis with `b = 16 / (m + 1)` and `δ = 5 / 24`.
  have hk' (p : PMF α) : 36 * Real.sqrt (16 / (m + 1)) ≤
      (k - 1) * flatteningProximity α m ε ^ 2 * (5 / 24) := by
    have : Nonempty α := ⟨p.support_nonempty.some⟩
    have hN : (0 : ℝ) < Fintype.card α + 2 * m := by
      have := Fintype.card_pos (α := α)
      positivity
    have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.mpr hm
    rw [flatteningProximity_eq, div_pow, Real.sq_sqrt hN.le, Real.sqrt_div' _ hm.le,
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
      show (36 : ℝ) * (4 / Real.sqrt (m + 1)) = 144 / Real.sqrt (m + 1) by ring, div_le_iff₀ hs,
      show ((k : ℝ) - 1) * ((2 * ε) ^ 2 / (Fintype.card α + 2 * m)) * (5 / 24) *
        Real.sqrt (m + 1) =
          5 * (k - 1) * ε ^ 2 * Real.sqrt (m + 1) / (6 * (Fintype.card α + 2 * m)) by
        field_simp; ring,
      le_div_iff₀ (by positivity)]
    linarith
  constructor
  · intro p
    rw [acceptProb₂_closenessFlatteningTester]
    have h := le_sum_sum p p _ _ _ hb (sum_iid_mul_collisionProbability_split_le p m)
      (sum_iid_mul_collisionProbability_split_le p m)
      (le_acceptProb₂_split (by norm_num) hb (hk' p) p)
    rw [hrs] at h
    linarith
  · intro p q hpq
    rw [acceptProb₂_closenessFlatteningTester]
    have h := sum_sum_le p q _ _ _ hb (sum_iid_mul_collisionProbability_split_le p m)
      (sum_iid_mul_collisionProbability_split_le q m)
      (acceptProb₂_split_le hε.le (by norm_num) hb (hk' p) hpq)
    rw [hrs] at h
    linarith

/-- **Choosing the parameters.** For any real flattening budget `0 < t ≤ n`, the flattening tester
with `m = ⌈t⌉` and `k = ⌈2592 n / (5 ε² √t)⌉ + 1` is a closeness tester with proximity `ε`. -/
theorem isClosenessTester_closenessFlatteningTester_ceil {t ε : ℝ} (ht : 0 < t)
    (htn : t ≤ Fintype.card α) (hε : 0 < ε) :
    IsClosenessTester (closenessFlatteningTester (α := α) ⌈t⌉₊
      (⌈2592 * Fintype.card α / (5 * ε ^ 2 * Real.sqrt t)⌉₊ + 1) ε) ε := by
  refine isClosenessTester_closenessFlatteningTester hε ?_
  have hm : (⌈t⌉₊ : ℝ) ≤ Fintype.card α := by exact_mod_cast Nat.ceil_le.mpr htn
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t ≤ Real.sqrt (⌈t⌉₊ + 1) :=
    Real.sqrt_le_sqrt ((Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one))
  have hX := Nat.le_ceil (2592 * Fintype.card α / (5 * ε ^ 2 * Real.sqrt t))
  rw [div_le_iff₀ (by positivity)] at hX
  push_cast
  have h1 : 0 ≤ (⌈2592 * Fintype.card α / (5 * ε ^ 2 * Real.sqrt t)⌉₊ : ℝ) * (5 * ε ^ 2) := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hst h1]

/-- **Sample complexity of closeness testing** [Chan–Diakonikolas–Valiant–Valiant]
[ChanDiakonikolasValiantValiant2014]: on a nonempty domain of size `n`, for every `0 < ε` there is
a closeness tester with proximity `ε` using `m + k ≤ 520 max(n^{2/3} ε^{-4/3}, √n ε^{-2}) + 3`
samples of each distribution, namely the flattening tester with `m = ⌈min(n, n^{2/3} ε^{-4/3})⌉`.
-/
theorem exists_isClosenessTester_closenessFlatteningTester [Nonempty α] {ε : ℝ} (hε : 0 < ε) :
    ∃ m k : ℕ, ((m + k : ℕ) : ℝ) ≤
        520 * max ((Fintype.card α : ℝ) ^ (2 / 3 : ℝ) / ε ^ (4 / 3 : ℝ))
          (Real.sqrt (Fintype.card α) / ε ^ 2) + 3 ∧
      IsClosenessTester (closenessFlatteningTester (α := α) m k ε) ε := by
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  set a := n ^ (2 / 3 : ℝ) / ε ^ (4 / 3 : ℝ) with ha_def
  set M := max a (Real.sqrt n / ε ^ 2) with hM
  set t := min n a with ht_def
  have ha : 0 < a := by positivity
  have ht : 0 < t := lt_min hn ha
  -- `n / (ε² √t)` is `√n / ε²` when `t = n` and `n^{2/3} ε^{-4/3}` when `t = n^{2/3} ε^{-4/3}`.
  have key : n / (ε ^ 2 * Real.sqrt t) ≤ M := by
    rcases min_choice n a with h | h
    · rw [ht_def.trans h]
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
      calc n / (ε ^ 2 * Real.sqrt n) = Real.sqrt n / ε ^ 2 := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            nth_rewrite 1 [← Real.sq_sqrt hn.le]
            ring
        _ ≤ M := le_max_right _ _
    · rw [ht_def.trans h]
      set u := n ^ (1 / 3 : ℝ)
      set v := ε ^ (2 / 3 : ℝ)
      have hu : 0 < u := by positivity
      have hv : 0 < v := by positivity
      have hu2 : n ^ (2 / 3 : ℝ) = u ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
      have hu3 : n = u ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
      have hv2 : ε ^ (4 / 3 : ℝ) = v ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
      have hv3 : ε ^ 2 = v ^ 3 := by
        refine Eq.symm ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
      have haa : a = (u / v) ^ 2 := by rw [ha_def, hu2, hv2, div_pow]
      calc n / (ε ^ 2 * Real.sqrt a) = a := by
            rw [haa, Real.sqrt_sq (by positivity), hv3]
            nth_rewrite 1 [hu3]
            field_simp
        _ ≤ M := le_max_left _ _
  refine ⟨⌈t⌉₊, ⌈2592 * n / (5 * ε ^ 2 * Real.sqrt t)⌉₊ + 1, ?_,
    isClosenessTester_closenessFlatteningTester_ceil ht (min_le_left _ _) hε⟩
  have h1 : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one ht.le
  have h2 : (⌈2592 * n / (5 * ε ^ 2 * Real.sqrt t)⌉₊ : ℝ) <
      2592 * n / (5 * ε ^ 2 * Real.sqrt t) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : t ≤ M := (min_le_right _ _).trans (le_max_left _ _)
  have h4 : 2592 * n / (5 * ε ^ 2 * Real.sqrt t) = 2592 / 5 * (n / (ε ^ 2 * Real.sqrt t)) := by
    field_simp
  have hM0 : 0 ≤ M := h3.trans' ht.le
  push_cast
  linarith

end Cslib.DistributionTesting
