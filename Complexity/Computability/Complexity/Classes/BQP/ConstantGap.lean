/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.Amplification
import Complexity.Foundations.BooleanAnalysis.Bernoulli
import Complexity.Foundations.Combinatorics.BinomialTail

/-!
# `BQP` from any constant gap

The thresholds `2 / 3` and `1 / 3` in the definition of `BQP` (`Cslib.Complexity.BQP`) can be
replaced by any constants `s < c`: a problem is in `BQP` exactly when some uniform family accepts
its members with probability at least `c` and other instances with probability at most `s`
(`Cslib.Complexity.mem_BQP_iff_exists_gap`).

The threshold vote of the family (`Cslib.Quantum.UniformCircuitFamily.threshold`) decides whether
more than `t` of `k` independent runs accept. Its acceptance probability is a binomial tail
(`Cslib.Quantum.UniformCircuitFamily.acceptProb_threshold_eq_sum_choose`), and Hoeffding's
inequality (`Cslib.sum_filter_le_sub_choose_mul_pow_le`,
`Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`) bounds its errors by `exp (-2 k δ²)` when the
threshold `t` lies `k δ` away from `k p`
(`Cslib.Quantum.UniformCircuitFamily.acceptProb_threshold_le_exp`,
`Cslib.Quantum.UniformCircuitFamily.one_sub_exp_le_acceptProb_threshold`). For constants `s < c`
with gap `2 δ = c - s`, a vote over `k = ⌈1 / δ²⌉` copies with threshold `⌊k (s + c) / 2⌋` has
errors at most `exp (-2) < 1 / 3`.

## Main results

* `Cslib.Quantum.UniformCircuitFamily.acceptProb_threshold_eq_sum_choose`: the acceptance
  probability of the threshold vote is the binomial tail `P[Bin(k, p) > t]`.
* `Cslib.Quantum.UniformCircuitFamily.acceptProb_threshold_le_exp`,
  `Cslib.Quantum.UniformCircuitFamily.one_sub_exp_le_acceptProb_threshold`: Hoeffding bounds for
  the threshold vote.
* `Cslib.Complexity.mem_BQP_of_gap`, `Cslib.Complexity.mem_BQP_iff_exists_gap`: `BQP` from any
  constant gap.

The argument is the standard one (threshold vote and Hoeffding's inequality); no source locator is
claimed for it. The gaps here are constants; gaps shrinking with the input length are not treated.
-/

public section

namespace Cslib.Quantum

namespace UniformCircuitFamily

open Finset Turing.MultiTapeTM

/-- **The threshold vote is a binomial tail**: it accepts with probability
`∑_{t < j ≤ k} C(k, j) p^j (1 - p)^(k - j)`, where `p` is the acceptance probability of the family
and `k`, `t` are taken at the input length. -/
theorem acceptProb_threshold_eq_sum_choose (F : UniformCircuitFamily) {k t : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary) (x : List Bool) :
    (F.threshold k t hk ht).acceptProb x =
      ∑ j ∈ range (k x.length + 1) with t x.length < j,
        ((k x.length).choose j : ℝ) * F.acceptProb x ^ j *
          (1 - F.acceptProb x) ^ (k x.length - j) := by
  have h := BitString.bernoulliAverage_lt_weight (ι := Fin (k x.length)) (F.acceptProb x)
    (t x.length)
  rw [Fintype.card_fin] at h
  rw [← h, acceptProb_threshold, BitString.bernoulliAverage, sum_filter]
  refine sum_congr rfl fun b _ => ?_
  rw [BitString.bernoulliWeight, BitString.weight, mul_ite, mul_one, mul_zero]

/-- **Hoeffding bound for rejection**: if the threshold `t` is at least `k (p + δ) - 1`, with
`0 ≤ δ`, then the threshold vote accepts with probability at most `exp (-2 k δ²)`. -/
theorem acceptProb_threshold_le_exp (F : UniformCircuitFamily) {k t : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary) (x : List Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hkt : k x.length * (F.acceptProb x + δ) ≤ t x.length + 1) :
    (F.threshold k t hk ht).acceptProb x ≤ Real.exp (-2 * k x.length * δ ^ 2) := by
  set K := k x.length
  set p := F.acceptProb x
  have hmono : (∑ j ∈ range (K + 1) with t x.length < j,
      (K.choose j : ℝ) * p ^ j * (1 - p) ^ (K - j)) ≤
      ∑ j ∈ range (K + 1) with K * δ ≤ ((j : ℕ) : ℝ) - K * p,
        (K.choose j : ℝ) * p ^ j * (1 - p) ^ (K - j) := by
    refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => ?_
    · rw [mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      have : ((t x.length : ℕ) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj.2
      nlinarith
    · have h1p : 0 ≤ 1 - p := sub_nonneg.mpr (F.acceptProb_le_one x)
      have hp : 0 ≤ p := F.acceptProb_nonneg x
      positivity
  have hhoeff := sum_filter_le_sub_choose_mul_pow_le K (F.acceptProb_nonneg x)
    (F.acceptProb_le_one x) (mul_nonneg (Nat.cast_nonneg K) hδ)
  rw [acceptProb_threshold_eq_sum_choose]
  refine hmono.trans (hhoeff.trans_eq ?_)
  rcases Nat.eq_zero_or_pos K with hK | hK
  · simp [hK]
  · congr 1
    field_simp

/-- **Hoeffding bound for acceptance**: if the threshold `t` is at most `k (p - δ)`, with `0 ≤ δ`,
then the threshold vote accepts with probability at least `1 - exp (-2 k δ²)`. -/
theorem one_sub_exp_le_acceptProb_threshold (F : UniformCircuitFamily) {k t : ℕ → ℕ}
    (hk : ComputableInPolyTime k encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary) (x : List Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (htk : (t x.length : ℝ) ≤ k x.length * (F.acceptProb x - δ)) :
    1 - Real.exp (-2 * k x.length * δ ^ 2) ≤ (F.threshold k t hk ht).acceptProb x := by
  set K := k x.length
  set p := F.acceptProb x
  have hp : 0 ≤ p := F.acceptProb_nonneg x
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr (F.acceptProb_le_one x)
  have hmono : (∑ j ∈ range (K + 1) with ¬ t x.length < j,
      (K.choose j : ℝ) * p ^ j * (1 - p) ^ (K - j)) ≤
      ∑ j ∈ range (K + 1) with K * δ ≤ K * p - ((j : ℕ) : ℝ),
        (K.choose j : ℝ) * p ^ j * (1 - p) ^ (K - j) := by
    refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => by positivity
    rw [mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have : (j : ℝ) ≤ ((t x.length : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hj.2
    nlinarith
  have hhoeff := sum_filter_le_mul_sub_choose_mul_pow_le K hp (F.acceptProb_le_one x)
    (mul_nonneg (Nat.cast_nonneg K) hδ)
  have htotal := sum_filter_add_sum_filter_not (range (K + 1)) (fun j => t x.length < j)
    fun j => (K.choose j : ℝ) * p ^ j * (1 - p) ^ (K - j)
  rw [sum_choose_mul_pow_eq_one] at htotal
  have hexp : Real.exp (-2 * (K * δ) ^ 2 / K) = Real.exp (-2 * K * δ ^ 2) := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · simp [hK]
    · congr 1
      field_simp
  rw [acceptProb_threshold_eq_sum_choose]
  linarith

end UniformCircuitFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **`BQP` from any constant gap**: a uniform family that accepts members with probability at
least `c` and other instances with probability at most `s`, for constants `s < c`, shows that the
problem is in `BQP`. A threshold vote over `⌈1 / δ²⌉` copies, with `2 δ = c - s`, brings the errors
below `exp (-2) < 1 / 3`. -/
theorem mem_BQP_of_gap {A : Set α} {s c : ℝ} (hsc : s < c) (F : UniformCircuitFamily)
    (hF : ∀ a, (a ∈ A → c ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ s)) :
    A ∈ BQP enc := by
  rcases lt_or_ge s 0 with hs | hs
  · -- no instance accepts with probability below `0`: every instance is a member
    have hA (a : α) : a ∈ A := by
      by_contra ha
      linarith [(hF a).2 ha, F.acceptProb_nonneg (enc a)]
    let G := (F.threshold (fun _ => 0) (fun _ => 0) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).appendNot
    refine ⟨G, fun a => ⟨fun _ => ?_, fun ha => absurd (hA a) ha⟩⟩
    rw [UniformCircuitFamily.acceptProb_appendNot,
      UniformCircuitFamily.acceptProb_threshold_eq_sum_choose]
    norm_num [Finset.filter_singleton]
  set δ := (c - s) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K : ℕ := ⌈1 / δ ^ 2⌉₊
  set T : ℕ := ⌊K * ((s + c) / 2)⌋₊
  have hKδ : 1 ≤ K * δ ^ 2 := by
    have := Nat.le_ceil (1 / δ ^ 2)
    rwa [div_le_iff₀ (by positivity)] at this
  -- `exp (-2) ≤ 1 / 3`, since `3 ≤ 1 + 2 ≤ exp 2`
  have hexp2 : Real.exp (-2) ≤ 1 / 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
    linarith [Real.add_one_le_exp 2]
  have hexp : Real.exp (-2 * K * δ ^ 2) ≤ 1 / 3 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hexp2
  have hK : ComputableInPolyTime (fun _ : ℕ => K) encUnary encUnary := ComputableInPolyTime.const _
  have hT : ComputableInPolyTime (fun _ : ℕ => T) encUnary encUnary := ComputableInPolyTime.const _
  refine ⟨F.threshold (fun _ => K) (fun _ => T) hK hT, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have hTle : (T : ℝ) ≤ K * (F.acceptProb (enc a) - δ) := by
      have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (by linarith : 0 ≤ (s + c) / 2))
      have := (hF a).1 ha
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have := F.one_sub_exp_le_acceptProb_threshold hK hT (enc a) hδ0.le hTle
    linarith
  · have hTge : (K : ℝ) * (F.acceptProb (enc a) + δ) ≤ T + 1 := by
      have := Nat.lt_floor_add_one ((K : ℝ) * ((s + c) / 2))
      have := (hF a).2 ha
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    exact (F.acceptProb_threshold_le_exp hK hT (enc a) hδ0.le hTge).trans hexp

/-- **`BQP` is the class of problems decided with some constant gap**: `A ∈ BQP enc` exactly when
for some constants `s < c`, a uniform family accepts members with probability at least `c` and
other instances with probability at most `s`. -/
theorem mem_BQP_iff_exists_gap {A : Set α} :
    A ∈ BQP enc ↔ ∃ s c : ℝ, s < c ∧ ∃ F : UniformCircuitFamily, ∀ a,
      (a ∈ A → c ≤ F.acceptProb (enc a)) ∧ (a ∉ A → F.acceptProb (enc a) ≤ s) := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨1 / 3, 2 / 3, by norm_num, F, hF⟩
  · rintro ⟨s, c, hsc, F, hF⟩
    exact mem_BQP_of_gap hsc F hF

end Cslib.Complexity
