/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.Basic
public import CslibFrontier.Computability.Streaming.Frequency
public import CslibFrontier.Probability.MedianOfMeans
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Data.Finset.PowerSum
import CslibFrontier.Foundations.Data.Finset.Variance
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The AMS estimator for the frequency moments `F_k`

Alon, Matias and Szegedy estimate every frequency moment `F_k = ∑ₐ (count a s) ^ k`
(`Cslib.Streaming.freqMoment`), `k ≥ 1`, of a stream of `m` items from a universe of size `n`
in one pass with `O(k λ⁻² log (1/ε) n ^ (1 - 1/k) (log n + log m))` bits of memory, to within
`λ F_k` except with probability `ε` [AlonMatiasSzegedy1999, Theorem 2.1].

**The basic estimator.** Draw a position `p` of the stream uniformly, let `r` be the number of
occurrences of the item `a_p` at positions `q ≥ p` (`Cslib.Streaming.suffixCount`), and set
`X = m (r ^ k - (r - 1) ^ k)` (`Cslib.Streaming.fkBasicEstimate`). Summing over the occurrences
of each item telescopes, so `𝔼 X = F_k` (`Cslib.Streaming.expect_fkBasicEstimate`). By
`a ^ k - b ^ k ≤ (a - b) k a ^ (k - 1)` (`Nat.succ_pow_sub_pow_le`),
`𝔼 X² ≤ k F₁ F_{2k-1}` (`Cslib.Streaming.expect_fkBasicEstimate_sq_le`), and the power-sum
inequality `F₁ F_{2k-1} ≤ n ^ (1 - 1/k) F_k²` of the source (`Finset.sum_mul_sum_pow_le`, raised to
the `k`-th power: `Cslib.Streaming.length_mul_freqMoment_pow_le`) bounds the variance by
`k n ^ (1 - 1/k) F_k²`.

**The sketch.** `Cslib.Streaming.fkSketch k m r K ω` runs `2 r` groups of `K` copies of the basic
estimator with sampled positions `ω i l` and reports the median over the groups of the average in
the group (`Cslib.Streaming.run_fkSketch_eq_medianOfMeans`). Each copy keeps the item at its
position, once that position has been read, and the number of its occurrences since; a step
counter tells when a sampled position arrives. As in the source the stream length `m` is known in
advance: the positions are drawn from `Fin m` and the answer scales by `m`, and the guarantees are
for streams of exactly `m` items. When `(3 k) ^ k n ^ (k - 1) ≤ (K λ²) ^ k`, that is
`3 k n ^ (1 - 1/k) ≤ K λ²` (`Cslib.Streaming.pow_mul_pow_sub_one_le_of_mul_rpow_le`), the answer
is within `λ F_k` of `F_k` except for an `(8 / 9) ^ r` fraction of the seeds
(`Cslib.Streaming.dens_fkSketch_error_le`), by the median-of-means bound
`Cslib.Probability.dens_abs_medianOfMeans_sub_gt_le`. So the randomized sketch with uniform
positions (`Cslib.Streaming.fkEstimator`) solves `F_k` estimation with error `δ ≥ (8 / 9) ^ r` on
streams of `m` items (`Cslib.Streaming.solves_fkEstimator`). The source takes `8 k n ^ (1 - 1/k)
/ λ²` copies per group, a Chebyshev bound `1/8` per group and a Chernoff bound over `2 log (1/ε)`
groups; here the group size `3 k n ^ (1 - 1/k) / λ²` gives `1/3` per group and
`r = ⌈log (1/ε) / log (9/8)⌉`, the same order.

**Memory.** On streams of at most `M` items the counter and every count lie in `[0, M]`, and a copy
stores one of `n + 1` item values (none or an item). Under the public-coin convention of
`Cslib.Streaming.Randomized` the positions are not charged, so every sketch drawn uses `b` bits
once `(M + 1) ((n + 1) (M + 1)) ^ (2 r K) ≤ 2 ^ b` (`Cslib.Streaming.spaceLE_fkEstimator`). As for
the AMS `F₂` sketch, only the initial memory depends on the positions
(`Cslib.Streaming.update_fkSketch`, `Cslib.Streaming.output_fkSketch`), and the states reachable
from all positions have one `b`-bit encoding once
`m ^ (2 r K) (M + 1) ((n + 1) (M + 1)) ^ (2 r K) ≤ 2 ^ b`
(`Cslib.Streaming.exists_injOn_iUnion_reachable_fkSketch`): `O(r K (log n + log m))` bits for
`M = m`, the bound of the theorem with `K = ⌈3 k n ^ (1 - 1/k) / λ²⌉`.

## Main definitions

* `Cslib.Streaming.suffixCount`: occurrences of the item at a position from that position on.
* `Cslib.Streaming.fkBasicEstimate`: the basic estimator `m (r ^ k - (r - 1) ^ k)`.
* `Cslib.Streaming.fkSketch`: the `F_k` sketch with given sampled positions.
* `Cslib.Streaming.fkEstimator`: the randomized `F_k` sketch with uniform positions.

## Main results

* `Cslib.Streaming.expect_fkBasicEstimate`, `Cslib.Streaming.expect_fkBasicEstimate_sq_le`: the
  basic estimator has mean `F_k` and second moment at most `k F₁ F_{2k-1}`.
* `Cslib.Streaming.length_mul_freqMoment_pow_le`: the power-sum inequality for streams,
  `(F₁ F_{2k+1}) ^ (k + 1) ≤ n ^ k F_{k+1} ^ (2 (k + 1))`.
* `Cslib.Streaming.dens_fkSketch_error_le`, `Cslib.Streaming.solves_fkEstimator`,
  `Cslib.Streaming.solves_fkEstimator_of_rpow`: the sketch estimates `F_k` within `λ F_k` except
  with probability `(8 / 9) ^ r` [AlonMatiasSzegedy1999, Theorem 2.1].
* `Cslib.Streaming.spaceLE_fkEstimator`, `Cslib.Streaming.exists_injOn_iUnion_reachable_fkSketch`:
  its memory without and with the sampled positions stored.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.1][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

open Finset Probability
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-! ### The basic estimator -/

/-- The number of occurrences of the item at position `p` of `s` among the positions `q ≥ p`, the
quantity `r` of [AlonMatiasSzegedy1999, proof of Theorem 2.1]; zero if `p` is not a position of
`s`. -/
@[expose] def suffixCount (s : List α) (p : ℕ) : ℕ :=
  match s[p]? with
  | none => 0
  | some a => (s.drop p).count a

@[simp] theorem suffixCount_nil (p : ℕ) : suffixCount ([] : List α) p = 0 := by
  simp [suffixCount]

@[simp] theorem suffixCount_cons_zero (a : α) (s : List α) :
    suffixCount (a :: s) 0 = s.count a + 1 := by
  simp [suffixCount]

@[simp] theorem suffixCount_cons_succ (a : α) (s : List α) (p : ℕ) :
    suffixCount (a :: s) (p + 1) = suffixCount s p := by
  simp [suffixCount]

theorem suffixCount_eq_of_lt {s : List α} {p : ℕ} (hp : p < s.length) :
    suffixCount s p = (s.drop p).count s[p] := by
  simp [suffixCount, List.getElem?_eq_getElem hp]

theorem suffixCount_eq_zero_of_le {s : List α} {p : ℕ} (hp : s.length ≤ p) :
    suffixCount s p = 0 := by
  simp [suffixCount, List.getElem?_eq_none hp]

theorem suffixCount_le_length (s : List α) (p : ℕ) : suffixCount s p ≤ s.length := by
  unfold suffixCount
  split
  · exact Nat.zero_le _
  · exact List.count_le_length.trans (by simp)

/-- **Telescoping** [AlonMatiasSzegedy1999, proof of Theorem 2.1]: summing
`r ^ k - (r - 1) ^ k` over the positions of the stream gives `F_k`, since the positions of an item
with `c` occurrences contribute `1 ^ k + (2 ^ k - 1 ^ k) + ⋯ + (c ^ k - (c - 1) ^ k) = c ^ k`. -/
theorem sum_range_pow_sub_pow_suffixCount {k : ℕ} (hk : k ≠ 0) (s : List α) :
    ∑ p ∈ range s.length, (suffixCount s p ^ k - (suffixCount s p - 1) ^ k) =
      freqMoment k s := by
  induction s with
  | nil => simp [freqMoment]
  | cons a s ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [suffixCount_cons_succ, suffixCount_cons_zero, Nat.add_sub_cancel, ih]
    have h1 := freqMoment_cons_add hk a s
    have h2 : s.count a ^ k ≤ (s.count a + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) k
    omega

/-- One occurrence's share of the second-moment bound:
`((c + 1) ^ (j + 1) - c ^ (j + 1)) ^ 2 ≤ (j + 1) ((c + 1) ^ (2 j + 1) - c ^ (2 j + 1))`. -/
private theorem sq_succ_pow_sub_pow_add_le (c j : ℕ) :
    ((c + 1) ^ (j + 1) - c ^ (j + 1)) ^ 2 + (j + 1) * c ^ (2 * j + 1) ≤
      (j + 1) * (c + 1) ^ (2 * j + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, (c + 1) ^ (j + 1) = c ^ (j + 1) + d :=
    Nat.exists_eq_add_of_le (Nat.pow_le_pow_left (Nat.le_succ c) _)
  have hdle := Nat.succ_pow_sub_pow_le c j
  rw [hd, Nat.add_sub_cancel_left] at hdle ⊢
  have hcj : c ^ j ≤ (c + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ _) _
  have key : d * (c + 1) ^ j + c ^ j * c ^ (j + 1) ≤ (c + 1) ^ j * (c + 1) ^ (j + 1) := by
    calc d * (c + 1) ^ j + c ^ j * c ^ (j + 1)
        ≤ d * (c + 1) ^ j + (c + 1) ^ j * c ^ (j + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hcj) _
      _ = (c + 1) ^ j * (c ^ (j + 1) + d) := by ring
      _ = (c + 1) ^ j * (c + 1) ^ (j + 1) := by rw [hd]
  have e1 : c ^ (2 * j + 1) = c ^ j * c ^ (j + 1) := by ring
  have e2 : (c + 1) ^ (2 * j + 1) = (c + 1) ^ j * (c + 1) ^ (j + 1) := by ring
  rw [e1, e2]
  calc d ^ 2 + (j + 1) * (c ^ j * c ^ (j + 1))
      ≤ d * ((j + 1) * (c + 1) ^ j) + (j + 1) * (c ^ j * c ^ (j + 1)) := by
        rw [sq]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left d hdle) _
    _ = (j + 1) * (d * (c + 1) ^ j + c ^ j * c ^ (j + 1)) := by ring
    _ ≤ (j + 1) * ((c + 1) ^ j * (c + 1) ^ (j + 1)) := Nat.mul_le_mul_left _ key

/-- **The second-moment sum** [AlonMatiasSzegedy1999, proof of Theorem 2.1, inequality (1)]:
summing `(r ^ k - (r - 1) ^ k) ^ 2` over the positions gives at most `k F_{2k-1}`, here with
`k = j + 1`. -/
theorem sum_range_sq_pow_sub_pow_suffixCount_le (j : ℕ) (s : List α) :
    ∑ p ∈ range s.length, (suffixCount s p ^ (j + 1) - (suffixCount s p - 1) ^ (j + 1)) ^ 2 ≤
      (j + 1) * freqMoment (2 * j + 1) s := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [suffixCount_cons_succ, suffixCount_cons_zero, Nat.add_sub_cancel]
    have h1 := freqMoment_cons_add (k := 2 * j + 1) (by omega) a s
    have h2 := sq_succ_pow_sub_pow_add_le (s.count a) j
    have h3 : (j + 1) * (freqMoment (2 * j + 1) (a :: s) + s.count a ^ (2 * j + 1)) =
        (j + 1) * (freqMoment (2 * j + 1) s + (s.count a + 1) ^ (2 * j + 1)) := by rw [h1]
    rw [mul_add, mul_add] at h3
    omega

/-- **The AMS power-sum inequality for streams** [AlonMatiasSzegedy1999, Fact in the proof of
Theorem 2.1]: `F₁ F_{2k-1} ≤ n ^ (1 - 1/k) F_k²` for a stream with `n` distinct items, raised to
the `k`-th power, with `k = j + 1`. -/
theorem length_mul_freqMoment_pow_le (j : ℕ) (s : List α) :
    (s.length * freqMoment (2 * j + 1) s) ^ (j + 1) ≤
      s.toFinset.card ^ j * freqMoment (j + 1) s ^ (2 * (j + 1)) := by
  have := Finset.sum_mul_sum_pow_le s.toFinset (c := fun a => s.count a)
    (fun _ _ => Nat.zero_le _) j
  simp only [Nat.cast_id, List.sum_toFinset_count_eq_length] at this
  exact this

/-- The **basic AMS estimator** of `F_k` at position `p` of the stream `s`:
`X = m (r ^ k - (r - 1) ^ k)` with `m` the length of `s` and `r = suffixCount s p`
[AlonMatiasSzegedy1999, proof of Theorem 2.1]. -/
@[expose] noncomputable def fkBasicEstimate (k : ℕ) (s : List α) (p : ℕ) : ℝ :=
  s.length * ((suffixCount s p ^ k - (suffixCount s p - 1) ^ k : ℕ) : ℝ)

/-- **The basic estimator is unbiased** [AlonMatiasSzegedy1999, proof of Theorem 2.1]: at a uniform
position of the stream its mean is `F_k`, for `k ≠ 0`. -/
theorem expect_fkBasicEstimate {k : ℕ} (hk : k ≠ 0) (s : List α) :
    𝔼 p : Fin s.length, fkBasicEstimate k s p = freqMoment k s := by
  rcases Nat.eq_zero_or_pos s.length with h0 | hpos
  · rw [List.length_eq_zero_iff.1 h0]
    simp [freqMoment]
  · rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    simp only [fkBasicEstimate]
    rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun p => ((suffixCount s p ^ k -
      (suffixCount s p - 1) ^ k : ℕ) : ℝ)), ← Nat.cast_sum,
      sum_range_pow_sub_pow_suffixCount hk]
    have : (s.length : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
    field_simp

/-- **The second moment of the basic estimator** [AlonMatiasSzegedy1999, proof of Theorem 2.1]:
`𝔼 X² ≤ k F₁ F_{2k-1}`, for `k ≠ 0`. -/
theorem expect_fkBasicEstimate_sq_le {k : ℕ} (hk : k ≠ 0) (s : List α) :
    𝔼 p : Fin s.length, fkBasicEstimate k s p ^ 2 ≤
      k * s.length * freqMoment (2 * k - 1) s := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [e]
  rcases Nat.eq_zero_or_pos s.length with h0 | hpos
  · rw [List.length_eq_zero_iff.1 h0]
    simp [freqMoment]
  · rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    simp only [fkBasicEstimate, mul_pow]
    rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun p => ((suffixCount s p ^ (j + 1) -
      (suffixCount s p - 1) ^ (j + 1) : ℕ) : ℝ) ^ 2)]
    have h : ∑ p ∈ range s.length, ((suffixCount s p ^ (j + 1) -
        (suffixCount s p - 1) ^ (j + 1) : ℕ) : ℝ) ^ 2 ≤
        ((j + 1 : ℕ) : ℝ) * freqMoment (2 * j + 1) s := by
      exact_mod_cast sum_range_sq_pow_sub_pow_suffixCount_le j s
    have hl : (0 : ℝ) < s.length := Nat.cast_pos.2 hpos
    rw [div_le_iff₀ hl]
    calc (s.length : ℝ) ^ 2 * ∑ p ∈ range s.length, ((suffixCount s p ^ (j + 1) -
          (suffixCount s p - 1) ^ (j + 1) : ℕ) : ℝ) ^ 2
        ≤ (s.length : ℝ) ^ 2 * (((j + 1 : ℕ) : ℝ) * freqMoment (2 * j + 1) s) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by push_cast; ring

/-- The group size condition `(3 k) ^ k n ^ (k - 1) ≤ (K η²) ^ k` bounds three times the second
moment bound `k F₁ F_{2k-1}` by `K (η F_k)²` on streams with at most `n` distinct items, through
the power-sum inequality `Cslib.Streaming.length_mul_freqMoment_pow_le`. -/
theorem three_mul_length_mul_freqMoment_le {k K n : ℕ} (hk : k ≠ 0) {η : ℝ}
    (hK : (3 * k : ℝ) ^ k * n ^ (k - 1) ≤ (K * η ^ 2) ^ k) {s : List α}
    (hn : s.toFinset.card ≤ n) :
    3 * (k * s.length * freqMoment (2 * k - 1) s : ℝ) ≤ K * (η * freqMoment k s) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  simp only [e, Nat.add_sub_cancel] at hK ⊢
  have hfact : ((s.length * freqMoment (2 * j + 1) s : ℕ) : ℝ) ^ (j + 1) ≤
      (n : ℝ) ^ j * (freqMoment (j + 1) s : ℝ) ^ (2 * (j + 1)) := by
    have h1 : ((s.length * freqMoment (2 * j + 1) s : ℕ) : ℝ) ^ (j + 1) ≤
        ((s.toFinset.card : ℕ) : ℝ) ^ j * (freqMoment (j + 1) s : ℝ) ^ (2 * (j + 1)) := by
      exact_mod_cast length_mul_freqMoment_pow_le j s
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn) j
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (Nat.succ_ne_zero j)]
  calc (3 * ((j + 1 : ℕ) * s.length * freqMoment (2 * j + 1) s : ℝ)) ^ (j + 1)
      = (3 * ((j + 1 : ℕ) : ℝ)) ^ (j + 1) *
          ((s.length * freqMoment (2 * j + 1) s : ℕ) : ℝ) ^ (j + 1) := by
        rw [← mul_pow]
        push_cast
        ring_nf
    _ ≤ (3 * ((j + 1 : ℕ) : ℝ)) ^ (j + 1) *
          ((n : ℝ) ^ j * (freqMoment (j + 1) s : ℝ) ^ (2 * (j + 1))) :=
        mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = ((3 * ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (n : ℝ) ^ j) *
          (freqMoment (j + 1) s : ℝ) ^ (2 * (j + 1)) := by ring
    _ ≤ ((K : ℝ) * η ^ 2) ^ (j + 1) * (freqMoment (j + 1) s : ℝ) ^ (2 * (j + 1)) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (K * (η * freqMoment (j + 1) s) ^ 2) ^ (j + 1) := by ring

/-- The `rpow` form `3 k n ^ (1 - 1/k) ≤ K η²` of the group size condition of
[AlonMatiasSzegedy1999, proof of Theorem 2.1] implies the form `(3 k) ^ k n ^ (k - 1) ≤ (K η²) ^ k`
used here. -/
theorem pow_mul_pow_sub_one_le_of_mul_rpow_le {k K n : ℕ} {η : ℝ}
    (h : 3 * k * (n : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ K * η ^ 2) :
    (3 * k : ℝ) ^ k * n ^ (k - 1) ≤ (K * η ^ 2) ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hpow : ((n : ℝ) ^ (1 - 1 / (k : ℝ))) ^ k = (n : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hk), Nat.cast_one]
    field_simp
  calc (3 * k : ℝ) ^ k * n ^ (k - 1) = (3 * k * (n : ℝ) ^ (1 - 1 / (k : ℝ))) ^ k := by
        rw [mul_pow (3 * (k : ℝ)), hpow]
    _ ≤ (K * η ^ 2) ^ k := pow_le_pow_left₀ (by positivity) h k

/-! ### The sketch -/

/-- The memory of the `F_k` sketch with `2 r` groups of `K` copies on streams of `m` items: the
sampled positions, a step counter, and for each copy an item (none before its position is read)
and a count. -/
abbrev FkState (α : Type*) (m r K : ℕ) : Type _ :=
  (Fin (2 * r) → Fin K → Fin m) × ℕ × (Fin (2 * r) → Fin K → Option α × ℕ)

/-- The update of one copy with sampled position `p` on reading the item `a` at step `t`: at its
position it stores `a` with count one, and afterwards it counts the occurrences of its item. -/
def fkCell (t : ℕ) (a : α) (p : ℕ) (c : Option α × ℕ) : Option α × ℕ :=
  if p = t then (some a, 1) else if c.1 = some a then (c.1, c.2 + 1) else c

/-- The **AMS `F_k` sketch** [AlonMatiasSzegedy1999, Theorem 2.1] for streams of `m` items with
sampled positions `ω`: the copy with position `p` computes `r = suffixCount s p`, and the answer is
the median over the `2 r` groups of the average of `m (r ^ k - (r - 1) ^ k)` over the `K` copies in
the group. The positions are written in the initial memory and read back by the update, which does
not otherwise depend on `ω` (`Cslib.Streaming.update_fkSketch`). -/
noncomputable def fkSketch (k m r K : ℕ) (ω : Fin (2 * r) → Fin K → Fin m) :
    Algorithm (FkState α m r K) α ℝ where
  init := (ω, 0, fun _ _ => (none, 0))
  update q a := (q.1, q.2.1 + 1, fun i l => fkCell q.2.1 a (q.1 i l) (q.2.2 i l))
  output q := median fun i => 𝔼 l, (m : ℝ) * ((q.2.2 i l).2 ^ k - ((q.2.2 i l).2 - 1) ^ k : ℕ)

/-- The randomized **AMS `F_k` sketch**: the sketch with independent uniform positions. -/
noncomputable def fkEstimator (α : Type*) [DecidableEq α] (k m r K : ℕ) [NeZero m] :
    Randomized (FkState α m r K) α ℝ :=
  (PMF.uniformOfFintype (Fin (2 * r) → Fin K → Fin m)).map (fkSketch k m r K)

variable {k m r K : ℕ}

/-- The `F_k` sketch starts with its positions, step zero and empty copies. -/
theorem init_fkSketch (ω : Fin (2 * r) → Fin K → Fin m) :
    (fkSketch (α := α) k m r K ω).init = (ω, 0, fun _ _ => (none, 0)) := by
  simp only [fkSketch]

/-- The update of the `F_k` sketch reads the positions from the memory: it does not depend on
`ω`. -/
theorem update_fkSketch (ω : Fin (2 * r) → Fin K → Fin m) (q : FkState α m r K) (a : α) :
    (fkSketch k m r K ω).update q a =
      (q.1, q.2.1 + 1, fun i l => fkCell q.2.1 a (q.1 i l) (q.2.2 i l)) := by
  simp only [fkSketch]

/-- The output of the `F_k` sketch does not depend on its positions. -/
theorem output_fkSketch (ω : Fin (2 * r) → Fin K → Fin m) (q : FkState α m r K) :
    (fkSketch k m r K ω).output q =
      median fun i => 𝔼 l, (m : ℝ) * ((q.2.2 i l).2 ^ k - ((q.2.2 i l).2 - 1) ^ k : ℕ) := by
  simp only [fkSketch]

private theorem fkCell_eq (s : List α) (a : α) (p : ℕ) :
    fkCell s.length a p (s[p]?, suffixCount s p) =
      ((s ++ [a])[p]?, suffixCount (s ++ [a]) p) := by
  rcases lt_trichotomy p s.length with hp | rfl | hp
  · have hp2 : p < (s ++ [a]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [suffixCount_eq_of_lt hp, suffixCount_eq_of_lt hp2, List.getElem?_eq_getElem hp,
      List.getElem?_eq_getElem hp2, List.getElem_append_left hp,
      List.drop_append_of_le_length hp.le, List.count_append]
    unfold fkCell
    by_cases h : s[p] = a
    · simp [h, hp.ne]
    · simp [h, hp.ne, Ne.symm h]
  · have hp2 : s.length < (s ++ [a]).length := by simp
    rw [suffixCount_eq_of_lt hp2]
    simp [fkCell]
  · have hp2 : (s ++ [a]).length ≤ p := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [suffixCount_eq_zero_of_le hp.le, suffixCount_eq_zero_of_le hp2,
      List.getElem?_eq_none hp.le, List.getElem?_eq_none hp2]
    simp [fkCell, hp.ne']

/-- After the stream `s`, the step counter is the length of `s`, and the copy with position `p`
holds the item at position `p` (if any) and `suffixCount s p`. -/
theorem state_fkSketch (ω : Fin (2 * r) → Fin K → Fin m) (s : List α) :
    (fkSketch k m r K ω).state s =
      (ω, s.length, fun i l => (s[(ω i l : ℕ)]?, suffixCount s (ω i l))) := by
  induction s using List.reverseRecOn with
  | nil => simp [Algorithm.state, fkSketch, suffixCount]
  | append_singleton s a ih =>
    rw [Algorithm.state_append, ih]
    simp only [Algorithm.stateFrom_cons, Algorithm.stateFrom_nil, fkSketch, List.length_append,
      List.length_singleton, fkCell_eq]

theorem run_fkSketch (ω : Fin (2 * r) → Fin K → Fin m) (s : List α) :
    (fkSketch k m r K ω).run s = median fun i => 𝔼 l, (m : ℝ) *
      ((suffixCount s (ω i l) ^ k - (suffixCount s (ω i l) - 1) ^ k : ℕ) : ℝ) := by
  rw [Algorithm.run, state_fkSketch]
  rfl

/-- On a stream of exactly `m` items, the answer of the `F_k` sketch is the median of means of the
basic estimator at the sampled positions. -/
theorem run_fkSketch_eq_medianOfMeans (s : List α) (ω : Fin (2 * r) → Fin K → Fin s.length) :
    (fkSketch k s.length r K ω).run s =
      medianOfMeans (fun p : Fin s.length => fkBasicEstimate k s p) ω := by
  rw [run_fkSketch]
  rfl

/-- **The AMS sketch estimates `F_k`** [AlonMatiasSzegedy1999, Theorem 2.1]: on a stream of `m`
items with at most `n` distinct items, if `k ≠ 0`, `η > 0` and `(3 k) ^ k n ^ (k - 1) ≤ (K η²) ^ k`,
the `F_k` sketch with `2 r` groups of `K` copies misses `F_k` by more than `η F_k` for at most an
`(8 / 9) ^ r` fraction of the sampled positions. -/
theorem dens_fkSketch_error_le {n : ℕ} (hk : k ≠ 0) {η : ℝ} (hη : 0 < η)
    (hK : (3 * k : ℝ) ^ k * n ^ (k - 1) ≤ (K * η ^ 2) ^ k) (s : List α)
    (hn : s.toFinset.card ≤ n) :
    (dens {ω : Fin (2 * r) → Fin K → Fin s.length |
      η * freqMoment k s < |(fkSketch k s.length r K ω).run s - freqMoment k s|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  rcases eq_or_ne s [] with rfl | hs
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero]
      exact_mod_cast dens_le_one
    have : Nonempty (Fin (2 * r)) := ⟨⟨0, by omega⟩⟩
    rw [filter_false_of_mem, dens_empty, NNRat.cast_zero]
    · positivity
    · intro ω _
      simp [run_fkSketch, freqMoment]
  have hne : Nonempty (Fin s.length) := ⟨⟨0, List.length_pos_iff.2 hs⟩⟩
  have hn1 : 1 ≤ n :=
    (Finset.card_pos.2 ⟨_, List.mem_toFinset.2 (List.head_mem hs)⟩).trans_le hn
  have hK0 : NeZero K := ⟨by
    rintro rfl
    have : (0 : ℝ) < (3 * k : ℝ) ^ k * n ^ (k - 1) := by
      have : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
      have : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      positivity
    simp only [Nat.cast_zero, zero_mul, zero_pow hk] at hK
    linarith⟩
  have hF : (0 : ℝ) < freqMoment k s := by exact_mod_cast freqMoment_pos k hs
  set g : Fin s.length → ℝ := fun p => fkBasicEstimate k s p
  have hmean : 𝔼 p, g p = freqMoment k s := expect_fkBasicEstimate hk s
  have hvar : 3 * 𝔼 p, (g p - 𝔼 p', g p') ^ 2 ≤ K * (η * freqMoment k s) ^ 2 := by
    rw [Fintype.expect_sub_expect_sq]
    have h1 := expect_fkBasicEstimate_sq_le hk s
    have h2 := three_mul_length_mul_freqMoment_le hk hK hn
    nlinarith [sq_nonneg (𝔼 p, g p)]
  have := dens_abs_medianOfMeans_sub_gt_le (r := r) g (by positivity) hvar
  rw [hmean] at this
  simpa only [run_fkSketch_eq_medianOfMeans] using this

/-- The error of the randomized `F_k` sketch is the fraction of bad sampled positions. -/
theorem errorProb_fkEstimator [NeZero m] (R : List α → ℝ → Prop) (s : List α)
    [DecidablePred fun ω : Fin (2 * r) → Fin K → Fin m => ¬R s ((fkSketch k m r K ω).run s)] :
    (fkEstimator α k m r K).errorProb R s =
      dens {ω : Fin (2 * r) → Fin K → Fin m | ¬R s ((fkSketch k m r K ω).run s)} :=
  Randomized.errorProb_map_uniformOfFintype _ R s

/-- **The AMS sketch solves `F_k` estimation** [AlonMatiasSzegedy1999, Theorem 2.1]: for items
from a universe of size `n`, if `k ≠ 0`, `η > 0`, `(3 k) ^ k n ^ (k - 1) ≤ (K η²) ^ k` and
`(8 / 9) ^ r ≤ δ`, the randomized `F_k` sketch for streams of `m` items estimates `F_k` within
`η F_k` with error at most `δ` on every stream of `m` items. -/
theorem solves_fkEstimator [Fintype α] [NeZero m] (hk : k ≠ 0) {η δ : ℝ} (hη : 0 < η)
    (hK : (3 * k : ℝ) ^ k * Fintype.card α ^ (k - 1) ≤ (K * η ^ 2) ^ k)
    (hδ : (8 / 9 : ℝ) ^ r ≤ δ) :
    (fkEstimator α k m r K).Solves δ
      (fun s Y => s.length = m → |Y - freqMoment k s| ≤ η * freqMoment k s) m := by
  classical
  intro s _
  rw [errorProb_fkEstimator]
  by_cases hs : s.length = m
  · subst hs
    simp only [not_imp, not_le, true_and]
    exact (dens_fkSketch_error_le hk hη hK s (card_le_univ _)).trans hδ
  · rw [filter_false_of_mem fun ω _ => by simp [hs], dens_empty, NNRat.cast_zero]
    exact (pow_nonneg (by norm_num) r).trans hδ

/-- `Cslib.Streaming.solves_fkEstimator` with the group size condition
`3 k n ^ (1 - 1/k) ≤ K η²` of [AlonMatiasSzegedy1999, proof of Theorem 2.1]. -/
theorem solves_fkEstimator_of_rpow [Fintype α] [NeZero m] (hk : k ≠ 0) {η δ : ℝ} (hη : 0 < η)
    (hK : 3 * k * (Fintype.card α : ℝ) ^ (1 - 1 / (k : ℝ)) ≤ K * η ^ 2)
    (hδ : (8 / 9 : ℝ) ^ r ≤ δ) :
    (fkEstimator α k m r K).Solves δ
      (fun s Y => s.length = m → |Y - freqMoment k s| ≤ η * freqMoment k s) m :=
  solves_fkEstimator hk hη (pow_mul_pow_sub_one_le_of_mul_rpow_le hK) hδ

/-! ### Memory -/

/-- The states of the `F_k` sketch on streams of at most `M` items lie in a product of the
positions, the counter values `[0, M]` and, for each copy, an item value and a count in `[0, M]`. -/
private theorem state_fkSketch_mem [Fintype α] {M : ℕ} (ω : Fin (2 * r) → Fin K → Fin m)
    {s : List α} (hs : s.length ≤ M) :
    (fkSketch k m r K ω).state s ∈ (({ω} : Finset _) ×ˢ range (M + 1) ×ˢ
      Fintype.piFinset fun _ : Fin (2 * r) => Fintype.piFinset fun _ : Fin K =>
        (univ : Finset (Option α)) ×ˢ range (M + 1)) := by
  rw [state_fkSketch, mem_product, mem_product, Fintype.mem_piFinset]
  refine ⟨mem_singleton_self _, mem_range.2 (Nat.lt_succ_of_le hs),
    fun i => Fintype.mem_piFinset.2 fun l => ?_⟩
  exact mem_product.2 ⟨mem_univ _,
    mem_range.2 (Nat.lt_succ_of_le ((suffixCount_le_length s _).trans hs))⟩

omit [DecidableEq α] in
private theorem card_fkState_finset [Fintype α] {M : ℕ}
    (T : Finset (Fin (2 * r) → Fin K → Fin m)) :
    (T ×ˢ range (M + 1) ×ˢ
      Fintype.piFinset fun _ : Fin (2 * r) => Fintype.piFinset fun _ : Fin K =>
        (univ : Finset (Option α)) ×ˢ range (M + 1)).card =
      T.card * ((M + 1) * ((Fintype.card α + 1) * (M + 1)) ^ (2 * r * K)) := by
  simp only [card_product, card_range, Fintype.card_piFinset, card_univ, Fintype.card_option,
    prod_const, Fintype.card_fin]
  rw [← pow_mul, mul_comm K]

/-- **The memory of the randomized `F_k` sketch** [AlonMatiasSzegedy1999, Theorem 2.1]: for items
from a universe of size `n`, every sketch it draws uses at most `b` bits of memory on streams of at
most `M` items when `(M + 1) ((n + 1) (M + 1)) ^ (2 r K) ≤ 2 ^ b`. Under the public-coin convention
of `Cslib.Streaming.Randomized` the sampled positions are not charged; for the count with the
positions stored see `Cslib.Streaming.exists_injOn_iUnion_reachable_fkSketch`. -/
theorem spaceLE_fkEstimator [Fintype α] [NeZero m] {M b : ℕ}
    (hb : (M + 1) * ((Fintype.card α + 1) * (M + 1)) ^ (2 * r * K) ≤ 2 ^ b) :
    (fkEstimator α k m r K).SpaceLE M b := by
  classical
  intro A hA
  rw [fkEstimator, PMF.support_map] at hA
  obtain ⟨ω, -, rfl⟩ := hA
  refine Algorithm.spaceLE_of_subset_finset ?_ (?_ : (({ω} : Finset _) ×ˢ range (M + 1) ×ˢ
      Fintype.piFinset fun _ : Fin (2 * r) => Fintype.piFinset fun _ : Fin K =>
        (univ : Finset (Option α)) ×ˢ range (M + 1)).card ≤ 2 ^ b)
  · rintro _ ⟨s, hs, rfl⟩
    exact state_fkSketch_mem ω hs
  · rwa [card_fkState_finset, card_singleton, one_mul]

/-- **The memory of the `F_k` sketch with its positions stored** [AlonMatiasSzegedy1999,
Theorem 2.1]: on streams of at most `M` items, the states reachable from all sampled positions
together have a single injective encoding by `b` bits as soon as
`m ^ (2 r K) (M + 1) ((n + 1) (M + 1)) ^ (2 r K) ≤ 2 ^ b`. Since only the initial memory depends on
the positions (`Cslib.Streaming.update_fkSketch`, `Cslib.Streaming.output_fkSketch`), this is the
memory of one algorithm whose initial memory is random, with the positions charged. -/
theorem exists_injOn_iUnion_reachable_fkSketch [Fintype α] {M b : ℕ}
    (hb : m ^ (2 * r * K) * ((M + 1) * ((Fintype.card α + 1) * (M + 1)) ^ (2 * r * K)) ≤
      2 ^ b) :
    ∃ enc : FkState α m r K → BitString b,
      Set.InjOn enc (⋃ ω, (fkSketch k m r K ω).reachable M) := by
  classical
  refine Algorithm.exists_injOn_of_subset_finset
    (T := (univ : Finset (Fin (2 * r) → Fin K → Fin m)) ×ˢ range (M + 1) ×ˢ
      Fintype.piFinset fun _ : Fin (2 * r) => Fintype.piFinset fun _ : Fin K =>
        (univ : Finset (Option α)) ×ˢ range (M + 1)) ?_ ?_
  · rintro _ ⟨_, ⟨ω, rfl⟩, s, hs, rfl⟩
    have := state_fkSketch_mem (k := k) ω hs
    rw [mem_coe]
    rw [mem_product] at this ⊢
    exact ⟨mem_univ _, this.2⟩
  · rw [card_fkState_finset, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
      Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Fintype.card_fin, ← pow_mul,
      mul_comm K]
    exact hb

end Cslib.Streaming
