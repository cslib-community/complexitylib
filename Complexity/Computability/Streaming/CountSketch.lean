/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Streaming.Basic
public import Complexity.Computability.Streaming.Frequency
public import Complexity.Foundations.Data.Finset.Median
public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.UniversalHash
import Complexity.Probability.KWiseIndependent.CountSketch
import Complexity.Probability.MedianOfMeans
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

/-!
# Count-Sketch

The **Count-Sketch** of Charikar, Chen and Farach-Colton [CharikarChenFarachColton2004] estimates
the frequency `f_a = count a s` of a queried item `a` in a stream `s`. Each of its `d = 2 r` rows
has `w` counters, a bucket hash `h θ : α → Fin w` and a sign hash `sgn (g φ a) = ±1`, with seed
`(θ, φ)`. On reading an item `a`, every row adds the sign of `a` to the counter of `a`; a point
query `a` reports the median over the rows of the counter of `a` times the sign of `a`
(`Cslib.Streaming.countSketch`, [Chakrabarti2025, Algorithm 8]).

For each fixed query `a`, with a two-universal bucket family and an independent pairwise independent
family of signs of mean zero, each row errs by more than `t` with probability at most `1 / 3` once
`3 ‖f_{-a}‖₂² ≤ w t²`, where `‖f_{-a}‖₂² = ∑_{b ≠ a} f_b²`
(`Cslib.Probability.CountSketch.dens_abs_sum_ite_mul_sign_gt_le`); so the median errs with
probability at most `(8 / 9) ^ r` (`Cslib.Streaming.dens_countSketch_error_gt_le`). With
`3 ≤ w ε²` and `(8 / 9) ^ r ≤ δ` the randomized Count-Sketch with uniform seeds
(`Cslib.Streaming.countSketchRandom`) answers every point query within `ε ‖f_{-a}‖₂`, hence within
`ε ‖f‖₂ = ε √F₂`, except with probability `δ` (`Cslib.Streaming.solves_countSketchRandom`,
`Cslib.Streaming.solves_countSketchRandom_freqMoment`) [Chakrabarti2025, equation (5.7)]. The query
is fixed before the seeds are drawn: there is no claim about adaptively chosen queries.

**Memory.** On streams of at most `m` items each counter lies in `[-m, m]`. Under the public-coin
convention of `Cslib.Streaming.Randomized` the seeds are not charged, so every sketch drawn uses at
most `b` bits when `(2 m + 1) ^ (2 r w) ≤ 2 ^ b` (`Cslib.Streaming.spaceLE_countSketchRandom`). Only
the initial memory depends on the seeds (`Cslib.Streaming.update_countSketch`,
`Cslib.Streaming.output_countSketch`), and with the seeds stored one `b`-bit encoding of the states
reachable from all seeds exists when `(|ι| |κ|) ^ (2 r) (2 m + 1) ^ (2 r w) ≤ 2 ^ b`
(`Cslib.Streaming.exists_injOn_iUnion_reachable_countSketch`). With `w = ⌈3 / ε²⌉`,
`r = O(log δ⁻¹)` and hash families with `O(log n)`-bit seeds, this is the
`O(ε⁻² log δ⁻¹ (log m + log n))` bound of [Chakrabarti2025, Section 5.3.2].

## Main definitions

* `Cslib.Streaming.countSketch`: the Count-Sketch with given seeds.
* `Cslib.Streaming.countSketchRandom`: the randomized Count-Sketch with uniform seeds.

## Main results

* `Cslib.Streaming.run_countSketch`: the answer is the median of the row estimates.
* `Cslib.Streaming.dens_countSketch_error_gt_le`, `Cslib.Streaming.solves_countSketchRandom`,
  `Cslib.Streaming.solves_countSketchRandom_freqMoment`: the accuracy of the Count-Sketch.
* `Cslib.Streaming.spaceLE_countSketchRandom`,
  `Cslib.Streaming.exists_injOn_iUnion_reachable_countSketch`: its memory.

## References

* [M. Charikar, K. Chen, M. Farach-Colton, *Finding frequent items in data
  streams*][CharikarChenFarachColton2004]
* [A. Chakrabarti, *Data Stream Algorithms*, Section 5.3][Chakrabarti2025]
-/

public section

namespace Cslib.Streaming

open Finset Probability
open scoped BigOperators

variable {ι κ α Y : Type*} {w r : ℕ}

/-- The memory of a Count-Sketch with `2 r` rows of `w` counters: the seeds of the hashes of each
row, and the counters. -/
abbrev CountSketchState (ι κ : Type*) (r w : ℕ) : Type _ :=
  (Fin (2 * r) → ι × κ) × (Fin (2 * r) → Fin w → ℤ)

/-- The **Count-Sketch** [CharikarChenFarachColton2004] with `2 r` rows of `w` counters and seeds
`ω`: row `i` with seed `(θ, φ) = ω i` adds the sign `sgn (g φ a)` of each item `a` to its counter
`h θ a`, and a point query `a` is answered with the median over the rows of the counter of `a` times
the sign of `a` [Chakrabarti2025, Algorithm 8]. The seeds are written in the initial memory and read
back by the update. -/
noncomputable def countSketch (h : ι → α → Fin w) (g : κ → α → Y) (sgn : Y → ℤ) (r : ℕ)
    (ω : Fin (2 * r) → ι × κ) : Algorithm (CountSketchState ι κ r w) α (α → ℝ) where
  init := (ω, 0)
  update := fun (ω', C) a => (ω', fun i j => C i j +
    if h (ω' i).1 a = j then sgn (g (ω' i).2 a) else 0)
  output := fun (ω', C) a => median fun i => ((C i (h (ω' i).1 a) * sgn (g (ω' i).2 a) : ℤ) : ℝ)

/-- The randomized **Count-Sketch**: the sketch with independent uniform seeds for its rows. -/
noncomputable def countSketchRandom [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (h : ι → α → Fin w) (g : κ → α → Y) (sgn : Y → ℤ) (r : ℕ) :
    Randomized (CountSketchState ι κ r w) α (α → ℝ) :=
  (PMF.uniformOfFintype (Fin (2 * r) → ι × κ)).map (countSketch h g sgn r)

variable {h : ι → α → Fin w} {g : κ → α → Y} {sgn : Y → ℤ}

/-- The Count-Sketch starts with its seeds and zero counters. -/
theorem init_countSketch (ω : Fin (2 * r) → ι × κ) :
    (countSketch h g sgn r ω).init = (ω, 0) := by
  simp only [countSketch]

/-- The update of the Count-Sketch reads the seeds from the memory: it does not depend on `ω`. -/
theorem update_countSketch (ω ω' : Fin (2 * r) → ι × κ) (C : Fin (2 * r) → Fin w → ℤ) (a : α) :
    (countSketch h g sgn r ω).update (ω', C) a = (ω', fun i j => C i j +
      if h (ω' i).1 a = j then sgn (g (ω' i).2 a) else 0) := by
  simp only [countSketch]

/-- The output of the Count-Sketch does not depend on its seeds. -/
theorem output_countSketch (ω ω' : Fin (2 * r) → ι × κ) (C : Fin (2 * r) → Fin w → ℤ) (a : α) :
    (countSketch h g sgn r ω).output (ω', C) a =
      median fun i => ((C i (h (ω' i).1 a) * sgn (g (ω' i).2 a) : ℤ) : ℝ) := by
  simp only [countSketch]

/-- Reading the stream `s` from the memory `(ω', C)` adds to the counter `j` of row `i` the sum of
the signs of the items of `s` hashed to `j`. -/
theorem stateFrom_countSketch (ω ω' : Fin (2 * r) → ι × κ) (C : Fin (2 * r) → Fin w → ℤ)
    (s : List α) :
    (countSketch h g sgn r ω).stateFrom (ω', C) s = (ω', fun i j => C i j +
      (s.map fun a => if h (ω' i).1 a = j then sgn (g (ω' i).2 a) else 0).sum) := by
  induction s generalizing C with
  | nil => simp only [Algorithm.stateFrom_nil, List.map_nil, List.sum_nil, add_zero]
  | cons a s ih =>
    rw [Algorithm.stateFrom_cons, update_countSketch, ih]
    simp only [List.map_cons, List.sum_cons, add_assoc]

/-- After the stream `s`, the counter `j` of row `i` holds the sum of the signs of the items of `s`
hashed to `j`. -/
theorem state_countSketch (ω : Fin (2 * r) → ι × κ) (s : List α) :
    (countSketch h g sgn r ω).state s = (ω, fun i j =>
      (s.map fun a => if h (ω i).1 a = j then sgn (g (ω i).2 a) else 0).sum) := by
  rw [Algorithm.state, init_countSketch, stateFrom_countSketch]
  simp only [Pi.zero_apply, zero_add]

/-- The answer of the Count-Sketch to the query `a` is the median over the rows of
`(∑ b ∈ s with h θ b = h θ a, count b s · sgn (g φ b)) · sgn (g φ a)`. -/
theorem run_countSketch [DecidableEq α] (ω : Fin (2 * r) → ι × κ) (s : List α) (a : α) :
    (countSketch h g sgn r ω).run s a = median fun i =>
      (∑ b ∈ s.toFinset, if h (ω i).1 b = h (ω i).1 a then
        (s.count b : ℝ) * sgn (g (ω i).2 b) else 0) * sgn (g (ω i).2 a) := by
  have hsum (θ : ι) (φ : κ) : (((s.map fun b => if h θ b = h θ a then sgn (g φ b) else 0).sum :
      ℤ) : ℝ) = ∑ b ∈ s.toFinset, if h θ b = h θ a then (s.count b : ℝ) * sgn (g φ b) else 0 := by
    rw [Finset.sum_list_map_count, Int.cast_sum]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, smul_zero,
      Int.cast_zero]
  rw [Algorithm.run, state_countSketch, output_countSketch]
  simp only [Int.cast_mul, hsum]

/-- The error of one row of the Count-Sketch is the collision noise. -/
private theorem abs_row_sub_count [DecidableEq α] (hsq : ∀ y, sgn y ^ 2 = 1) (θ : ι) (φ : κ)
    (s : List α) (a : α) :
    |(∑ b ∈ s.toFinset, if h θ b = h θ a then (s.count b : ℝ) * sgn (g φ b) else 0) *
        sgn (g φ a) - s.count a| =
      |∑ b ∈ s.toFinset.erase a, if h θ b = h θ a then (s.count b : ℝ) * sgn (g φ b) else 0| := by
  have hsq' : ((sgn (g φ a) : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq _
  have hab : |((sgn (g φ a) : ℤ) : ℝ)| = 1 := by
    rcases sq_eq_one_iff.1 hsq' with h1 | h1 <;> simp only [h1, abs_one, abs_neg]
  have hsplit : (∑ b ∈ s.toFinset, if h θ b = h θ a then (s.count b : ℝ) * sgn (g φ b) else 0) =
      s.count a * sgn (g φ a) +
        ∑ b ∈ s.toFinset.erase a, if h θ b = h θ a then (s.count b : ℝ) * sgn (g φ b) else 0 := by
    by_cases ha : a ∈ s.toFinset
    · rw [← add_sum_erase _ _ ha]
      simp only [↓reduceIte]
    · have hc : s.count a = 0 := List.count_eq_zero.2 fun h => ha (List.mem_toFinset.2 h)
      rw [erase_eq_of_notMem ha, hc, Nat.cast_zero, zero_mul, zero_add]
  rw [hsplit, add_mul, mul_assoc, ← sq, hsq', mul_one, add_sub_cancel_left, abs_mul, hab, mul_one]

/-- **The Count-Sketch estimates frequencies** [Chakrabarti2025, equations (5.6)–(5.7)]: with a
two-universal bucket family `h` and an independent pairwise independent family `sgn ∘ g` of signs
of mean zero, if `3 ‖f_{-a}‖₂² ≤ w t²` then the Count-Sketch with `2 r` rows misses the frequency
of `a` by more than `t` for at most an `(8 / 9) ^ r` fraction of the seeds. -/
theorem dens_countSketch_error_gt_le [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq α]
    [Fintype Y] [DecidableEq Y] (hh : IsTwoUniversal (PMF.uniformOfFintype ι) h)
    (hg : IsKWiseIndependentHash 2 g) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    (s : List α) (a : α) {t : ℝ} (ht : 0 ≤ t)
    (hw : 3 * ∑ b ∈ s.toFinset.erase a, (s.count b : ℝ) ^ 2 ≤ w * t ^ 2) :
    (dens {ω : Fin (2 * r) → ι × κ |
      t < |(countSketch h g sgn r ω).run s a - s.count a|} : ℝ) ≤ (8 / 9) ^ r := by
  classical
  have hκ := hg.nonempty
  have hε : ∀ y, ((sgn y : ℤ) : ℝ) ^ 2 = 1 := fun y => by exact_mod_cast hsq y
  have hε₀ : 𝔼 y, ((sgn y : ℤ) : ℝ) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, ← Int.cast_sum, hsum, Int.cast_zero, zero_div]
  let G : ι × κ → ℝ := fun p => (∑ b ∈ s.toFinset, if h p.1 b = h p.1 a then
    (s.count b : ℝ) * sgn (g p.2 b) else 0) * sgn (g p.2 a)
  have hrow : (dens {p : ι × κ | t < |G p - s.count a|} : ℝ) ≤ 1 / 3 := by
    have hset : ({p : ι × κ | t < |G p - s.count a|} : Finset (ι × κ)) =
        ({p : ι × κ | t < |∑ b ∈ s.toFinset.erase a, if h p.1 b = h p.1 a then
          (s.count b : ℝ) * sgn (g p.2 b) else 0|} : Finset (ι × κ)) := by
      ext p
      simp only [mem_filter, mem_univ, true_and, G, abs_row_sub_count (h := h) (g := g) hsq]
    rw [hset]
    exact CountSketch.dens_abs_sum_ite_mul_sign_gt_le (κ := κ) hh hg hε hε₀
      (S := s.toFinset.erase a) (a := a) (notMem_erase a _) (fun b => (s.count b : ℝ)) ht hw
  have := dens_abs_median_sub_gt_le G hrow r
  simp only [run_countSketch]
  exact this

/-- The error of the randomized Count-Sketch is the fraction of bad seeds. -/
theorem errorProb_countSketchRandom [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (R : List α → (α → ℝ) → Prop) (s : List α)
    [DecidablePred fun ω : Fin (2 * r) → ι × κ => ¬R s ((countSketch h g sgn r ω).run s)] :
    (countSketchRandom h g sgn r).errorProb R s =
      dens {ω : Fin (2 * r) → ι × κ | ¬R s ((countSketch h g sgn r ω).run s)} := by
  unfold Randomized.errorProb countSketchRandom
  rw [PMF.toOuterMeasure_map_apply, nnratCast_dens]
  exact Probability.PMF.toOuterMeasure_uniformOfFintype_toReal
    {ω : Fin (2 * r) → ι × κ | ¬R s ((countSketch h g sgn r ω).run s)}

/-- **The Count-Sketch answers point queries** [Chakrabarti2025, equation (5.7)]: with a
two-universal bucket family `h`, an independent pairwise independent family `sgn ∘ g` of signs of
mean zero, `3 ≤ w ε²` and `(8 / 9) ^ r ≤ δ`, for every fixed query `a` the randomized Count-Sketch
estimates the frequency of `a` within `ε ‖f_{-a}‖₂ = ε (∑_{b ≠ a} f_b²)^{1/2}` with error at most
`δ` on every stream. -/
theorem solves_countSketchRandom [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [DecidableEq α] [Fintype Y] [DecidableEq Y] (hh : IsTwoUniversal (PMF.uniformOfFintype ι) h)
    (hg : IsKWiseIndependentHash 2 g) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hw : 3 ≤ w * ε ^ 2) (hδ : (8 / 9 : ℝ) ^ r ≤ δ) (a : α) (m : ℕ) :
    (countSketchRandom h g sgn r).Solves δ (fun s est => |est a - s.count a| ≤
      ε * √(∑ b ∈ s.toFinset.erase a, (s.count b : ℝ) ^ 2)) m := by
  classical
  intro s _
  rw [errorProb_countSketchRandom]
  simp only [not_le]
  have hV : 0 ≤ ∑ b ∈ s.toFinset.erase a, (s.count b : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  refine (dens_countSketch_error_gt_le hh hg hsq hsum s a (by positivity) ?_).trans hδ
  rw [mul_pow, Real.sq_sqrt hV]
  nlinarith [mul_nonneg (sub_nonneg.2 hw) hV]

/-- **The Count-Sketch answers point queries within `ε √F₂`** [Chakrabarti2025, Section 5.3.2]:
under the hypotheses of `Cslib.Streaming.solves_countSketchRandom`, for every fixed query `a` the
randomized Count-Sketch estimates the frequency of `a` within `ε ‖f‖₂ = ε √F₂` with error at most
`δ` on every stream. -/
theorem solves_countSketchRandom_freqMoment [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    [DecidableEq α] [Fintype Y] [DecidableEq Y] (hh : IsTwoUniversal (PMF.uniformOfFintype ι) h)
    (hg : IsKWiseIndependentHash 2 g) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hw : 3 ≤ w * ε ^ 2) (hδ : (8 / 9 : ℝ) ^ r ≤ δ) (a : α) (m : ℕ) :
    (countSketchRandom h g sgn r).Solves δ (fun s est => |est a - s.count a| ≤
      ε * √(freqMoment 2 s : ℝ)) m := by
  classical
  intro s _
  rw [errorProb_countSketchRandom]
  simp only [not_le]
  have hV : 0 ≤ ∑ b ∈ s.toFinset.erase a, (s.count b : ℝ) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hVF : ∑ b ∈ s.toFinset.erase a, (s.count b : ℝ) ^ 2 ≤ freqMoment 2 s := by
    simp only [freqMoment, Nat.cast_sum, Nat.cast_pow]
    exact sum_le_sum_of_subset_of_nonneg (erase_subset a _) fun _ _ _ => sq_nonneg _
  refine (dens_countSketch_error_gt_le hh hg hsq hsum s a (by positivity) ?_).trans hδ
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  nlinarith [mul_nonneg (sub_nonneg.2 hw) hV, mul_nonneg (sub_nonneg.2 hw) (sub_nonneg.2 hVF)]

/-- On streams of at most `m` items, every counter of the Count-Sketch lies in `[-m, m]`. -/
theorem mem_Icc_state_countSketch_snd (hsgn : ∀ y, |sgn y| ≤ 1) (ω : Fin (2 * r) → ι × κ)
    {m : ℕ} {s : List α} (hs : s.length ≤ m) (i : Fin (2 * r)) (j : Fin w) :
    ((countSketch h g sgn r ω).state s).2 i j ∈ Icc (-(m : ℤ)) m := by
  rw [state_countSketch, mem_Icc]
  have hle : ∀ x ∈ s.map fun a => if h (ω i).1 a = j then sgn (g (ω i).2 a) else 0,
      |x| ≤ 1 := by
    simp only [List.mem_map]
    rintro _ ⟨a, -, rfl⟩
    split_ifs
    · exact hsgn _
    · simp only [abs_zero, zero_le_one]
  have hm : ((s.map fun a => if h (ω i).1 a = j then sgn (g (ω i).2 a) else 0).length : ℤ) ≤ m :=
    by rw [List.length_map]; exact_mod_cast hs
  constructor
  · have := List.length_nsmul_le_sum _ (-1 : ℤ) fun x hx => neg_le_of_abs_le (hle x hx)
    rw [nsmul_eq_mul, mul_neg_one] at this
    linarith
  · have := List.sum_le_length_nsmul _ (1 : ℤ) fun x hx => le_of_abs_le (hle x hx)
    rw [nsmul_eq_mul, mul_one] at this
    linarith

/-- **The memory of the randomized Count-Sketch** [Chakrabarti2025, Section 5.3.2]: every sketch it
draws uses at most `b` bits of memory on streams of at most `m` items when
`(2 m + 1) ^ (2 r w) ≤ 2 ^ b`. Under the public-coin convention of `Cslib.Streaming.Randomized`
only the `2 r w` counters are charged; the seeds are not. For the count with the seeds stored see
`Cslib.Streaming.exists_injOn_iUnion_reachable_countSketch`. -/
theorem spaceLE_countSketchRandom [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (hsgn : ∀ y, |sgn y| ≤ 1) {m b : ℕ} (hb : (2 * m + 1) ^ (2 * r * w) ≤ 2 ^ b) :
    (countSketchRandom h g sgn r).SpaceLE m b := by
  classical
  intro A hA
  rw [countSketchRandom, PMF.support_map] at hA
  obtain ⟨ω, -, rfl⟩ := hA
  refine Algorithm.spaceLE_of_subset_finset (T := {ω} ×ˢ
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    rw [mem_coe, mem_product, Fintype.mem_piFinset]
    refine ⟨?_, fun i => Fintype.mem_piFinset.2 fun j =>
      mem_Icc_state_countSketch_snd hsgn ω hs i j⟩
    rw [state_countSketch, mem_singleton]
  · have hc : (↑m + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    simp only [card_product, card_singleton, one_mul, Fintype.card_piFinset, Int.card_Icc, hc,
      prod_const, card_univ, Fintype.card_fin]
    rwa [← pow_mul, mul_comm w]

/-- **The memory of the Count-Sketch with its seeds stored** [Chakrabarti2025, Section 5.3.2]: on
streams of at most `m` items, the states reachable from all seeds together have a single injective
encoding by `b` bits as soon as `(|ι| |κ|) ^ (2 r) (2 m + 1) ^ (2 r w) ≤ 2 ^ b`. Since only the
initial memory depends on the seeds (`Cslib.Streaming.update_countSketch`,
`Cslib.Streaming.output_countSketch`), this is the memory of one algorithm whose initial memory is
random, with the seeds charged. -/
theorem exists_injOn_iUnion_reachable_countSketch [Fintype ι] [Fintype κ]
    (hsgn : ∀ y, |sgn y| ≤ 1) {m b : ℕ}
    (hb : (Fintype.card ι * Fintype.card κ) ^ (2 * r) * (2 * m + 1) ^ (2 * r * w) ≤ 2 ^ b) :
    ∃ enc : CountSketchState ι κ r w → BitString b,
      Set.InjOn enc (⋃ ω, (countSketch h g sgn r ω).reachable m) := by
  classical
  let T : Finset (CountSketchState ι κ r w) := (univ : Finset (Fin (2 * r) → ι × κ)) ×ˢ
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m
  refine Algorithm.exists_injOn_of_subset_finset (T := T) ?_ ?_
  · rintro _ ⟨_, ⟨ω, rfl⟩, s, hs, rfl⟩
    rw [mem_coe, mem_product, Fintype.mem_piFinset]
    exact ⟨mem_univ _, fun i => Fintype.mem_piFinset.2 fun j =>
      mem_Icc_state_countSketch_snd hsgn ω hs i j⟩
  · have hc : (↑m + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
    simp only [T, card_product, card_univ, Fintype.card_pi, Fintype.card_prod, Fintype.card_fin,
      prod_const, Fintype.card_piFinset, Int.card_Icc, hc]
    rwa [← pow_mul (2 * m + 1), mul_comm w]

end Cslib.Streaming
