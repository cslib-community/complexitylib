/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Streaming.Basic
public import Complexity.Computability.Streaming.Frequency
public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.MedianOfMeans
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Probability.KWiseIndependent.TugOfWar
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

/-!
# The AMS sketch for the second frequency moment

The `k`-th **frequency moment** of a stream is `F_k = ∑ₐ (count a s) ^ k`
(`Cslib.Streaming.freqMoment`). Alon, Matias and Szegedy estimate `F₂` in small space
[AlonMatiasSzegedy1999, Theorem 2.2]: a **tug-of-war counter** with seed `θ` adds a sign
`sgn (h θ a) = ±1` for each item `a`, so after the stream `s` it holds
`Z = ∑ₐ count a s · sgn (h θ a)`. For a four-wise independent family of signs of mean zero,
`𝔼 Z² = F₂` and `𝔼 (Z² - F₂)² ≤ 2 F₂²` (`Cslib.Probability.IsKWiseIndependentHash`, tug-of-war
moments). The **AMS sketch** (`Cslib.Streaming.amsSketch`) keeps `2 r` groups of `k` counters with
independent seeds and answers the median over the groups of the average of `Z²` in the group, the
median of means `Cslib.Probability.medianOfMeans` of `Z²`.

With `6 ≤ k η²` the answer is within `η F₂` of `F₂` except for an `(8 / 9) ^ r` fraction of the
seeds (`Cslib.Streaming.dens_amsSketch_error_le`); so the randomized sketch with uniform seeds
(`Cslib.Streaming.ams`) solves `F₂` estimation with error `δ ≥ (8 / 9) ^ r` on every stream
(`Cslib.Streaming.solves_ams`). Taking `k = ⌈6 / η²⌉` and `r = ⌈log (1 / δ) / log (9 / 8)⌉` uses
`O(η⁻² log δ⁻¹)` counters.

**Memory.** On streams of at most `m` items each counter lies in `[-m, m]`. Under the public-coin
convention of `Cslib.Streaming.Randomized` the seeds are drawn with the algorithm and are not
charged, so every sketch drawn uses at most `b` bits as soon as `(2 m + 1) ^ (2 r k) ≤ 2 ^ b`
(`Cslib.Streaming.spaceLE_ams`). Storing the seeds as well costs `2 r k log₂ |ι|` more bits. Only
the initial memory of the sketch depends on the seeds (`Cslib.Streaming.update_amsSketch`,
`Cslib.Streaming.output_amsSketch`), so the sketch is one algorithm with a random initial memory,
and one `b`-bit encoding of the states reachable from all seeds exists as soon as
`(|ι| (2 m + 1)) ^ (2 r k) ≤ 2 ^ b` (`Cslib.Streaming.exists_injOn_iUnion_reachable_amsSketch`),
that is `b = ⌈2 r k (log₂ |ι| + log₂ (2 m + 1))⌉` bits. With four-wise independent seeds of
`O(log n)` bits for a universe of size `n`, for instance from `Cslib.Probability.trinomialPolyHash`,
this seed-inclusive count is the `O(η⁻² log δ⁻¹ (log n + log m))` bound of
[AlonMatiasSzegedy1999, Theorem 2.2].

## Main definitions

* `Cslib.Streaming.amsSketch`: the AMS sketch with given seeds.
* `Cslib.Streaming.ams`: the randomized AMS sketch with uniform seeds.

## Main results

* `Cslib.Streaming.run_amsSketch`: the answer is the median of means of the squared tug-of-war
  sums.
* `Cslib.Streaming.init_amsSketch`, `Cslib.Streaming.update_amsSketch`,
  `Cslib.Streaming.output_amsSketch`: only the initial memory depends on the seeds.
* `Cslib.Streaming.dens_amsSketch_error_le`, `Cslib.Streaming.solves_ams`: the AMS sketch
  estimates `F₂` within `η F₂` except with probability `(8 / 9) ^ r`.
* `Cslib.Streaming.spaceLE_ams`: its memory under the public-coin convention, seeds not charged.
* `Cslib.Streaming.exists_injOn_iUnion_reachable_amsSketch`: its memory with the seeds stored.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

open Finset Probability
open scoped BigOperators

variable {ι α Y : Type*}

/-- The memory of the AMS sketch with `2 r` groups of `k` tug-of-war counters: a seed and a counter
for each of them. -/
abbrev AMSState (ι : Type*) (r k : ℕ) : Type _ :=
  (Fin (2 * r) → Fin k → ι) × (Fin (2 * r) → Fin k → ℤ)

/-- The **AMS sketch** for `F₂` [AlonMatiasSzegedy1999, Theorem 2.2] with seeds `ω`: the counter
with seed `θ` adds the sign `sgn (h θ a)` of each item `a`, and the answer is the median over the
`2 r` groups of the average square of the `k` counters in the group. The seeds are written in the
initial memory and read back by the update, which does not otherwise depend on `ω`
(`Cslib.Streaming.update_amsSketch`). -/
noncomputable def amsSketch (h : ι → α → Y) (sgn : Y → ℤ) (r k : ℕ)
    (ω : Fin (2 * r) → Fin k → ι) : Algorithm (AMSState ι r k) α ℝ where
  init := (ω, 0)
  update q a := (q.1, fun i l => q.2 i l + sgn (h (q.1 i l) a))
  output q := median fun i => 𝔼 l, ((q.2 i l : ℤ) : ℝ) ^ 2

/-- The randomized **AMS sketch**: the sketch with independent uniform seeds. -/
noncomputable def ams [Fintype ι] [Nonempty ι] (h : ι → α → Y) (sgn : Y → ℤ) (r k : ℕ) :
    Randomized (AMSState ι r k) α ℝ :=
  (PMF.uniformOfFintype (Fin (2 * r) → Fin k → ι)).map (amsSketch h sgn r k)

variable {h : ι → α → Y} {sgn : Y → ℤ} {r k : ℕ}

/-- The AMS sketch starts with its seeds and zero counters. -/
theorem init_amsSketch (ω : Fin (2 * r) → Fin k → ι) :
    (amsSketch h sgn r k ω).init = (ω, 0) := by
  simp only [amsSketch]

/-- The update of the AMS sketch reads the seeds from the memory: it does not depend on `ω`. -/
theorem update_amsSketch (ω : Fin (2 * r) → Fin k → ι) (q : AMSState ι r k) (a : α) :
    (amsSketch h sgn r k ω).update q a = (q.1, fun i l => q.2 i l + sgn (h (q.1 i l) a)) := by
  simp only [amsSketch]

/-- The output of the AMS sketch does not depend on its seeds. -/
theorem output_amsSketch (ω : Fin (2 * r) → Fin k → ι) (q : AMSState ι r k) :
    (amsSketch h sgn r k ω).output q = median fun i => 𝔼 l, ((q.2 i l : ℤ) : ℝ) ^ 2 := by
  simp only [amsSketch]

theorem stateFrom_amsSketch (ω : Fin (2 * r) → Fin k → ι) (q : AMSState ι r k) (s : List α) :
    (amsSketch h sgn r k ω).stateFrom q s =
      (q.1, fun i l => q.2 i l + (s.map fun a => sgn (h (q.1 i l) a)).sum) := by
  induction s generalizing q with
  | nil => simp only [Algorithm.stateFrom_nil, List.map_nil, List.sum_nil, add_zero]
  | cons a s ih =>
    rw [Algorithm.stateFrom_cons, ih]
    simp only [amsSketch, List.map_cons, List.sum_cons, add_assoc]

/-- After the stream `s`, the counter with seed `θ` holds `∑_{a ∈ s} sgn (h θ a)`. -/
theorem state_amsSketch (ω : Fin (2 * r) → Fin k → ι) (s : List α) :
    (amsSketch h sgn r k ω).state s = (ω, fun i l => (s.map fun a => sgn (h (ω i l) a)).sum) := by
  rw [Algorithm.state, stateFrom_amsSketch]
  simp only [amsSketch, Pi.zero_apply, zero_add]

/-- The answer of the AMS sketch is the median of means of the squared tug-of-war sums
`(∑ₐ count a s · sgn (h θ a)) ^ 2`. -/
theorem run_amsSketch [DecidableEq α] (ω : Fin (2 * r) → Fin k → ι) (s : List α) :
    (amsSketch h sgn r k ω).run s =
      medianOfMeans (fun θ => (∑ a ∈ s.toFinset, (s.count a : ℝ) * sgn (h θ a)) ^ 2) ω := by
  have hsum (θ : ι) : (((s.map fun a => sgn (h θ a)).sum : ℤ) : ℝ) =
      ∑ a ∈ s.toFinset, (s.count a : ℝ) * sgn (h θ a) := by
    rw [Finset.sum_list_map_count, Int.cast_sum]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  rw [Algorithm.run, state_amsSketch]
  simp only [amsSketch, medianOfMeans, hsum]

/-- **The AMS sketch estimates `F₂`** [AlonMatiasSzegedy1999, Theorem 2.2]: with a four-wise
independent family of signs of mean zero, and `6 ≤ k η²`, the AMS sketch with `2 r` groups of `k`
counters misses `F₂` by more than `η F₂` for at most an `(8 / 9) ^ r` fraction of the seeds. -/
theorem dens_amsSketch_error_le [Fintype ι] [DecidableEq α] [Fintype Y] [DecidableEq Y]
    (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    {η : ℝ} (hη : 0 < η) (hk : 6 ≤ k * η ^ 2) (s : List α) :
    (dens {ω : Fin (2 * r) → Fin k → ι |
      η * freqMoment 2 s < |(amsSketch h sgn r k ω).run s - freqMoment 2 s|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero]
    exact_mod_cast dens_le_one
  have hι := hh.nonempty
  have hε : ∀ y, ((sgn y : ℝ)) ^ 2 = 1 := fun y => by exact_mod_cast hsq y
  have hε₀ : 𝔼 y, (sgn y : ℝ) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, ← Int.cast_sum, hsum, Int.cast_zero, zero_div]
  have hF : ((freqMoment 2 s : ℕ) : ℝ) = ∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2 := by
    simp only [freqMoment, Nat.cast_sum, Nat.cast_pow]
  set g : ι → ℝ := fun θ => (∑ a ∈ s.toFinset, (s.count a : ℝ) * sgn (h θ a)) ^ 2
  have hmean : 𝔼 θ, g θ = ∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2 :=
    (hh.mono (by norm_num)).expect_sq_sum_mul_sign hε hε₀ _ _
  simp only [run_amsSketch, hF]
  rcases eq_or_ne s [] with rfl | hs
  · have hempty : ({ω : Fin (2 * r) → Fin k → ι | η * ∑ a ∈ ([] : List α).toFinset,
        (([] : List α).count a : ℝ) ^ 2 < |medianOfMeans (fun θ => (∑ a ∈ ([] : List α).toFinset,
          (([] : List α).count a : ℝ) * sgn (h θ a)) ^ 2) ω - ∑ a ∈ ([] : List α).toFinset,
            (([] : List α).count a : ℝ) ^ 2|} : Finset _) = ∅ := by
      have : Nonempty (Fin (2 * r)) := ⟨⟨0, by omega⟩⟩
      refine filter_false_of_mem fun ω _ => ?_
      simp only [List.toFinset_nil, sum_empty, mul_zero, sub_zero, not_lt, medianOfMeans,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, expect_const_zero, median_const,
        abs_zero, le_refl]
    rw [hempty, dens_empty, NNRat.cast_zero]
    positivity
  · have hpos : 0 < ∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2 := by
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
      refine sum_pos' (fun _ _ => by positivity) ⟨a, List.mem_toFinset.2 ha, ?_⟩
      exact pow_pos (Nat.cast_pos.2 (List.count_pos_iff.2 ha)) 2
    have hk0 : NeZero k := ⟨by rintro rfl; norm_num at hk⟩
    have hvar : 3 * 𝔼 θ, (g θ - 𝔼 θ', g θ') ^ 2 ≤
        k * (η * ∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2 := by
      rw [hmean]
      have := hh.expect_sq_sum_mul_sign_sub_sq_le hε hε₀ s.toFinset fun a => (s.count a : ℝ)
      have hF2 : 0 ≤ (∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2 := sq_nonneg _
      calc 3 * 𝔼 θ, (g θ - ∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2
          ≤ 3 * (2 * (∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2) := by gcongr
        _ = 6 * (∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2 := by ring
        _ ≤ k * η ^ 2 * (∑ a ∈ s.toFinset, ((s.count a : ℝ)) ^ 2) ^ 2 := by gcongr
        _ = _ := by ring
    have := dens_abs_medianOfMeans_sub_gt_le (r := r) g (by positivity) hvar
    rwa [hmean] at this

/-- The error of the randomized AMS sketch is the fraction of bad seeds. -/
theorem errorProb_ams [Fintype ι] [Nonempty ι] (R : List α → ℝ → Prop) (s : List α)
    [DecidablePred fun ω : Fin (2 * r) → Fin k → ι => ¬R s ((amsSketch h sgn r k ω).run s)] :
    (ams h sgn r k).errorProb R s =
      dens {ω : Fin (2 * r) → Fin k → ι | ¬R s ((amsSketch h sgn r k ω).run s)} :=
  Randomized.errorProb_map_uniformOfFintype _ R s

/-- **The AMS sketch solves `F₂` estimation** [AlonMatiasSzegedy1999, Theorem 2.2]: with a
four-wise independent family of signs of mean zero, `6 ≤ k η²` and `(8 / 9) ^ r ≤ δ`, the
randomized AMS sketch estimates `F₂` within `η F₂` with error at most `δ` on every stream. -/
theorem solves_ams [Fintype ι] [Nonempty ι] [DecidableEq α] [Fintype Y] [DecidableEq Y]
    (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    {η δ : ℝ} (hη : 0 < η) (hk : 6 ≤ k * η ^ 2) (hδ : (8 / 9 : ℝ) ^ r ≤ δ) (m : ℕ) :
    (ams h sgn r k).Solves δ (fun s Y => |Y - freqMoment 2 s| ≤ η * freqMoment 2 s) m := by
  classical
  intro s _
  rw [errorProb_ams]
  simp only [not_le]
  exact (dens_amsSketch_error_le hh hsq hsum hη hk s).trans hδ

/-- On streams of at most `m` items, every counter of the AMS sketch lies in `[-m, m]`. -/
theorem mem_Icc_state_amsSketch_snd (hsgn : ∀ y, |sgn y| ≤ 1) (ω : Fin (2 * r) → Fin k → ι)
    {m : ℕ} {s : List α} (hs : s.length ≤ m) (i : Fin (2 * r)) (l : Fin k) :
    ((amsSketch h sgn r k ω).state s).2 i l ∈ Icc (-(m : ℤ)) m := by
  rw [state_amsSketch, mem_Icc]
  exact abs_le.1 ((abs_sum_map_le (fun a => hsgn (h (ω i l) a)) s).trans
    (by exact_mod_cast hs : ((s.length : ℕ) : ℤ) ≤ m))

/-- **The memory of the randomized AMS sketch** [AlonMatiasSzegedy1999, Theorem 2.2]: every sketch
it draws uses at most `b` bits of memory on streams of at most `m` items when
`(2 m + 1) ^ (2 r k) ≤ 2 ^ b`. Under the public-coin convention of `Cslib.Streaming.Randomized`
only the `2 r k` counters are charged; the seeds are not. For the count with the seeds stored see
`Cslib.Streaming.exists_injOn_iUnion_reachable_amsSketch`. -/
theorem spaceLE_ams [Fintype ι] [Nonempty ι] (hsgn : ∀ y, |sgn y| ≤ 1) {m b : ℕ}
    (hb : (2 * m + 1) ^ (2 * r * k) ≤ 2 ^ b) :
    (ams h sgn r k).SpaceLE m b := by
  classical
  intro A hA
  rw [ams, PMF.support_map] at hA
  obtain ⟨ω, -, rfl⟩ := hA
  refine Algorithm.spaceLE_of_subset_finset (T := {ω} ×ˢ
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    rw [mem_coe, mem_product, Fintype.mem_piFinset]
    refine ⟨?_, fun i => Fintype.mem_piFinset.2 fun l => mem_Icc_state_amsSketch_snd hsgn ω hs i l⟩
    rw [state_amsSketch, mem_singleton]
  · rw [card_product, card_singleton, one_mul, card_piFinset_Icc, Fintype.card_fin,
      Fintype.card_fin]
    exact hb

/-- **The memory of the AMS sketch with its seeds stored** [AlonMatiasSzegedy1999, Theorem 2.2]:
on streams of at most `m` items, the states reachable from all seeds together have a single
injective encoding by `b` bits as soon as `(|ι| (2 m + 1)) ^ (2 r k) ≤ 2 ^ b`. Since only the
initial memory depends on the seeds (`Cslib.Streaming.update_amsSketch`,
`Cslib.Streaming.output_amsSketch`), this is the memory of one algorithm whose initial memory is
random, with the seeds charged. -/
theorem exists_injOn_iUnion_reachable_amsSketch [Fintype ι] (hsgn : ∀ y, |sgn y| ≤ 1) {m b : ℕ}
    (hb : (Fintype.card ι * (2 * m + 1)) ^ (2 * r * k) ≤ 2 ^ b) :
    ∃ enc : AMSState ι r k → BitString b,
      Set.InjOn enc (⋃ ω, (amsSketch h sgn r k ω).reachable m) := by
  classical
  let T : Finset (AMSState ι r k) := (univ : Finset (Fin (2 * r) → Fin k → ι)) ×ˢ
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m
  refine Algorithm.exists_injOn_of_subset_finset (T := T) ?_ ?_
  · rintro _ ⟨_, ⟨ω, rfl⟩, s, hs, rfl⟩
    rw [mem_coe, mem_product, Fintype.mem_piFinset]
    exact ⟨mem_univ _, fun i => Fintype.mem_piFinset.2 fun l =>
      mem_Icc_state_amsSketch_snd hsgn ω hs i l⟩
  · rw [card_product, card_piFinset_Icc, Fintype.card_fin, Fintype.card_fin, card_univ,
      Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Fintype.card_pi, prod_const,
      card_univ, Fintype.card_fin, ← pow_mul, mul_comm k, ← mul_pow]
    exact hb

end Cslib.Streaming
