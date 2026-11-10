/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.AMS
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.KWiseIndependent.TugOfWar
import CslibFrontier.Probability.KWiseIndependent.TugOfWarProduct
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

/-!
# The tug-of-war join signature for join sizes

The **join size** of two relations with frequency vectors `f` and `g` on a common join attribute is
the inner product `|F ⋈ G| = ∑ₐ fₐ gₐ`; for streams `u` and `v` of attribute values it is
`Cslib.Streaming.joinSize u v = ∑ₐ count a u · count a v`. Its self-join `joinSize u u` is the
second frequency moment `F₂ u` (`Cslib.Streaming.joinSize_self`), and `joinSize u v ^ 2 ≤ F₂ u F₂ v`
(`Cslib.Streaming.joinSize_sq_le`).

Alon, Gibbons, Matias and Szegedy [AlonGibbonsMatiasSzegedy1999, Section 4.3] estimate join sizes
with **tug-of-war join signatures**: each relation keeps a tug-of-war counter
`S(F) = ∑ₐ fₐ sgn (h θ a)` of the AMS sketch, with the seed `θ` shared by the two relations, and
`S(F) S(G)` estimates `|F ⋈ G|` with variance at most `2 F₂ F₂`
(`Cslib.Probability.IsKWiseIndependentHash.expect_sum_mul_sign_mul_sum_mul_sign`,
`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub_le`).

The **join sketch** (`Cslib.Streaming.joinSketch`) reads one stream of tagged items `α ⊕ α`: an item
`Sum.inl a` adds a tuple with attribute value `a` to the first relation and `Sum.inr a` to the
second, in any interleaving, so the relations are `s.filterMap Sum.getLeft?` and
`s.filterMap Sum.getRight?`. It keeps `2 r` groups of `k` seeds, each with one counter per
relation, and answers the median over the groups of the average product of the two counters
(`Cslib.Streaming.run_joinSketch`). Each relation's counters depend only on its own items
(`Cslib.Streaming.joinSketch_state_left`, `Cslib.Streaming.joinSketch_state_right`): they are the
AMS sketch of that relation with the shared seeds, so the two signatures could equally be maintained
separately and combined at query time, as in the source.

With a four-wise independent family of signs of mean zero and `6 ≤ k η²`, the answer is within
`η √(F₂(F) F₂(G))` of the join size except for an `(8 / 9) ^ r` fraction of the seeds
(`Cslib.Streaming.dens_joinSketch_error_le`, `Cslib.Streaming.solves_joinSketchRandom`). This is
[AlonGibbonsMatiasSzegedy1999, Theorem 4.5] with the median trick added: given a lower bound
`B₁ ≤ |F ⋈ G|` and upper bounds `F₂(F), F₂(G) ≤ B₂`, taking `6 B₂² ≤ k ε² B₁²` gives relative error
`ε` (`Cslib.Streaming.solves_joinSketchRandom_relative`), so `k = O(B₂² / (ε² B₁²))` copies suffice
as in the source, and `r = O(log δ⁻¹)` groups reduce the failure probability to `δ`.

**Memory.** On streams of at most `m` items every counter lies in `[-m, m]`. With the seeds not
charged (the public-coin convention of `Cslib.Streaming.Randomized`), every sketch drawn uses `b`
bits once `(2 m + 1) ^ (4 r k) ≤ 2 ^ b` (`Cslib.Streaming.spaceLE_joinSketchRandom`); with the
seeds stored, once `(|ι| (2 m + 1) ^ 2) ^ (2 r k) ≤ 2 ^ b`
(`Cslib.Streaming.exists_injOn_iUnion_reachable_joinSketch`). With the four-wise independent
polynomial hash families on a domain of `t` attribute values (`log₂ |ι| = O(log t)`), this is
`O(r k (log t + log m))` bits. In the source, `n` is the number of tuples in each relation, not
the domain size, and the hash functions are not charged, so its `k log n` bits per relation
count only the `k` counters, matching the public-coin bound above.

**Scope.** The relations are insert-only: the source also handles deletions by subtracting the
sign, which would need turnstile stream items, not formalized here. The answer is the median of
means rather than the source's plain mean, which gives the `(8 / 9) ^ r` failure bound in place of
Chebyshev's constant failure probability.

## Main definitions

* `Cslib.Streaming.joinSize`: the join size `∑ₐ count a u · count a v` of two streams.
* `Cslib.Streaming.JoinState`: the memory of the join sketch.
* `Cslib.Streaming.joinSketch`: the join sketch with given seeds.
* `Cslib.Streaming.joinSketchRandom`: the randomized join sketch with uniform seeds.

## Main results

* `Cslib.Streaming.joinSize_self`, `Cslib.Streaming.joinSize_comm`,
  `Cslib.Streaming.joinSize_sq_le`: the self-join is `F₂`, and `|F ⋈ G|² ≤ F₂(F) F₂(G)`.
* `Cslib.Streaming.joinSketch_state_left`, `Cslib.Streaming.joinSketch_state_right`,
  `Cslib.Streaming.run_joinSketch`: the counters are the AMS sketches of the two relations, and the
  answer is the median of means of their products.
* `Cslib.Streaming.dens_joinSketch_error_le`, `Cslib.Streaming.solves_joinSketchRandom`,
  `Cslib.Streaming.solves_joinSketchRandom_relative`: the join sketch estimates the join size within
  `η √(F₂(F) F₂(G))`, or within relative error `ε` under a priori bounds, except with probability
  `(8 / 9) ^ r`.
* `Cslib.Streaming.spaceLE_joinSketchRandom`,
  `Cslib.Streaming.exists_injOn_iUnion_reachable_joinSketch`: its memory without and with the
  seeds.

## References

* [N. Alon, P. B. Gibbons, Y. Matias, M. Szegedy, *Tracking join and self-join sizes in limited
  storage*, Section 4.3][AlonGibbonsMatiasSzegedy1999]
* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

open Finset Probability
open scoped BigOperators

variable {ι α Y : Type*}

/-! ### Join sizes -/

section JoinSize

variable [DecidableEq α]

/-- The **join size** `|F ⋈ G| = ∑ₐ count a u · count a v` of the relations whose join attribute
values are listed by the streams `u` and `v`: the inner product of their frequency vectors. -/
@[expose] def joinSize (u v : List α) : ℕ :=
  ∑ a ∈ u.toFinset, u.count a * v.count a

/-- The join size is the sum of `count a u · count a v` over any set of values containing those
of `u`. -/
theorem joinSize_eq_sum_of_subset {u v : List α} {T : Finset α} (hT : u.toFinset ⊆ T) :
    joinSize u v = ∑ a ∈ T, u.count a * v.count a := by
  unfold joinSize
  refine Finset.sum_subset hT fun a _ ha => ?_
  rw [List.mem_toFinset, ← List.count_eq_zero] at ha
  rw [ha, zero_mul]

theorem joinSize_comm (u v : List α) : joinSize u v = joinSize v u := by
  rw [joinSize_eq_sum_of_subset (T := u.toFinset ∪ v.toFinset) subset_union_left,
    joinSize_eq_sum_of_subset (T := u.toFinset ∪ v.toFinset) subset_union_right]
  exact sum_congr rfl fun a _ => mul_comm _ _

/-- The self-join size of a relation is its second frequency moment. -/
theorem joinSize_self (u : List α) : joinSize u u = freqMoment 2 u := by
  unfold joinSize freqMoment
  exact sum_congr rfl fun a _ => (sq _).symm

/-- **Join sizes are bounded by self-join sizes**: `|F ⋈ G|² ≤ F₂(F) F₂(G)`, by the
Cauchy–Schwarz inequality. -/
theorem joinSize_sq_le (u v : List α) :
    joinSize u v ^ 2 ≤ freqMoment 2 u * freqMoment 2 v := by
  have hT : u.toFinset ⊆ u.toFinset ∪ v.toFinset := subset_union_left
  rw [joinSize_eq_sum_of_subset hT, freqMoment_eq_sum_of_subset two_ne_zero hT,
    freqMoment_eq_sum_of_subset two_ne_zero subset_union_right]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

end JoinSize

/-! ### The join sketch -/

/-- The memory of the join sketch with `2 r` groups of `k` seeds: the seeds, and for each seed a
tug-of-war counter of each relation. -/
structure JoinState (ι : Type*) (r k : ℕ) where
  /-- The seed of each counter pair. -/
  seeds : Fin (2 * r) → Fin k → ι
  /-- The tug-of-war counters of the first relation. -/
  left : Fin (2 * r) → Fin k → ℤ
  /-- The tug-of-war counters of the second relation. -/
  right : Fin (2 * r) → Fin k → ℤ

/-- The **join sketch** [AlonGibbonsMatiasSzegedy1999, Section 4.3] with seeds `ω`, reading a
stream of tagged items: `Sum.inl a` adds the sign `sgn (h θ a)` to the first relation's counter with
seed `θ`, and `Sum.inr a` to the second relation's. The answer is the median over the `2 r` groups
of the average product of the two counters. The seeds are written in the initial memory and read
back by the update. -/
noncomputable def joinSketch (h : ι → α → Y) (sgn : Y → ℤ) (r k : ℕ)
    (ω : Fin (2 * r) → Fin k → ι) : Algorithm (JoinState ι r k) (α ⊕ α) ℝ where
  init := ⟨ω, 0, 0⟩
  update q := Sum.elim
    (fun a => ⟨q.seeds, fun i l => q.left i l + sgn (h (q.seeds i l) a), q.right⟩)
    (fun a => ⟨q.seeds, q.left, fun i l => q.right i l + sgn (h (q.seeds i l) a)⟩)
  output q := median fun i => 𝔼 l, ((q.left i l : ℤ) : ℝ) * ((q.right i l : ℤ) : ℝ)

/-- The randomized **join sketch**: the join sketch with independent uniform seeds. -/
noncomputable def joinSketchRandom [Fintype ι] [Nonempty ι] (h : ι → α → Y) (sgn : Y → ℤ)
    (r k : ℕ) : Randomized (JoinState ι r k) (α ⊕ α) ℝ :=
  (PMF.uniformOfFintype (Fin (2 * r) → Fin k → ι)).map (joinSketch h sgn r k)

variable {h : ι → α → Y} {sgn : Y → ℤ} {r k : ℕ}

private theorem stateFrom_joinSketch (ω : Fin (2 * r) → Fin k → ι) (q : JoinState ι r k)
    (s : List (α ⊕ α)) :
    (joinSketch h sgn r k ω).stateFrom q s =
      ⟨q.seeds, fun i l => q.left i l + ((s.filterMap Sum.getLeft?).map
        fun a => sgn (h (q.seeds i l) a)).sum,
        fun i l => q.right i l + ((s.filterMap Sum.getRight?).map
          fun a => sgn (h (q.seeds i l) a)).sum⟩ := by
  induction s generalizing q with
  | nil => simp only [Algorithm.stateFrom_nil, List.filterMap_nil, List.map_nil, List.sum_nil,
      add_zero]
  | cons x s ih =>
    rw [Algorithm.stateFrom_cons, ih]
    cases x with
    | inl a =>
      simp only [joinSketch, Sum.elim_inl, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, List.map_cons, List.sum_cons, add_assoc]
    | inr a =>
      simp only [joinSketch, Sum.elim_inr, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, List.map_cons, List.sum_cons, add_assoc]

/-- After the stream `s`, the counters with seed `θ` hold `∑_{a ∈ F} sgn (h θ a)` and
`∑_{a ∈ G} sgn (h θ a)`, where `F` and `G` are the items tagged `Sum.inl` and `Sum.inr`. -/
theorem state_joinSketch (ω : Fin (2 * r) → Fin k → ι) (s : List (α ⊕ α)) :
    (joinSketch h sgn r k ω).state s =
      ⟨ω, fun i l => ((s.filterMap Sum.getLeft?).map fun a => sgn (h (ω i l) a)).sum,
        fun i l => ((s.filterMap Sum.getRight?).map fun a => sgn (h (ω i l) a)).sum⟩ := by
  rw [Algorithm.state, stateFrom_joinSketch]
  simp only [joinSketch, Pi.zero_apply, zero_add]

/-- The first relation's counters are the AMS sketch of its items, with the shared seeds. -/
theorem joinSketch_state_left (ω : Fin (2 * r) → Fin k → ι) (s : List (α ⊕ α)) :
    ((joinSketch h sgn r k ω).state s).left =
      ((amsSketch h sgn r k ω).state (s.filterMap Sum.getLeft?)).2 := by
  rw [state_joinSketch, state_amsSketch]

/-- The second relation's counters are the AMS sketch of its items, with the shared seeds. -/
theorem joinSketch_state_right (ω : Fin (2 * r) → Fin k → ι) (s : List (α ⊕ α)) :
    ((joinSketch h sgn r k ω).state s).right =
      ((amsSketch h sgn r k ω).state (s.filterMap Sum.getRight?)).2 := by
  rw [state_joinSketch, state_amsSketch]

/-- A sum of signs over a stream is the sum over its values of the count times the sign. -/
private theorem cast_sum_map_sign [DecidableEq α] (u : List α) (θ : ι) :
    (((u.map fun a => sgn (h θ a)).sum : ℤ) : ℝ) =
      ∑ a ∈ u.toFinset, (u.count a : ℝ) * sgn (h θ a) := by
  rw [Finset.sum_list_map_count, Int.cast_sum]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- The answer of the join sketch is the median of means of the products of the tug-of-war sums of
the two relations. -/
theorem run_joinSketch [DecidableEq α] (ω : Fin (2 * r) → Fin k → ι) (s : List (α ⊕ α)) :
    (joinSketch h sgn r k ω).run s =
      medianOfMeans (fun θ =>
        (∑ a ∈ (s.filterMap Sum.getLeft?).toFinset,
          ((s.filterMap Sum.getLeft?).count a : ℝ) * sgn (h θ a)) *
        ∑ a ∈ (s.filterMap Sum.getRight?).toFinset,
          ((s.filterMap Sum.getRight?).count a : ℝ) * sgn (h θ a)) ω := by
  rw [Algorithm.run, state_joinSketch]
  simp only [joinSketch, medianOfMeans, cast_sum_map_sign]

/-- The median-of-means estimate from the tug-of-war sums of two streams `u` and `v` with shared
signs misses `joinSize u v` by more than `η √(F₂ u F₂ v)` for at most an `(8 / 9) ^ r` fraction of
the seeds. -/
private theorem dens_medianOfMeans_joinSize_error_le [Fintype ι] [DecidableEq α] [Fintype Y]
    [DecidableEq Y] (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1)
    (hsum : ∑ y, sgn y = 0) {η : ℝ} (hη : 0 < η) (hk : 6 ≤ k * η ^ 2) (u v : List α) :
    (dens {ω : Fin (2 * r) → Fin k → ι |
      η * √((freqMoment 2 u : ℝ) * freqMoment 2 v) <
        |medianOfMeans (fun θ => (∑ a ∈ u.toFinset, (u.count a : ℝ) * sgn (h θ a)) *
          ∑ a ∈ v.toFinset, (v.count a : ℝ) * sgn (h θ a)) ω - joinSize u v|} : ℝ) ≤
      (8 / 9) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero]
    exact_mod_cast dens_le_one
  have hι := hh.nonempty
  have hε : ∀ y, ((sgn y : ℝ)) ^ 2 = 1 := fun y => by exact_mod_cast hsq y
  have hε₀ : 𝔼 y, (sgn y : ℝ) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, ← Int.cast_sum, hsum, Int.cast_zero, zero_div]
  set T := u.toFinset ∪ v.toFinset
  have hsub {w : List α} (hw : w.toFinset ⊆ T) (θ : ι) :
      ∑ a ∈ w.toFinset, (w.count a : ℝ) * sgn (h θ a) = ∑ a ∈ T, (w.count a : ℝ) * sgn (h θ a) := by
    refine Finset.sum_subset hw fun a _ ha => ?_
    rw [List.mem_toFinset, ← List.count_eq_zero] at ha
    rw [ha, Nat.cast_zero, zero_mul]
  have hF {w : List α} (hw : w.toFinset ⊆ T) :
      ((freqMoment 2 w : ℕ) : ℝ) = ∑ a ∈ T, ((w.count a : ℝ)) ^ 2 := by
    rw [freqMoment_eq_sum_of_subset two_ne_zero hw]
    push_cast
    rfl
  have hJ : ((joinSize u v : ℕ) : ℝ) = ∑ a ∈ T, (u.count a : ℝ) * v.count a := by
    rw [joinSize_eq_sum_of_subset (T := T) subset_union_left]
    push_cast
    rfl
  set g : ι → ℝ := fun θ => (∑ a ∈ T, (u.count a : ℝ) * sgn (h θ a)) *
    ∑ a ∈ T, (v.count a : ℝ) * sgn (h θ a)
  have hg : (fun θ => (∑ a ∈ u.toFinset, (u.count a : ℝ) * sgn (h θ a)) *
      ∑ a ∈ v.toFinset, (v.count a : ℝ) * sgn (h θ a)) = g := by
    funext θ
    rw [hsub subset_union_left θ, hsub subset_union_right θ]
  have hmean : 𝔼 θ, g θ = joinSize u v := by
    rw [hJ]
    exact (hh.mono (by norm_num)).expect_sum_mul_sign_mul_sum_mul_sign hε hε₀ T _ _
  set B := (∑ a ∈ T, ((u.count a : ℝ)) ^ 2) * ∑ a ∈ T, ((v.count a : ℝ)) ^ 2
  have hB : ((freqMoment 2 u : ℕ) : ℝ) * freqMoment 2 v = B := by
    rw [hF subset_union_left, hF subset_union_right]
  have hvar : 𝔼 θ, (g θ - 𝔼 θ', g θ') ^ 2 ≤ 2 * B := by
    rw [hmean, hJ]
    exact hh.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub_le hε hε₀ T _ _
  rw [hg, hB, ← hmean]
  rcases (show 0 ≤ B by positivity).eq_or_lt with hB0 | hBpos
  · -- If one relation is empty, every estimate is exact.
    set μ := 𝔼 θ, g θ
    have hconst : ∀ θ, g θ = μ := by
      have h0 : 𝔼 θ, (g θ - μ) ^ 2 = 0 :=
        le_antisymm (by rw [← hB0, mul_zero] at hvar; exact hvar)
          (Finset.expect_nonneg fun _ _ => sq_nonneg _)
      intro θ
      have := (Finset.expect_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h0 θ (mem_univ θ)
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have hempty : ({ω : Fin (2 * r) → Fin k → ι |
        η * √B < |medianOfMeans g ω - μ|} : Finset _) = ∅ := by
      have : Nonempty (Fin (2 * r)) := ⟨⟨0, by omega⟩⟩
      refine filter_false_of_mem fun ω _ => ?_
      have hk0 : NeZero k := ⟨by rintro rfl; norm_num at hk⟩
      simp only [medianOfMeans, hconst, Fintype.expect_const, median_const, sub_self, abs_zero,
        not_lt]
      positivity
    rw [hempty, dens_empty, NNRat.cast_zero]
    positivity
  · have hk0 : NeZero k := ⟨by rintro rfl; norm_num at hk⟩
    have hvar3 : 3 * 𝔼 θ, (g θ - 𝔼 θ', g θ') ^ 2 ≤ k * (η * √B) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hBpos.le]
      nlinarith
    exact dens_abs_medianOfMeans_sub_gt_le g (mul_pos hη (Real.sqrt_pos.2 hBpos)) hvar3

/-- **The join sketch estimates join sizes** [AlonGibbonsMatiasSzegedy1999, Lemma 4.4 and
Theorem 4.5]: with a four-wise independent family of signs of mean zero and `6 ≤ k η²`, the join
sketch with `2 r` groups of `k` counter pairs misses the join size of the two relations by more
than `η √(F₂(F) F₂(G))` for at most an `(8 / 9) ^ r` fraction of the seeds. -/
theorem dens_joinSketch_error_le [Fintype ι] [DecidableEq α] [Fintype Y] [DecidableEq Y]
    (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1) (hsum : ∑ y, sgn y = 0)
    {η : ℝ} (hη : 0 < η) (hk : 6 ≤ k * η ^ 2) (s : List (α ⊕ α)) :
    (dens {ω : Fin (2 * r) → Fin k → ι |
      η * √((freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ) *
        freqMoment 2 (s.filterMap Sum.getRight?)) <
        |(joinSketch h sgn r k ω).run s -
          joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)|} : ℝ) ≤
      (8 / 9) ^ r := by
  simp only [run_joinSketch]
  exact dens_medianOfMeans_joinSize_error_le hh hsq hsum hη hk _ _

/-- The error of the randomized join sketch is the fraction of bad seeds. -/
theorem errorProb_joinSketchRandom [Fintype ι] [Nonempty ι] (R : List (α ⊕ α) → ℝ → Prop)
    (s : List (α ⊕ α))
    [DecidablePred fun ω : Fin (2 * r) → Fin k → ι => ¬R s ((joinSketch h sgn r k ω).run s)] :
    (joinSketchRandom h sgn r k).errorProb R s =
      dens {ω : Fin (2 * r) → Fin k → ι | ¬R s ((joinSketch h sgn r k ω).run s)} :=
  Randomized.errorProb_map_uniformOfFintype _ R s

/-- **The join sketch solves join size estimation** [AlonGibbonsMatiasSzegedy1999, Theorem 4.5]:
with a four-wise independent family of signs of mean zero, `6 ≤ k η²` and `(8 / 9) ^ r ≤ δ`, the
randomized join sketch estimates the join size of the two relations within `η √(F₂(F) F₂(G))` with
error at most `δ` on every stream. -/
theorem solves_joinSketchRandom [Fintype ι] [Nonempty ι] [DecidableEq α] [Fintype Y]
    [DecidableEq Y] (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1)
    (hsum : ∑ y, sgn y = 0) {η δ : ℝ} (hη : 0 < η) (hk : 6 ≤ k * η ^ 2)
    (hδ : (8 / 9 : ℝ) ^ r ≤ δ) (m : ℕ) :
    (joinSketchRandom h sgn r k).Solves δ (fun s J =>
      |J - joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)| ≤
        η * √((freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ) *
          freqMoment 2 (s.filterMap Sum.getRight?))) m := by
  classical
  intro s _
  rw [errorProb_joinSketchRandom]
  simp only [not_le]
  exact (dens_joinSketch_error_le hh hsq hsum hη hk s).trans hδ

/-- **Relative error under a priori bounds** [AlonGibbonsMatiasSzegedy1999, Theorem 4.5]: if the
join size is known to be at least `B₁ > 0` and the self-join sizes at most `B₂`, then
`k ≥ 6 B₂² / (ε² B₁²)` counter pairs per group give relative error `ε` except with probability
`(8 / 9) ^ r`. -/
theorem solves_joinSketchRandom_relative [Fintype ι] [Nonempty ι] [DecidableEq α] [Fintype Y]
    [DecidableEq Y] (hh : IsKWiseIndependentHash 4 h) (hsq : ∀ y, sgn y ^ 2 = 1)
    (hsum : ∑ y, sgn y = 0) {ε B₁ B₂ δ : ℝ} (hε : 0 < ε) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hk : 6 * B₂ ^ 2 ≤ k * ε ^ 2 * B₁ ^ 2) (hδ : (8 / 9 : ℝ) ^ r ≤ δ) (m : ℕ) :
    (joinSketchRandom h sgn r k).Solves δ (fun s J =>
      B₁ ≤ joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?) →
      (freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ) ≤ B₂ →
      (freqMoment 2 (s.filterMap Sum.getRight?) : ℝ) ≤ B₂ →
      |J - joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)| ≤
        ε * joinSize (s.filterMap Sum.getLeft?) (s.filterMap Sum.getRight?)) m := by
  classical
  have hη : 0 < ε * B₁ / B₂ := by positivity
  have hkη : 6 ≤ k * (ε * B₁ / B₂) ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  intro s _
  rw [errorProb_joinSketchRandom]
  refine le_trans ?_ ((dens_joinSketch_error_le hh hsq hsum hη hkη s).trans hδ)
  refine NNRat.cast_le.2 (dens_le_dens fun ω hω => ?_)
  simp only [mem_filter, mem_univ, true_and, Classical.not_imp, not_le] at hω ⊢
  obtain ⟨hJ, hF, hG, hlt⟩ := hω
  refine lt_of_le_of_lt ?_ hlt
  set F := (freqMoment 2 (s.filterMap Sum.getLeft?) : ℝ)
  set G := (freqMoment 2 (s.filterMap Sum.getRight?) : ℝ)
  have hFG : √(F * G) ≤ B₂ :=
    calc √(F * G) ≤ √(B₂ * B₂) :=
          Real.sqrt_le_sqrt (mul_le_mul hF hG (Nat.cast_nonneg _) hB₂.le)
      _ = B₂ := Real.sqrt_mul_self hB₂.le
  calc ε * B₁ / B₂ * √(F * G) ≤ ε * B₁ / B₂ * B₂ := by gcongr
    _ = ε * B₁ := by field_simp
    _ ≤ _ := by gcongr

/-- On streams of at most `m` items, every counter of the join sketch lies in `[-m, m]`. -/
theorem mem_Icc_joinSketch_state (hsgn : ∀ y, |sgn y| ≤ 1) (ω : Fin (2 * r) → Fin k → ι)
    {m : ℕ} {s : List (α ⊕ α)} (hs : s.length ≤ m) (i : Fin (2 * r)) (l : Fin k) :
    ((joinSketch h sgn r k ω).state s).left i l ∈ Icc (-(m : ℤ)) m ∧
      ((joinSketch h sgn r k ω).state s).right i l ∈ Icc (-(m : ℤ)) m := by
  rw [joinSketch_state_left, joinSketch_state_right]
  exact ⟨mem_Icc_state_amsSketch_snd hsgn ω ((List.length_filterMap_le _ _).trans hs) i l,
    mem_Icc_state_amsSketch_snd hsgn ω ((List.length_filterMap_le _ _).trans hs) i l⟩

/-- The memory of the join sketch as a triple. -/
private def JoinState.equivProd :
    JoinState ι r k ≃ (Fin (2 * r) → Fin k → ι) × (Fin (2 * r) → Fin k → ℤ) ×
      (Fin (2 * r) → Fin k → ℤ) where
  toFun q := (q.seeds, q.left, q.right)
  invFun := fun ⟨ω, L, R⟩ => ⟨ω, L, R⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- The states of the join sketch with seeds in `W` and counters in `[-m, m]`. -/
private def joinStates (W : Finset (Fin (2 * r) → Fin k → ι)) (m : ℕ) :
    Finset (JoinState ι r k) :=
  (W ×ˢ ((Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m) ×ˢ
    (Fintype.piFinset fun _ => Fintype.piFinset fun _ => Icc (-(m : ℤ)) m))).map
      JoinState.equivProd.symm.toEmbedding

private theorem card_joinStates (W : Finset (Fin (2 * r) → Fin k → ι)) (m : ℕ) :
    #(joinStates W m) = #W * ((2 * m + 1) ^ 2) ^ (2 * r * k) := by
  rw [joinStates, card_map, card_product, card_product, card_piFinset_Icc, ← mul_pow, ← sq]

private theorem state_mem_joinStates (hsgn : ∀ y, |sgn y| ≤ 1)
    {W : Finset (Fin (2 * r) → Fin k → ι)} {ω : Fin (2 * r) → Fin k → ι} (hω : ω ∈ W) {m : ℕ}
    {s : List (α ⊕ α)} (hs : s.length ≤ m) :
    (joinSketch h sgn r k ω).state s ∈ joinStates W m := by
  rw [joinStates, mem_map_equiv, Equiv.symm_symm]
  simp only [JoinState.equivProd, Equiv.coe_fn_mk, mem_product, Fintype.mem_piFinset]
  refine ⟨?_, fun i l => (mem_Icc_joinSketch_state hsgn ω hs i l).1,
    fun i l => (mem_Icc_joinSketch_state hsgn ω hs i l).2⟩
  rw [state_joinSketch]
  exact hω

/-- **The memory of the randomized join sketch** [AlonGibbonsMatiasSzegedy1999, Section 4.3]:
every sketch it draws uses at most `b` bits of memory on streams of at most `m` items when
`(2 m + 1) ^ (4 r k) ≤ 2 ^ b`. Under the public-coin convention of `Cslib.Streaming.Randomized`
only the `4 r k` counters are charged; the seeds are not. For the count with the seeds stored see
`Cslib.Streaming.exists_injOn_iUnion_reachable_joinSketch`. -/
theorem spaceLE_joinSketchRandom [Fintype ι] [Nonempty ι] (hsgn : ∀ y, |sgn y| ≤ 1) {m b : ℕ}
    (hb : (2 * m + 1) ^ (4 * r * k) ≤ 2 ^ b) :
    (joinSketchRandom h sgn r k).SpaceLE m b := by
  classical
  intro A hA
  rw [joinSketchRandom, PMF.support_map] at hA
  obtain ⟨ω, -, rfl⟩ := hA
  refine Algorithm.spaceLE_of_subset_finset (T := joinStates {ω} m) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact state_mem_joinStates hsgn (mem_singleton_self ω) hs
  · rw [card_joinStates, card_singleton, one_mul, ← pow_mul,
      show 2 * (2 * r * k) = 4 * r * k by ring]
    exact hb

/-- **The memory of the join sketch with its seeds stored** [AlonGibbonsMatiasSzegedy1999,
Section 4.3]: on streams of at most `m` items, the states reachable from all seeds together have a
single injective encoding by `b` bits as soon as `(|ι| (2 m + 1) ^ 2) ^ (2 r k) ≤ 2 ^ b`. -/
theorem exists_injOn_iUnion_reachable_joinSketch [Fintype ι] (hsgn : ∀ y, |sgn y| ≤ 1)
    {m b : ℕ} (hb : (Fintype.card ι * (2 * m + 1) ^ 2) ^ (2 * r * k) ≤ 2 ^ b) :
    ∃ enc : JoinState ι r k → BitString b,
      Set.InjOn enc (⋃ ω, (joinSketch h sgn r k ω).reachable m) := by
  classical
  refine Algorithm.exists_injOn_of_subset_finset (T := joinStates univ m) ?_ ?_
  · rintro _ ⟨_, ⟨ω, rfl⟩, s, hs, rfl⟩
    exact state_mem_joinStates hsgn (mem_univ ω) hs
  · rw [card_joinStates, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
      Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm k, ← mul_pow]
    exact hb

end Cslib.Streaming
