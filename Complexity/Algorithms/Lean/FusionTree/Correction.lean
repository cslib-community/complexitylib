/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FusionTree.Sketch
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Arbitrary-query sketch correction

Correct the rank of an arbitrary query using the actual significant-bit sketch and the two
stored keys neighboring its inclusive sketch rank. Exact hits return that rank directly;
other queries use a second sketch rank at a prefix boundary. No word-RAM running-time bound
is asserted.

## Main definitions

* `upperRank`, `lowerRank`: inclusive and strict ranks in a finite sequence.
* `bestSketchNeighbor`: select between indices `t-1` and `t` at inclusive sketch rank `t`.
* `correctedRank`: the resulting arbitrary-query correction.

## Main results

* `highestDiff_mem_relevantBits_of_lt`: every stored pair's highest differing bit is selected.
* `exists_sketchNeighbor_prefix`: every nonempty query-prefix block contains a sketch neighbor.
* `exists_sketchNeighbor_min_highestDiff`: a sketch neighbor attains a globally longest prefix.
* `correctedRank_eq_upperRank`: correction gives the true inclusive rank for every bounded query.

## References

See [FredmanWillard1993] and
[MIT 6.851, Spring 2021, Lecture 12, handwritten page 4]
(https://courses.csail.mit.edu/6.851/spring21/lectures/L12.pdf).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

open Cslib.BitString

/-- Every pair of distinct stored keys has its highest differing bit among the adjacent-pair
bits, even when the keys are not adjacent. -/
theorem highestDiff_mem_relevantBits_of_lt {n w : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    {i j : Fin n} (hij : i < j) : highestDiff w (keys i) (keys j) ∈ relevantBits w keys := by
  suffices h : ∀ d (i j : Fin n), j.val = i.val + d + 1 →
      highestDiff w (keys i) (keys j) ∈ relevantBits w keys by
    exact h (j.val - i.val - 1) i j (by omega)
  intro d
  induction d with
  | zero =>
    intro i j hgap
    apply Finset.mem_image.mpr
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, by
      congr 2
      apply Fin.ext
      change i.val + 1 = j.val
      omega⟩
  | succ d ih =>
    intro i j hgap
    let k : Fin n := ⟨i.val + 1, by omega⟩
    have hik : i < k := by change i.val < i.val + 1; omega
    have hkj : k < j := by change i.val + 1 < j.val; omega
    let p := highestDiff w (keys i) (keys j)
    obtain ⟨hp, hdiff, habove⟩ := highestDiff_spec (hbound i) (hbound j)
      (Nat.ne_of_lt (hsorted (hik.trans hkj)))
    have hprefix := shiftRight_highestDiff_add_one_eq (hbound i) (hbound j)
      (Nat.ne_of_lt (hsorted (hik.trans hkj)))
    have hkprefix : keys k >>> (p + 1) = keys i >>> (p + 1) :=
      Nat.shiftRight_eq_of_between (hsorted hik).le (hsorted hkj).le hprefix
    have hkabove : ∀ b, p < b → (keys k).testBit b = (keys i).testBit b :=
      fun _ hb => Nat.testBit_eq_of_shiftRight_eq hkprefix (by omega)
    by_cases hbit : (keys i).testBit p = (keys k).testBit p
    · have heq : highestDiff w (keys k) (keys j) = p :=
        highestDiff_eq_of_testBit hp (by simpa only [← hbit] using hdiff)
          (fun b hb => (hkabove b hb).trans (habove b hb))
      change p ∈ relevantBits w keys
      rw [← heq]
      exact ih k j (by change j.val = (i.val + 1) + d + 1; omega)
    · have heq : highestDiff w (keys i) (keys k) = p :=
        highestDiff_eq_of_testBit hp hbit (fun b hb => (hkabove b hb).symm)
      change p ∈ relevantBits w keys
      rw [← heq]
      apply Finset.mem_image.mpr
      exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩

/-- A query sharing the larger stored key's prefix lies strictly above every sketch of a
smaller stored key outside that prefix block. -/
private theorem sketch_lt_query_of_prefix {n w cut q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    {i j : Fin n} (hij : i < j) (hprefix : keys j >>> cut = q >>> cut)
    (hne : keys i >>> cut ≠ q >>> cut) :
    sketch (relevantBits w keys) (keys i) < sketch (relevantBits w keys) q := by
  let p := highestDiff w (keys i) (keys j)
  have hp : cut ≤ p := by
    by_contra h
    have heq := (highestDiff_lt_iff_shiftRight_eq (hbound i) (hbound j)
      (Nat.ne_of_lt (hsorted hij))).mp (by omega : p < cut)
    exact hne (heq.trans hprefix)
  obtain ⟨h₀, h₁⟩ := highestDiff_bits_of_lt (hbound i) (hbound j) (hsorted hij)
  apply projectBits_lt (relevantBits w keys).sortedLT_sort.pairwise
    ((Finset.mem_sort _).mpr (highestDiff_mem_relevantBits_of_lt hsorted hbound hij)) h₀
  · exact (Nat.testBit_eq_of_shiftRight_eq hprefix hp).symm.trans h₁
  · intro b hb
    exact (testBit_eq_of_highestDiff_lt (hbound i) (hbound j) hb).trans
      (Nat.testBit_eq_of_shiftRight_eq hprefix (by omega))

/-- A query sharing the smaller stored key's prefix lies strictly below every sketch of a
larger stored key outside that prefix block. -/
private theorem query_lt_sketch_of_prefix {n w cut q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    {i j : Fin n} (hij : i < j) (hprefix : keys i >>> cut = q >>> cut)
    (hne : keys j >>> cut ≠ q >>> cut) :
    sketch (relevantBits w keys) q < sketch (relevantBits w keys) (keys j) := by
  let p := highestDiff w (keys i) (keys j)
  have hp : cut ≤ p := by
    by_contra h
    have heq := (highestDiff_lt_iff_shiftRight_eq (hbound i) (hbound j)
      (Nat.ne_of_lt (hsorted hij))).mp (by omega : p < cut)
    exact hne (heq.symm.trans hprefix)
  obtain ⟨h₀, h₁⟩ := highestDiff_bits_of_lt (hbound i) (hbound j) (hsorted hij)
  apply projectBits_lt (relevantBits w keys).sortedLT_sort.pairwise
    ((Finset.mem_sort _).mpr (highestDiff_mem_relevantBits_of_lt hsorted hbound hij))
    ((Nat.testBit_eq_of_shiftRight_eq hprefix hp).symm.trans h₀) h₁
  intro b hb
  exact (Nat.testBit_eq_of_shiftRight_eq hprefix (by omega)).symm.trans
    (testBit_eq_of_highestDiff_lt (hbound i) (hbound j) hb)

/-- The inclusive rank is the number of stored values at most the query. -/
def upperRank {n : ℕ} (values : Fin n → ℕ) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i => values i ≤ q).card

/-- The strict rank is the number of stored values strictly below the query. -/
def lowerRank {n : ℕ} (values : Fin n → ℕ) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i => values i < q).card

/-- An inclusive rank is a cut between zero and the number of stored values. -/
theorem upperRank_le {n : ℕ} (values : Fin n → ℕ) (q : ℕ) : upperRank values q ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

/-- In a sorted sequence, inclusive rank exactly characterizes the indices below its cut. -/
theorem lt_upperRank_iff {n q : ℕ} {values : Fin n → ℕ} (hsorted : StrictMono values)
    (i : Fin n) : i.val < upperRank values q ↔ values i ≤ q := by
  constructor
  · intro hi
    by_contra h
    have hsubset : (Finset.univ.filter fun j => values j ≤ q) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have := hsorted.monotone (le_of_not_gt hji)
      have := (Finset.mem_filter.mp hj).2
      omega
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iio] at hcard
    exact (not_le_of_gt hi) hcard
  · intro hi
    have hsubset : Finset.Iic i ⊆ (Finset.univ.filter fun j => values j ≤ q) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hsorted.monotone (Finset.mem_Iic.mp hj)).trans hi⟩
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Iic] at hcard
    exact hcard

/-- The immediate sketch neighbors of the inclusive query cut. At the endpoints there is
only one neighbor; in an empty sequence there are none. -/
def IsSketchNeighbor {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) (i : Fin n) : Prop :=
  i.val + 1 = upperRank (fun j => sketch (relevantBits w keys) (keys j))
      (sketch (relevantBits w keys) q) ∨
    i.val = upperRank (fun j => sketch (relevantBits w keys) (keys j))
      (sketch (relevantBits w keys) q)

/-- Every nonempty full-prefix block contains an immediate sketch neighbor of the query.
The query is arbitrary: it need not be a stored key or have a faithful sketch rank. -/
theorem exists_sketchNeighbor_prefix {n w q cut : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    (hprefix : ∃ i, keys i >>> cut = q >>> cut) :
    ∃ j, IsSketchNeighbor w keys q j ∧ keys j >>> cut = q >>> cut := by
  obtain ⟨i, hi⟩ := hprefix
  let values := fun j => sketch (relevantBits w keys) (keys j)
  let sq := sketch (relevantBits w keys) q
  let t := upperRank values sq
  have hmono : StrictMono values := strictMono_sketch hsorted hbound
  have ht : t ≤ n := upperRank_le values sq
  by_cases hit : i.val < t
  · let j : Fin n := ⟨t - 1, by omega⟩
    refine ⟨j, Or.inl (by change t - 1 + 1 = t; omega), ?_⟩
    by_contra hj
    have hle : values j ≤ sq := (lt_upperRank_iff hmono j).mp (by change t - 1 < t; omega)
    have hij : i ≤ j := by change i.val ≤ t - 1; omega
    have hne : i ≠ j := by intro heq; exact hj (heq ▸ hi)
    exact (not_lt_of_ge hle) (query_lt_sketch_of_prefix hsorted hbound
      (lt_of_le_of_ne hij hne) hi hj)
  · let j : Fin n := ⟨t, by omega⟩
    refine ⟨j, Or.inr rfl, ?_⟩
    by_contra hj
    have hlt : sq < values j := lt_of_not_ge (fun h =>
      (Nat.lt_irrefl t) ((lt_upperRank_iff hmono j).mpr h))
    have hji : j ≤ i := by change t ≤ i.val; omega
    have hne : j ≠ i := by intro heq; exact hj (heq.symm ▸ hi)
    exact (not_lt_of_ge hlt.le) (sketch_lt_query_of_prefix hsorted hbound
      (lt_of_le_of_ne hji hne) hi hj)

/-- For a query unequal to every stored key, an immediate sketch neighbor attains the longest
full common prefix, expressed as the minimum highest differing position. -/
theorem exists_sketchNeighbor_min_highestDiff {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w)
    (hn : 0 < n) (hmiss : ∀ i, keys i ≠ q) :
    ∃ j, IsSketchNeighbor w keys q j ∧
      ∀ i, highestDiff w (keys j) q ≤ highestDiff w (keys i) q := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun i => highestDiff w (keys i) q) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hprefix⟩ := exists_sketchNeighbor_prefix hsorted hbound
    ⟨i, shiftRight_highestDiff_add_one_eq (hbound i) hq (hmiss i)⟩
  have hle : highestDiff w (keys j) q ≤ highestDiff w (keys i) q := by
    have := (highestDiff_lt_iff_shiftRight_eq (hbound j) hq (hmiss j)).mpr hprefix
    omega
  exact ⟨j, hj, fun k => hle.trans (hi k (Finset.mem_univ _))⟩

/-- Minimizing over the at most two sketch neighbors therefore minimizes over every key. -/
private theorem min_highestDiff_of_sketchNeighbor {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w)
    (hmiss : ∀ i, keys i ≠ q) (j : Fin n)
    (hbest : ∀ i, IsSketchNeighbor w keys q i →
      highestDiff w (keys j) q ≤ highestDiff w (keys i) q) :
    ∀ i, highestDiff w (keys j) q ≤ highestDiff w (keys i) q := by
  obtain ⟨k, hk, hmin⟩ := exists_sketchNeighbor_min_highestDiff hsorted hbound hq
    (Nat.zero_lt_of_lt j.isLt) hmiss
  exact fun i => (hbest k hk).trans (hmin i)

/-- Every key sharing the query's prefix above the globally minimum differing bit differs
from the query at that bit. Thus none follows the query's branch there. -/
private theorem testBit_ne_of_min_highestDiff {n w q : ℕ} {keys : Fin n → ℕ}
    (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w) (hmiss : ∀ i, keys i ≠ q)
    (j : Fin n) (hmin : ∀ i, highestDiff w (keys j) q ≤ highestDiff w (keys i) q)
    (i : Fin n)
    (hprefix : keys i >>> (highestDiff w (keys j) q + 1) =
      q >>> (highestDiff w (keys j) q + 1)) :
    (keys i).testBit (highestDiff w (keys j) q) ≠ q.testBit (highestDiff w (keys j) q) := by
  have hlt := (highestDiff_lt_iff_shiftRight_eq (hbound i) hq (hmiss i)).mpr hprefix
  have heq : highestDiff w (keys i) q = highestDiff w (keys j) q := by
    have := hmin i
    omega
  simpa only [heq] using (highestDiff_spec (hbound i) hq (hmiss i)).2.1

/-- If the query takes the one branch at its first divergence from a longest-prefix key,
the true inclusive comparison equals the inclusive sketch comparison at the lower boundary. -/
private theorem le_iff_sketch_le_lowerBoundary {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w)
    (hmiss : ∀ i, keys i ≠ q) (j : Fin n)
    (hmin : ∀ i, highestDiff w (keys j) q ≤ highestDiff w (keys i) q)
    (hbit : q.testBit (highestDiff w (keys j) q) = true) (i : Fin n) :
    keys i ≤ q ↔ sketch (relevantBits w keys) (keys i) ≤
      sketch (relevantBits w keys) (lowerBoundary q (highestDiff w (keys j) q)) := by
  let p := highestDiff w (keys j) q
  have hjprefix : keys j >>> (p + 1) = q >>> (p + 1) :=
    shiftRight_highestDiff_add_one_eq (hbound j) hq (hmiss j)
  by_cases hiprefix : keys i >>> (p + 1) = q >>> (p + 1)
  · have hne := testBit_ne_of_min_highestDiff hbound hq hmiss j hmin i hiprefix
    have hi : (keys i).testBit p = false := by
      change (keys i).testBit p ≠ q.testBit p at hne
      cases h : (keys i).testBit p
      · rfl
      · exact False.elim (hne (h.trans hbit.symm))
    have hlt : keys i < q := Nat.lt_of_testBit p hi hbit
      (fun b hb => Nat.testBit_eq_of_shiftRight_eq hiprefix (by omega))
    exact iff_of_true hlt.le (sketch_le_lowerBoundary hiprefix hi)
  · have hiboundary : keys i >>> (p + 1) ≠ lowerBoundary q p >>> (p + 1) := by
      rwa [(boundary_prefix q p).1]
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hshift : keys i >>> (p + 1) < q >>> (p + 1) := by
        rw [← hjprefix]
        exact (Nat.lt_iff_shiftRight_lt_of_ne (fun h => hiprefix (h.trans hjprefix))).mp
          (hsorted hij)
      have hlt : keys i < q := (Nat.lt_iff_shiftRight_lt_of_ne hiprefix).mpr hshift
      have hslt := sketch_lt_query_of_prefix hsorted hbound hij
        (hjprefix.trans (boundary_prefix q p).1.symm) hiboundary
      exact iff_of_true hlt.le hslt.le
    · exact False.elim (hiprefix hjprefix)
    · have hshift : q >>> (p + 1) < keys i >>> (p + 1) := by
        rw [← hjprefix]
        exact (Nat.lt_iff_shiftRight_lt_of_ne (fun h => hiprefix (h.symm.trans hjprefix))).mp
          (hsorted hji)
      have hlt : q < keys i :=
        (Nat.lt_iff_shiftRight_lt_of_ne (Ne.symm hiprefix)).mpr hshift
      have hslt := query_lt_sketch_of_prefix hsorted hbound hji
        (hjprefix.trans (boundary_prefix q p).1.symm) hiboundary
      exact iff_of_false (not_le_of_gt hlt) (not_le_of_gt hslt)

/-- If the query takes the zero branch at its first divergence from a longest-prefix key,
the true inclusive comparison equals the strict sketch comparison at the upper boundary. -/
private theorem le_iff_sketch_lt_upperBoundary {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w)
    (hmiss : ∀ i, keys i ≠ q) (j : Fin n)
    (hmin : ∀ i, highestDiff w (keys j) q ≤ highestDiff w (keys i) q)
    (hbit : q.testBit (highestDiff w (keys j) q) = false) (i : Fin n) :
    keys i ≤ q ↔ sketch (relevantBits w keys) (keys i) <
      sketch (relevantBits w keys) (upperBoundary q (highestDiff w (keys j) q)) := by
  let p := highestDiff w (keys j) q
  have hjprefix : keys j >>> (p + 1) = q >>> (p + 1) :=
    shiftRight_highestDiff_add_one_eq (hbound j) hq (hmiss j)
  by_cases hiprefix : keys i >>> (p + 1) = q >>> (p + 1)
  · have hne := testBit_ne_of_min_highestDiff hbound hq hmiss j hmin i hiprefix
    have hi : (keys i).testBit p = true := by
      change (keys i).testBit p ≠ q.testBit p at hne
      cases h : (keys i).testBit p
      · exact False.elim (hne (h.trans hbit.symm))
      · rfl
    have hlt : q < keys i := Nat.lt_of_testBit p hbit hi
      (fun b hb => (Nat.testBit_eq_of_shiftRight_eq hiprefix (by omega)).symm)
    exact iff_of_false (not_le_of_gt hlt)
      (not_lt_of_ge (upperBoundary_le_sketch hiprefix hi))
  · have hiboundary : keys i >>> (p + 1) ≠ upperBoundary q p >>> (p + 1) := by
      rwa [(boundary_prefix q p).2]
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hshift : keys i >>> (p + 1) < q >>> (p + 1) := by
        rw [← hjprefix]
        exact (Nat.lt_iff_shiftRight_lt_of_ne (fun h => hiprefix (h.trans hjprefix))).mp
          (hsorted hij)
      have hlt : keys i < q := (Nat.lt_iff_shiftRight_lt_of_ne hiprefix).mpr hshift
      have hslt := sketch_lt_query_of_prefix hsorted hbound hij
        (hjprefix.trans (boundary_prefix q p).2.symm) hiboundary
      exact iff_of_true hlt.le hslt
    · exact False.elim (hiprefix hjprefix)
    · have hshift : q >>> (p + 1) < keys i >>> (p + 1) := by
        rw [← hjprefix]
        exact (Nat.lt_iff_shiftRight_lt_of_ne (fun h => hiprefix (h.symm.trans hjprefix))).mp
          (hsorted hji)
      have hlt : q < keys i :=
        (Nat.lt_iff_shiftRight_lt_of_ne (Ne.symm hiprefix)).mpr hshift
      have hslt := query_lt_sketch_of_prefix hsorted hbound hji
        (hjprefix.trans (boundary_prefix q p).2.symm) hiboundary
      exact iff_of_false (not_le_of_gt hlt) (not_lt_of_ge hslt.le)

/-- The second sketch query, with the comparison convention determined by the divergence bit. -/
def boundaryRank {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) (j : Fin n) : ℕ :=
  let p := highestDiff w (keys j) q
  let values := fun i => sketch (relevantBits w keys) (keys i)
  if q.testBit p then upperRank values (sketch (relevantBits w keys) (lowerBoundary q p))
  else lowerRank values (sketch (relevantBits w keys) (upperBoundary q p))

/-- The corrected sketch rank equals the true inclusive rank when `j` minimizes divergence
among the immediate sketch neighbors. This hypothesis is a comparison of at most two keys. -/
theorem boundaryRank_eq_upperRank {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w)
    (hmiss : ∀ i, keys i ≠ q) (j : Fin n)
    (hbest : ∀ i, IsSketchNeighbor w keys q i →
      highestDiff w (keys j) q ≤ highestDiff w (keys i) q) :
    boundaryRank w keys q j = upperRank keys q := by
  have hmin := min_highestDiff_of_sketchNeighbor hsorted hbound hq hmiss j hbest
  unfold boundaryRank
  dsimp only
  split
  · unfold upperRank
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (le_iff_sketch_le_lowerBoundary hsorted hbound hq hmiss j hmin
      (by assumption) i).symm
  · unfold lowerRank upperRank
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (le_iff_sketch_lt_upperBoundary hsorted hbound hq hmiss j hmin
      (by simpa only [Bool.not_eq_true] using ‹¬q.testBit (highestDiff w (keys j) q) = true›)
      i).symm

/-- The inclusive rank of a stored key is its index plus one. -/
theorem upperRank_apply {n : ℕ} {values : Fin n → ℕ} (hsorted : StrictMono values)
    (i : Fin n) : upperRank values (values i) = i.val + 1 := by
  have heq : (Finset.univ.filter fun j => values j ≤ values i) = Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
      hsorted.le_iff_le]
  simp only [upperRank, heq, Fin.card_Iic]

/-- An exact hit has its true inclusive rank already, before correction. -/
theorem upperRank_sketch_apply {n w : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (i : Fin n) :
    upperRank (fun j => sketch (relevantBits w keys) (keys j))
      (sketch (relevantBits w keys) (keys i)) = upperRank keys (keys i) := by
  rw [upperRank_apply (strictMono_sketch hsorted hbound), upperRank_apply hsorted]

/-- Initial inclusive rank of the uncorrected query sketch. -/
def sketchRank {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : ℕ :=
  upperRank (fun j => sketch (relevantBits w keys) (keys j)) (sketch (relevantBits w keys) q)

/-- The predecessor of the inclusive sketch cut, when present. -/
def sketchPredecessor {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : Option (Fin n) :=
  let t := sketchRank w keys q
  if h : 0 < t then some ⟨t - 1, by
    have := upperRank_le (fun j => sketch (relevantBits w keys) (keys j))
      (sketch (relevantBits w keys) q)
    change t ≤ n at this
    omega⟩
  else none

/-- The successor of the inclusive sketch cut, when present. -/
def sketchSuccessor {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : Option (Fin n) :=
  let t := sketchRank w keys q
  if h : t < n then some ⟨t, h⟩ else none

/-- The predecessor is precisely index `t-1`, using the inclusive convention. -/
theorem sketchPredecessor_eq_some_iff {n w q : ℕ} {keys : Fin n → ℕ} (i : Fin n) :
    sketchPredecessor w keys q = some i ↔ i.val + 1 = sketchRank w keys q := by
  unfold sketchPredecessor
  dsimp only
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · intro heq
      have := congrArg Fin.val heq
      dsimp only at this
      omega
    · intro hi
      apply Fin.ext
      dsimp only
      omega
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    omega

/-- The successor is precisely index `t`, using the inclusive convention. -/
theorem sketchSuccessor_eq_some_iff {n w q : ℕ} {keys : Fin n → ℕ} (i : Fin n) :
    sketchSuccessor w keys q = some i ↔ i.val = sketchRank w keys q := by
  unfold sketchSuccessor
  dsimp only
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
    exact eq_comm
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hi
    exact h (hi ▸ i.isLt)

/-- The two optional candidates are exactly the immediate sketch neighbors. -/
theorem isSketchNeighbor_iff {n w q : ℕ} {keys : Fin n → ℕ} (i : Fin n) :
    IsSketchNeighbor w keys q i ↔
      sketchPredecessor w keys q = some i ∨ sketchSuccessor w keys q = some i := by
  rw [sketchPredecessor_eq_some_iff, sketchSuccessor_eq_some_iff]
  rfl

/-- Compare at most two optional candidates by a natural-number score. -/
def chooseByScore {α : Type*} (score : α → ℕ) : Option α → Option α → Option α
  | none, b => b
  | a, none => a
  | some a, some b => if score a ≤ score b then some a else some b

/-- A chosen candidate belongs to the input pair and has minimum score among that pair. -/
theorem chooseByScore_spec {α : Type*} (score : α → ℕ) {a b : Option α} {j : α}
    (h : chooseByScore score a b = some j) :
    (a = some j ∨ b = some j) ∧
      ∀ i, (a = some i ∨ b = some i) → score j ≤ score i := by
  cases a with
  | none =>
    have hb : b = some j := h
    subst b
    refine ⟨Or.inr rfl, ?_⟩
    intro i hi
    have heq : j = i := by simpa using hi
    exact le_of_eq (congrArg score heq)
  | some a =>
    cases b with
    | none =>
      have ha : a = j := Option.some.inj h
      subst j
      refine ⟨Or.inl rfl, ?_⟩
      intro i hi
      have heq : a = i := by simpa using hi
      exact le_of_eq (congrArg score heq)
    | some b =>
      dsimp only [chooseByScore] at h
      split at h
      · rename_i hab
        have ha : a = j := Option.some.inj h
        subst j
        refine ⟨Or.inl rfl, ?_⟩
        intro i hi
        rcases hi with hi | hi
        · cases Option.some.inj hi
          exact le_rfl
        · cases Option.some.inj hi
          exact hab
      · rename_i hab
        have hb : b = j := Option.some.inj h
        subst j
        refine ⟨Or.inr rfl, ?_⟩
        intro i hi
        rcases hi with hi | hi
        · cases Option.some.inj hi
          exact le_of_not_ge hab
        · cases Option.some.inj hi
          exact le_rfl

/-- No candidate is selected exactly when both inputs are absent. -/
theorem chooseByScore_eq_none_iff {α : Type*} (score : α → ℕ) (a b : Option α) :
    chooseByScore score a b = none ↔ a = none ∧ b = none := by
  cases a with
  | none => simp [chooseByScore]
  | some a =>
    cases b with
    | none => simp [chooseByScore]
    | some b =>
      dsimp only [chooseByScore]
      split <;> simp

/-- Exact hits score zero; other keys are scored by their highest differing bit plus one. -/
def divergenceScore (w x q : ℕ) : ℕ := if x = q then 0 else highestDiff w x q + 1

/-- Select a longest-prefix candidate from the two sketch neighbors, preferring exact hits. -/
def bestSketchNeighbor {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : Option (Fin n) :=
  chooseByScore (fun i => divergenceScore w (keys i) q)
    (sketchPredecessor w keys q) (sketchSuccessor w keys q)

/-- The selected neighbor minimizes the divergence score among the two candidates. -/
theorem bestSketchNeighbor_spec {n w q : ℕ} {keys : Fin n → ℕ} {j : Fin n}
    (h : bestSketchNeighbor w keys q = some j) :
    IsSketchNeighbor w keys q j ∧
      ∀ i, IsSketchNeighbor w keys q i →
        divergenceScore w (keys j) q ≤ divergenceScore w (keys i) q := by
  obtain ⟨hj, hmin⟩ := chooseByScore_spec (fun i => divergenceScore w (keys i) q) h
  exact ⟨(isSketchNeighbor_iff j).mpr hj, fun i hi => hmin i ((isSketchNeighbor_iff i).mp hi)⟩

/-- A nonempty node always has at least one of the two sketch neighbors. -/
theorem bestSketchNeighbor_eq_none_iff {n w q : ℕ} {keys : Fin n → ℕ} :
    bestSketchNeighbor w keys q = none ↔ n = 0 := by
  constructor
  · intro h
    obtain ⟨hleft, hright⟩ :=
      (chooseByScore_eq_none_iff (fun i => divergenceScore w (keys i) q)
        (sketchPredecessor w keys q) (sketchSuccessor w keys q)).mp h
    by_contra hn
    have hn : 0 < n := Nat.pos_of_ne_zero hn
    by_cases ht : 0 < sketchRank w keys q
    · simp [sketchPredecessor, ht] at hleft
    · have ht : sketchRank w keys q = 0 := by omega
      simp [sketchSuccessor, ht, hn] at hright
  · intro hn
    subst n
    simp [bestSketchNeighbor, sketchPredecessor, sketchSuccessor, sketchRank, upperRank,
      chooseByScore]

/-- An exact stored hit is the predecessor of the inclusive sketch cut. -/
theorem isSketchNeighbor_of_eq {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (i : Fin n)
    (hi : keys i = q) : IsSketchNeighbor w keys q i := by
  apply Or.inl
  rw [← hi, upperRank_apply (strictMono_sketch hsorted hbound)]

/-- If the selected candidate is not an exact hit, then no stored key is an exact hit.
Only the two neighboring candidates are inspected by the selection function. -/
private theorem miss_of_bestSketchNeighbor {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) {j : Fin n}
    (hj : bestSketchNeighbor w keys q = some j) (hmiss : keys j ≠ q) :
    ∀ i, keys i ≠ q := by
  intro i hi
  have hscore := (bestSketchNeighbor_spec hj).2 i (isSketchNeighbor_of_eq hsorted hbound i hi)
  simp only [divergenceScore, ite_eq_right hmiss, ite_eq_left hi] at hscore
  omega

/-- Away from exact hits, the two-candidate selector minimizes the highest differing bit. -/
private theorem bestSketchNeighbor_highestDiff_le {n w q : ℕ} {keys : Fin n → ℕ}
    (hmiss : ∀ i, keys i ≠ q) {j : Fin n}
    (hj : bestSketchNeighbor w keys q = some j) (i : Fin n)
    (hi : IsSketchNeighbor w keys q i) :
    highestDiff w (keys j) q ≤ highestDiff w (keys i) q := by
  have hscore := (bestSketchNeighbor_spec hj).2 i hi
  simpa only [divergenceScore, ite_eq_right (hmiss j), ite_eq_right (hmiss i),
    Nat.add_le_add_iff_right] using hscore

/-- Arbitrary-query correction using two sketch neighbors. Exact hits return the initial
inclusive sketch rank directly. Otherwise a second sketch rank uses the appropriate boundary.
After taking sketch ranks, candidate selection and correction use at most two full-key values.
The sketches and rank primitives here are mathematical specifications, without a RAM-time bound. -/
def correctedRank {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) (q : ℕ) : ℕ :=
  match bestSketchNeighbor w keys q with
  | none => 0
  | some j => if keys j = q then sketchRank w keys q else boundaryRank w keys q j

/-- For every bounded query, correction of the actual significant-bit sketch gives the true
inclusive rank among the stored keys. This includes empty nodes, boundary cuts, and exact hits. -/
theorem correctedRank_eq_upperRank {n w q : ℕ} {keys : Fin n → ℕ}
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (hq : q < 2 ^ w) :
    correctedRank w keys q = upperRank keys q := by
  cases hj : bestSketchNeighbor w keys q with
  | none =>
    have hn := bestSketchNeighbor_eq_none_iff.mp hj
    subst n
    simp [correctedRank, hj, upperRank]
  | some j =>
    rw [correctedRank, hj]
    dsimp only
    by_cases hhit : keys j = q
    · rw [ite_eq_left hhit]
      unfold sketchRank
      rw [← hhit]
      exact upperRank_sketch_apply hsorted hbound j
    · rw [ite_eq_right hhit]
      have hmiss := miss_of_bestSketchNeighbor hsorted hbound hj hhit
      exact boundaryRank_eq_upperRank hsorted hbound hq hmiss j
        (fun i hi => bestSketchNeighbor_highestDiff_le hmiss hj i hi)

end Cslib.Algorithms.Lean.FusionTree
