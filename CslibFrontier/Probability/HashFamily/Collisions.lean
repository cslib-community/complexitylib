/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.UniversalHash
import CslibFrontier.Probability.PMF.Markov

/-!
# Expected collisions of universal hash families

A hash function `h : X → Y` sorts a finite key set `S` into buckets `{x ∈ S | h x = j}`. The
number `orderedCollisionCount h S` of ordered pairs of distinct keys sharing a bucket controls
both injectivity and the total squared bucket size:

* `h` is injective on `S` iff no pair collides (`orderedCollisionCount_eq_zero_iff`), and any
  collision is counted twice (`two_le_orderedCollisionCount`);
* `∑ⱼ bⱼ² = |S| + orderedCollisionCount h S`, where `bⱼ` is the size of bucket `j`
  (`sum_card_filter_sq`).

For an `ε`-universal family (`Cslib.Probability.IsUniversalHash`) and `|S| = n`, linearity of
expectation bounds the expected number of ordered collisions by `n (n - 1) ε`, that is twice the
`C(n, 2) ε` bound on unordered collisions. With a universal family into `m` values
(`Cslib.Probability.IsTwoUniversal`, `ε = 1 / m`) this gives the two estimates behind
Fredman–Komlós–Szemerédi perfect hashing [FredmanKomlosSzemeredi1984], in the form of [CLRS2009],
Section 11.5:

* if `n² ≤ m`, the hash is injective on `S` except with probability at most `1 / 2`
  (`IsTwoUniversal.toOuterMeasure_not_injOn_le`);
* if `n ≤ m`, the expected sum of squared bucket sizes is at most `2n - 1`
  (`IsTwoUniversal.tsum_sum_card_filter_sq_le`), so by Markov's inequality
  (`Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum`) it exceeds `4n` with probability at most
  `1 / 2` (`IsTwoUniversal.toOuterMeasure_four_mul_lt_sum_card_filter_sq_le`).

CLRS states the two probability bounds for `m = n²` and `m = n`, with strict inequalities
(`< 1 / 2`, and secondary storage `≥ 4n`). The forms here allow any `m` at least that large and
bound the probability by `≤ 1 / 2`; they are exactly what the construction's success tests use.

Expectations are `∑' i, seed i * f i` in `ℝ≥0∞` over an arbitrary seed law, and probabilities are
`PMF.toOuterMeasure`. These are information-theoretic statements; evaluation cost is separate.

## Main definitions

* `Cslib.Probability.orderedCollisionCount`: ordered pairs of distinct keys with equal hashes.

## Main results

* `Cslib.Probability.orderedCollisionCount_eq_zero_iff`,
  `Cslib.Probability.two_le_orderedCollisionCount`: collisions and injectivity.
* `Cslib.Probability.sum_card_filter_sq`: squared bucket sizes count collisions.
* `Cslib.Probability.IsUniversalHash.tsum_orderedCollisionCount_le`: expected collisions.
* `Cslib.Probability.IsUniversalHash.tsum_sum_card_filter_sq_le`: expected squared bucket sizes.
* `Cslib.Probability.IsTwoUniversal.toOuterMeasure_not_injOn_le`: injectivity into `n²` cells.
* `Cslib.Probability.IsTwoUniversal.tsum_sum_card_filter_sq_le`,
  `Cslib.Probability.IsTwoUniversal.toOuterMeasure_four_mul_lt_sum_card_filter_sq_le`: linear
  total squared bucket size into `n` cells.

## References

* [M. L. Fredman, J. Komlós, E. Szemerédi, *Storing a Sparse Table with O(1) Worst Case Access
  Time*][FredmanKomlosSzemeredi1984]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to Algorithms*, 3rd ed.,
  Section 11.5][CLRS2009]
-/

public section

namespace Cslib.Probability

open Finset
open scoped BigOperators ENNReal

variable {ι X Y : Type*}

/-- The number of ordered pairs `(x, y)` of distinct elements of `S` that `h` maps to the same
value. Each unordered colliding pair is counted twice. -/
@[expose] def orderedCollisionCount [DecidableEq Y] (h : X → Y) (S : Finset X) : ℕ :=
  (S.offDiag.filter fun p => h p.1 = h p.2).card

section Deterministic

variable [DecidableEq Y]

theorem orderedCollisionCount_eq_sum (h : X → Y) (S : Finset X) :
    orderedCollisionCount h S = ∑ p ∈ S.offDiag, if h p.1 = h p.2 then 1 else 0 := by
  rw [orderedCollisionCount, card_filter]

/-- `h` is injective on `S` exactly when no ordered pair of distinct elements collides. -/
theorem orderedCollisionCount_eq_zero_iff {h : X → Y} {S : Finset X} :
    orderedCollisionCount h S = 0 ↔ Set.InjOn h S := by
  rw [orderedCollisionCount, card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro hS x hx y hy hxy
    by_contra hne
    exact hS (x := (x, y)) (mem_offDiag.mpr ⟨hx, hy, hne⟩) hxy
  · rintro hS ⟨x, y⟩ hp hxy
    obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp hp
    exact hne (hS hx hy hxy)

/-- A collision of `x ≠ y` is counted as `(x, y)` and as `(y, x)`. -/
theorem two_le_orderedCollisionCount {h : X → Y} {S : Finset X} (hS : ¬ Set.InjOn h S) :
    2 ≤ orderedCollisionCount h S := by
  classical
  simp only [Set.InjOn, not_forall] at hS
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hS
  rw [orderedCollisionCount, ← card_pair (a := (x, y)) (b := (y, x)) (by simp [hne])]
  apply card_le_card
  intro p hp
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hx, hy, hne⟩, hxy⟩
  · exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hy, hx, Ne.symm hne⟩, hxy.symm⟩

/-- The sum of the squared bucket sizes counts each key with itself and every ordered colliding
pair: `∑ⱼ bⱼ² = |S| + #{(x, y) : x ≠ y, h x = h y}`. -/
theorem sum_card_filter_sq [Fintype Y] (h : X → Y) (S : Finset X) :
    ∑ j, (S.filter fun x => h x = j).card ^ 2 = S.card + orderedCollisionCount h S := by
  classical
  have hsq : ∀ j, (S.filter fun x => h x = j).card ^ 2 =
      ((S ×ˢ S).filter fun p => h p.1 = j ∧ h p.2 = j).card := by
    intro j
    rw [sq, ← card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [mem_product, mem_filter]
    tauto
  simp only [hsq]
  rw [← card_biUnion]
  · have hsplit : (univ : Finset Y).biUnion
          (fun j => (S ×ˢ S).filter fun p => h p.1 = j ∧ h p.2 = j) =
        S.diag ∪ S.offDiag.filter fun p => h p.1 = h p.2 := by
      ext ⟨x, y⟩
      simp only [mem_biUnion, mem_univ, mem_filter, mem_product, true_and, mem_union, mem_diag,
        mem_offDiag]
      constructor
      · rintro ⟨j, ⟨hx, hy⟩, hxj, hyj⟩
        by_cases hxy : x = y
        · exact Or.inl ⟨hx, hxy⟩
        · exact Or.inr ⟨⟨hx, hy, hxy⟩, hxj.trans hyj.symm⟩
      · rintro (⟨hx, rfl⟩ | ⟨⟨hx, hy, _⟩, hxy⟩)
        · exact ⟨h x, ⟨hx, hx⟩, rfl, rfl⟩
        · exact ⟨h x, ⟨hx, hy⟩, rfl, hxy.symm⟩
    rw [hsplit, card_union_of_disjoint, diag_card, orderedCollisionCount]
    exact disjoint_left.mpr fun p hp hp' =>
      (mem_offDiag.mp (mem_filter.mp hp').1).2.2 (mem_diag.mp hp).2
  · intro j _ j' _ hjj'
    exact disjoint_left.mpr fun p hp hp' =>
      hjj' ((mem_filter.mp hp).2.1.symm.trans (mem_filter.mp hp').2.1)

end Deterministic

variable [DecidableEq Y]

/-- **Expected collisions** of an `ε`-universal family: on a set of `n` keys the expected number of
ordered colliding pairs is at most `n (n - 1) ε`, twice the `C(n, 2) ε` bound for unordered pairs
([CLRS2009], Section 11.5). -/
theorem IsUniversalHash.tsum_orderedCollisionCount_le {seed : PMF ι} {hash : ι → X → Y}
    {ε : ℝ≥0∞} (hh : IsUniversalHash seed hash ε) (S : Finset X) :
    ∑' i, seed i * orderedCollisionCount (hash i) S ≤ (S.card * (S.card - 1) : ℕ) * ε := by
  have hpair : ∀ p ∈ S.offDiag,
      ∑' i, seed i * ((if hash i p.1 = hash i p.2 then 1 else 0 : ℕ) : ℝ≥0∞) ≤ ε := by
    intro p hp
    have hcoll := hh p.1 p.2 (mem_offDiag.mp hp).2.2
    rw [PMF.toOuterMeasure_apply] at hcoll
    refine le_of_eq_of_le (tsum_congr fun i => ?_) hcoll
    by_cases hi : hash i p.1 = hash i p.2
    · simp [hi]
    · simp [hi]
  calc ∑' i, seed i * (orderedCollisionCount (hash i) S : ℝ≥0∞)
      = ∑ p ∈ S.offDiag,
          ∑' i, seed i * ((if hash i p.1 = hash i p.2 then 1 else 0 : ℕ) : ℝ≥0∞) := by
        simp only [orderedCollisionCount_eq_sum, Nat.cast_sum, Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable
    _ ≤ ∑ _p ∈ S.offDiag, ε := sum_le_sum hpair
    _ = (S.card * (S.card - 1) : ℕ) * ε := by
        rw [sum_const, nsmul_eq_mul, offDiag_card, ← Nat.mul_sub_one]

/-- The expected sum of squared bucket sizes is `n` plus the expected number of ordered
collisions, so at most `n + n (n - 1) ε` for an `ε`-universal family. -/
theorem IsUniversalHash.tsum_sum_card_filter_sq_le [Fintype Y] {seed : PMF ι} {hash : ι → X → Y}
    {ε : ℝ≥0∞} (hh : IsUniversalHash seed hash ε) (S : Finset X) :
    ∑' i, seed i * ((∑ j, (S.filter fun x => hash i x = j).card ^ 2 : ℕ) : ℝ≥0∞) ≤
      S.card + (S.card * (S.card - 1) : ℕ) * ε := by
  classical
  simp only [sum_card_filter_sq, Nat.cast_add, mul_add]
  rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  exact add_le_add le_rfl (hh.tsum_orderedCollisionCount_le S)

omit [DecidableEq Y] in
/-- **Perfect hashing into `n²` cells** ([CLRS2009], Section 11.5): a universal family into at
least `n²` values is injective on a fixed set of `n` keys except with probability at most `1 / 2`.
CLRS states the strict bound `< 1 / 2` for exactly `n²` values; the non-strict form is what the
secondary level of the construction uses. -/
theorem IsTwoUniversal.toOuterMeasure_not_injOn_le [Fintype Y] {seed : PMF ι} {hash : ι → X → Y}
    (hh : IsTwoUniversal seed hash) (S : Finset X) (hS : S.card ^ 2 ≤ Fintype.card Y) :
    seed.toOuterMeasure {i | ¬ Set.InjOn (hash i) S} ≤ 2⁻¹ := by
  classical
  have hsub : {i | ¬ Set.InjOn (hash i) S} ⊆
      {i | (2 : ℝ≥0∞) ≤ (orderedCollisionCount (hash i) S : ℝ≥0∞)} := fun i hi => by
    have := two_le_orderedCollisionCount hi
    exact_mod_cast this
  have hle : ((S.card * (S.card - 1) : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact_mod_cast (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (sq S.card ▸ hS)
  rw [ENNReal.le_inv_iff_mul_le, mul_comm]
  calc 2 * seed.toOuterMeasure {i | ¬ Set.InjOn (hash i) S}
      ≤ 2 * seed.toOuterMeasure {i | (2 : ℝ≥0∞) ≤ (orderedCollisionCount (hash i) S : ℝ≥0∞)} := by
        gcongr
    _ ≤ ∑' i, seed i * (orderedCollisionCount (hash i) S : ℝ≥0∞) :=
        PMF.mul_toOuterMeasure_le_tsum seed _ 2
    _ ≤ 1 := (hh.tsum_orderedCollisionCount_le S).trans hle

/-- **Linear total secondary space** ([CLRS2009], Section 11.5): with a universal family into at
least `n` values, the expected sum of squared bucket sizes is at most `2n - 1`. -/
theorem IsTwoUniversal.tsum_sum_card_filter_sq_le [Fintype Y] {seed : PMF ι} {hash : ι → X → Y}
    (hh : IsTwoUniversal seed hash) (S : Finset X) (hS : S.card ≤ Fintype.card Y) :
    ∑' i, seed i * ((∑ j, (S.filter fun x => hash i x = j).card ^ 2 : ℕ) : ℝ≥0∞) ≤
      (2 * S.card - 1 : ℕ) := by
  classical
  refine (IsUniversalHash.tsum_sum_card_filter_sq_le hh S).trans ?_
  have hle : ((S.card * (S.card - 1) : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹ ≤
      (S.card - 1 : ℕ) := by
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm S.card]
    exact_mod_cast Nat.mul_le_mul_left _ hS
  calc (S.card : ℝ≥0∞) + ((S.card * (S.card - 1) : ℕ) : ℝ≥0∞) * (Fintype.card Y : ℝ≥0∞)⁻¹
      ≤ (S.card : ℝ≥0∞) + (S.card - 1 : ℕ) := add_le_add le_rfl hle
    _ = (2 * S.card - 1 : ℕ) := by
        rw [← Nat.cast_add]
        congr 1
        omega

/-- **Markov bound for the top level** ([CLRS2009], Section 11.5): with a universal family into
at least `n` values, the sum of squared bucket sizes exceeds `4n` with probability at most
`1 / 2`. CLRS bounds the probability of `≥ 4n` by `< 1 / 2` for exactly `n` values; the top-level
test of the construction accepts `≤ 4n`, so it needs the form stated here. -/
theorem IsTwoUniversal.toOuterMeasure_four_mul_lt_sum_card_filter_sq_le [Fintype Y]
    {seed : PMF ι} {hash : ι → X → Y} (hh : IsTwoUniversal seed hash) (S : Finset X)
    (hS : S.card ≤ Fintype.card Y) :
    seed.toOuterMeasure {i | 4 * S.card < ∑ j, (S.filter fun x => hash i x = j).card ^ 2} ≤
      2⁻¹ := by
  classical
  set P := seed.toOuterMeasure {i | 4 * S.card < ∑ j, (S.filter fun x => hash i x = j).card ^ 2}
  have hset : {i | 4 * S.card < ∑ j, (S.filter fun x => hash i x = j).card ^ 2} =
      {i | ((4 * S.card + 1 : ℕ) : ℝ≥0∞) ≤
        ((∑ j, (S.filter fun x => hash i x = j).card ^ 2 : ℕ) : ℝ≥0∞)} := by
    ext i
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
    omega
  have hmarkov : ((4 * S.card + 1 : ℕ) : ℝ≥0∞) * P ≤ (2 * S.card - 1 : ℕ) := by
    rw [show P = _ from congrArg seed.toOuterMeasure hset]
    exact (PMF.mul_toOuterMeasure_le_tsum seed _ _).trans (hh.tsum_sum_card_filter_sq_le S hS)
  have hne0 : ((4 * S.card + 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnetop : ((4 * S.card + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.le_inv_iff_mul_le, ← ENNReal.mul_le_mul_iff_right hne0 hnetop, mul_one]
  calc ((4 * S.card + 1 : ℕ) : ℝ≥0∞) * (P * 2) = 2 * (((4 * S.card + 1 : ℕ) : ℝ≥0∞) * P) := by
        ring
    _ ≤ 2 * (2 * S.card - 1 : ℕ) := by gcongr
    _ ≤ ((4 * S.card + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast (show 2 * (2 * S.card - 1) ≤ 4 * S.card + 1 by omega)

end Cslib.Probability
