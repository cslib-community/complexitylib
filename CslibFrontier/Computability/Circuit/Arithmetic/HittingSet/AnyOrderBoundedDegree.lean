/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AnyOrder
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorComponentEval
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.BoundedDegreeShifts
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorDegree

/-!
# Hitting sets for any-order ROABPs of bounded individual degree

Over a field of characteristic zero, `boundedDegreeHittingSet F n w δ` is an explicit set of
points on which no nonzero polynomial in `n` variables of individual degree at most `δ` computed
by read-once oblivious branching programs of width `w` in every variable order vanishes
(`isHittingSet_boundedDegreeHittingSet_roabp`). For `δ = 1` this is Theorem 1.1 of Shpilka
[Shpilka2026], formalized in
`CslibFrontier/Computability/Circuit/Arithmetic/HittingSet/AnyOrder.lean`. For every fixed
`δ` the size of the set is polynomial in `n` and `w` (`card_boundedDegreeHittingSet_le`).

**Scope.** The bound is `(n w) ^ O(δ) * (δ + 1) ^ O(log w)`: exponential in `δ`. The question of
[Shpilka2026, §4], a set of size polynomial in `n`, `w` and `δ` together, is not answered.
Characteristic zero only. The statement for `δ ≥ 2` and its proof are not taken from a
source and have not been refereed. As in the multilinear case the class that is hit is
defined by split ranks (`MvPolynomial.SplitRankLE`) and contains the branching programs
(`IsAnyOrderROABP.splitRankLE`).

## Proof

1. Some shift `a₀` from `boundedDegreeShifts` gives `G = f (X + a₀)` a monomial `m` with
   `r ≤ ⌊lg w⌋` variables (`exists_mem_boundedDegreeShifts`).
2. A colouring `h` with `r` colours from `Cslib.perfectHashFamily` separates the variables of
   `m`. Let `ε` be the colour degree of `m`, with entries at most `δ`, and
   `g = colorComponent h ε G`: nonzero, of split rank at most `w` across unions of colour
   classes.
3. `g` is nonzero at a point `x` of `colorHittingSet F h w (δ * n) δ`
   (`exists_mem_colorHittingSet_eval_ne_zero`). For `δ ≥ 2`, `g` need not lie in a
   small space closed under partial derivatives, but one derivative per colour lowers the
   colour degree, and the recursion ends with polynomials that have at most one variable per
   colour.
4. `g x` is recovered from values of `G` at the points `z • y ⊙ x`, by a finite difference in
   the scaling `y` of each colour (`exists_eval_ne_zero_of_eval_colorComponent_ne_zero`).

## Main definitions

* `boundedDegreeHittingSet`: the hitting set.

## Main results

* `isHittingSet_boundedDegreeHittingSet`: it hits the polynomials of individual degree at most
  `δ` and split rank at most `w` across every split.
* `isHittingSet_boundedDegreeHittingSet_roabp`: it hits the any-order ROABPs of individual
  degree at most `δ` and width `w`.
* `card_boundedDegreeHittingSet_le`: its size.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Theorem 1.1 and §4 (unrefereed preprint)
* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] (n w δ : ℕ)

open scoped Classical in
/-- The hitting set for polynomials in `n` variables of individual degree at most `δ` and split
rank at most `w` across every split: the concentrating shifts `a₀`, together with the points
`a₀ + z • y ⊙ x`, where `h` is a colouring with `r ≤ ⌊lg w⌋` colours from the perfect hash
family, `x` is a point of `colorHittingSet F h w (δ * n) δ`, `y` scales the variables of each
colour by `0, …, δ`, and `z = 0, …, δ * n`. -/
noncomputable def boundedDegreeHittingSet : Finset (Fin n → F) :=
  boundedDegreeShifts F δ (perfectHashFamily n (Nat.log 2 w + 1)) ∪
    (range (Nat.log 2 w + 1)).biUnion fun r =>
      (boundedDegreeShifts F δ (perfectHashFamily n (Nat.log 2 w + 1)) ×ˢ
        (perfectHashFamily n r).sigma (fun h => colorHittingSet F h w (δ * n) δ) ×ˢ
        (univ : Finset (Fin r → Fin (δ + 1))) ×ˢ range (δ * n + 1)).image
        fun ⟨a₀, ⟨h, x⟩, y, z⟩ v => a₀ v + (z : F) * ((y (h v) : ℕ) : F) * x v

variable {F n w δ}

omit [CharZero F] in
private theorem totalDegree_le_mul {f : MvPolynomial (Fin n) F}
    (h : ∀ i, f.degreeOf i ≤ δ) : f.totalDegree ≤ δ * n :=
  Finset.sup_le fun m hm =>
    calc (m.sum fun _ e => e) ≤ ∑ j ∈ m.support, δ :=
          Finset.sum_le_sum fun j _ => (monomial_le_degreeOf j hm).trans (h j)
      _ ≤ δ * n := by
          rw [sum_const, smul_eq_mul, mul_comm]
          exact Nat.mul_le_mul_left _ ((card_le_univ _).trans_eq (Fintype.card_fin n))

/-- **Hitting set for bounded individual degree and small split rank.** Over a field of
characteristic zero, `boundedDegreeHittingSet F n w δ` hits every polynomial in `n` variables
of individual degree at most `δ` that is a sum of `w` products across every split of its
variables. -/
theorem isHittingSet_boundedDegreeHittingSet :
    IsHittingSet (boundedDegreeHittingSet F n w δ)
      {f | (∀ i, f.degreeOf i ≤ δ) ∧
        ∀ U : Finset (Fin n), SplitRankLE (U : Set (Fin n)) w f} := by
  classical
  rintro f ⟨hdeg, hsplit⟩ hf0
  obtain ⟨a₀, ha₀, m, hm, hmL⟩ := exists_mem_boundedDegreeShifts
    (isPerfectHashFamily_perfectHashFamily n _ (Nat.succ_pos _))
    (Nat.lt_pow_succ_log_self (by norm_num) w) hf0 hdeg fun Y _ => hsplit Y
  set G := shift a₀ f with hG
  have hGdeg : ∀ i, G.degreeOf i ≤ δ := fun i => (degreeOf_shift_le a₀ f i).trans (hdeg i)
  have hGtot : G.totalDegree ≤ δ * n := totalDegree_le_mul hGdeg
  rcases Nat.eq_zero_or_pos m.support.card with h0 | hpos
  · refine ⟨a₀, mem_union_left _ ha₀, ?_⟩
    have hm0 : m = 0 := Finsupp.support_eq_empty.1 (card_eq_zero.1 h0)
    have h := eval_shift a₀ 0 f
    rw [eval_zero, constantCoeff_eq] at h
    simp only [Pi.zero_apply, zero_add] at h
    rw [← h]
    exact hm0 ▸ mem_support_iff.1 hm
  · obtain ⟨h, hh, hinj⟩ := isPerfectHashFamily_perfectHashFamily n _ hpos m.support rfl
    set ε := Finsupp.weight (colorWeight h) m with hεdef
    -- every colour is the colour of exactly one variable of `m`
    have hε : ∀ i, ε i ≤ δ := by
      intro i
      have hsurj : m.support.image h = univ :=
        eq_univ_of_card _ (by rw [card_image_of_injOn hinj, Fintype.card_fin])
      obtain ⟨v, hv, hvi⟩ := mem_image.1 (hsurj ▸ mem_univ i)
      rw [hεdef, weight_colorWeight_apply, Finset.sum_eq_single_of_mem v
        (mem_filter.2 ⟨hv, hvi⟩) fun u hu hne =>
          absurd (hinj (mem_filter.1 hu).1 hv ((mem_filter.1 hu).2.trans hvi.symm)) hne]
      exact (monomial_le_degreeOf v hm).trans (hGdeg v)
    set g := colorComponent h ε G with hg
    have hsub : g.support ⊆ G.support := fun d hd => by
      rw [hg, colorComponent, support_weightedHomogeneousComponent] at hd
      exact Finset.mem_of_mem_filter d hd
    have hg0 : g ≠ 0 := fun h0 => mem_support_iff.1 hm (by
      have hc : g.coeff m = G.coeff m := by
        rw [hg, colorComponent, coeff_weightedHomogeneousComponent, ite_eq_left rfl]
      rw [← hc, h0]
      rfl)
    have hgsplit : ∀ I : Finset (Fin m.support.card),
        SplitRankLE (h ⁻¹' (I : Set (Fin m.support.card))) w g := fun I => by
      have hI := (hsplit (univ.filter fun v => h v ∈ I)).shift a₀
      have hset : ((univ.filter fun v => h v ∈ I : Finset (Fin n)) : Set (Fin n)) =
          h ⁻¹' (I : Set (Fin m.support.card)) := by
        ext v
        simp
      rw [hset] at hI
      exact splitRankLE_colorComponent h ε I hI
    obtain ⟨x, hx, hxg⟩ := exists_mem_colorHittingSet_eval_ne_zero F h hε hg0
      (weightedHomogeneousComponent_isWeightedHomogeneous ε G) hgsplit
      ((totalDegree_le_of_support_subset hsub).trans hGtot)
    obtain ⟨z, hz, y, hy, hzy⟩ := exists_eval_ne_zero_of_eval_colorComponent_ne_zero h ε
      (Λ := (range (δ * n + 1)).image Nat.cast)
      (by
        rw [card_image_of_injective _ Nat.cast_injective, card_range]
        exact Nat.lt_succ_of_le hGtot) hxg
    obtain ⟨z', hz', rfl⟩ := mem_image.1 hz
    rw [eval_shift] at hzy
    refine ⟨_, mem_union_right _ (mem_biUnion.2 ⟨m.support.card,
      mem_range.2 hmL, mem_image.2
        ⟨(a₀, ⟨h, x⟩, fun i => ⟨y i, Nat.lt_succ_of_le ((hy i).trans (hε i))⟩, z'),
          ?_, rfl⟩⟩), ?_⟩
    · simp only [mem_product, mem_sigma, mem_univ, true_and]
      exact ⟨ha₀, ⟨hh, hx⟩, hz'⟩
    · have hpt : (fun v => a₀ v + (z' : F) * ((y (h v) : ℕ) : F) * x v) =
          fun i => (z' : F) * (y (h i) : F) * x i + a₀ i := funext fun v => add_comm _ _
      rw [hpt]
      exact hzy

variable (F n w δ) in
/-- The size of the hitting set: with `L = ⌊lg w⌋`, the number of shifts times
`1 + ∑ r ≤ L, n 2 ^ (25 r) B(r) ^ δ (δ + 1) ^ r (δ n + 1)`, where
`B(r) = (r (n (2 ^ r w)² + 2 ^ r w) + 1) (δ n + 1) 2 ^ r`. For fixed `δ` this is polynomial in
`n` and `w`. -/
theorem card_boundedDegreeHittingSet_le :
    (boundedDegreeHittingSet F n w δ).card ≤
      (n * δ * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) *
        (n * δ * (δ + 1) ^ (Nat.log 2 w + 1) + 1) *
        (1 + ∑ r ∈ range (Nat.log 2 w + 1), n * 2 ^ (25 * r) *
          ((r * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (δ * n + 1) * 2 ^ r) ^ δ *
            ((δ + 1) ^ r * (δ * n + 1))) := by
  classical
  unfold boundedDegreeHittingSet
  set A := boundedDegreeShifts F δ (perfectHashFamily n (Nat.log 2 w + 1)) with hA
  have hAcard : A.card ≤ (n * δ * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) *
      (n * δ * (δ + 1) ^ (Nat.log 2 w + 1) + 1) :=
    (card_boundedDegreeShifts_le δ _).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (card_perfectHashFamily_le _ _)) _))
  refine ((card_union_le _ _).trans ?_).trans (Nat.mul_le_mul_right _ hAcard)
  rw [mul_add, mul_one, mul_sum]
  refine add_le_add_right (card_biUnion_le.trans (sum_le_sum fun r _ => card_image_le.trans ?_)) _
  simp only [card_product, card_sigma, card_univ, Fintype.card_fin, card_range, Fintype.card_pi,
    prod_const]
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_)
  calc ∑ h ∈ perfectHashFamily n r, (colorHittingSet F h w (δ * n) δ).card
      ≤ ∑ _h ∈ perfectHashFamily n r,
          ((r * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (δ * n + 1) * 2 ^ r) ^ δ :=
        sum_le_sum fun h _ => card_colorHittingSet_le F h w (δ * n) δ
    _ ≤ _ := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_perfectHashFamily_le n r)

/-- **Polynomial-size hitting sets for any-order ROABPs of bounded individual degree.** Over a
field of characteristic zero, `boundedDegreeHittingSet F n w δ` hits every polynomial in `n`
variables of individual degree at most `δ` computed by width-`w` read-once oblivious branching
programs in every variable order. -/
theorem isHittingSet_boundedDegreeHittingSet_roabp :
    IsHittingSet (boundedDegreeHittingSet F n w δ)
      {f | (∀ i, f.degreeOf i ≤ δ) ∧ IsAnyOrderROABP w f} :=
  fun f hf => isHittingSet_boundedDegreeHittingSet f ⟨hf.1, hf.2.splitRankLE⟩

end Cslib.Circuits.Arithmetic
