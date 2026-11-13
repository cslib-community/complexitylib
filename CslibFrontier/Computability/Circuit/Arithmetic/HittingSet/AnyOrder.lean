/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShiftSet
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SetPartitioned
public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP

/-!
# Hitting sets for multilinear any-order ROABPs

Over a field of characteristic zero there is an explicit set of points, of size polynomial in
`n` and `w`, on which no nonzero multilinear polynomial in `n` variables computed by read-once
oblivious algebraic branching programs of width `w` in every variable order vanishes
(`isHittingSet_anyOrderHittingSet_roabp`). This is Theorem 1.1 of Shpilka [Shpilka2026] in
characteristic zero. The source also covers positive characteristic, by a hitting set that is
not in the library. Its Theorem 1.2, for set-multilinear depth-three circuits, is
`isHittingSet_setMultilinearHittingSet_sum_prod`.

The class that is actually hit is larger and has no branching program in it
(`isHittingSet_anyOrderHittingSet`): the multilinear polynomials of split rank at most `w`
across every split of the variables (`MvPolynomial.SplitRankLE`). A polynomial computed by
width-`w` programs in every order is in this class (`IsAnyOrderROABP.splitRankLE`), which is the
easy direction of Nisan's characterisation. The class is closed under limits of coefficients, so
it also contains the border of the branching-program class; no notion of border is defined.

## Proof

Let `f` be nonzero in the class. Some shift `a` from `concentratingShifts` gives `f (X + a)` a
monomial with at most `⌊lg w⌋` variables (`exists_mem_concentratingShifts_perfectHashFamily`).
The passage from such a shift to a point where `f` is nonzero is
`exists_mem_setPartitionedHittingSet_eval_ne_zero` ([Shpilka2026], Lemma 3.4), applied with
every variable a block of its own; the set of all these points is `anyOrderHittingSet F n w`
([Shpilka2026], eq. (7)).

## Main definitions

* `anyOrderHittingSet`: the hitting set.

## Main results

* `isHittingSet_anyOrderHittingSet`: the hitting set for multilinear polynomials of split rank
  at most `w` across every split.
* `card_anyOrderHittingSet_le`: its size, a polynomial in `n` and `w`.
* `IsAnyOrderROABP.splitRankLE`: any-order programs of width `w` have split rank at most `w`.
* `isHittingSet_anyOrderHittingSet_roabp`: the hitting set for multilinear any-order ROABPs.

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Theorem 1.1 and §3 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] (n w : ℕ)

/-- The hitting set for multilinear polynomials in `n` variables of split rank at most `w`
across every split: the points of `setPartitionedHittingSet`, with every variable a block of
its own, built from the concentrating shifts for the perfect hash family with `⌊lg w⌋ + 1`
colours. -/
noncomputable def anyOrderHittingSet : Finset (Fin n → F) :=
  setPartitionedHittingSet F id
    (concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1))) (Nat.log 2 w) w

variable {F n w}

/-- **Hitting set for multilinear polynomials of small split rank.** Over a field of
characteristic zero, `anyOrderHittingSet F n w` hits every multilinear polynomial in `n`
variables that is a sum of `w` products across every split of its variables. -/
theorem isHittingSet_anyOrderHittingSet :
    IsHittingSet (anyOrderHittingSet F n w)
      {f | (∀ i, f.degreeOf i ≤ 1) ∧
        ∀ U : Finset (Fin n), SplitRankLE (U : Set (Fin n)) w f} := by
  rintro f ⟨hmul, hsplit⟩ hf0
  obtain ⟨a, ha, m, hm, hmL⟩ :=
    exists_mem_concentratingShifts_perfectHashFamily hf0 hmul fun Y _ => hsplit Y
  exact exists_mem_setPartitionedHittingSet_eval_ne_zero (isSetPartitioned_id_iff.2 hmul)
    hsplit ha hm hmL

variable (F n w) in
/-- The hitting set has size polynomial in `n` and `w`: with `L = ⌊lg w⌋`, at most
`(n² 2 ^ (25 (L + 1)) + 1) (n 2 ^ (L + 1) + 1)` shifts, each with at most
`1 + ∑ r ≤ L, n 2 ^ (25 r) 2 ^ r (n (n (2 ^ r w)² + 2 ^ r w) + 1) (n + 1)` points. -/
theorem card_anyOrderHittingSet_le :
    (anyOrderHittingSet F n w).card ≤
      (n * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) * (n * 2 ^ (Nat.log 2 w + 1) + 1) *
        (1 + ∑ r ∈ range (Nat.log 2 w + 1), n * 2 ^ (25 * r) *
          (2 ^ r * ((n * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (n + 1)))) := by
  refine (card_setPartitionedHittingSet_le _ _ _ _).trans ?_
  rw [Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (card_concentratingShifts_perfectHashFamily_le n w)

/-! ### Read-once oblivious branching programs -/

section ROABP

variable {F : Type*} [Field F] {n w : ℕ}

/-- Nisan's observation: a polynomial computed by width-`w` read-once oblivious branching
programs in every order has split rank at most `w` across every split of the variables. -/
theorem IsAnyOrderROABP.splitRankLE {f : MvPolynomial (Fin n) F} (hf : IsAnyOrderROABP w f)
    (U : Finset (Fin n)) : SplitRankLE (U : Set (Fin n)) w f := by
  classical
  obtain ⟨M, s, t, rfl⟩ := hf (U.toList ++ Uᶜ.toList)
    (List.Nodup.append U.nodup_toList Uᶜ.nodup_toList fun i hi hi' =>
      (mem_compl.1 (mem_toList.1 hi')) (mem_toList.1 hi))
    (fun i => List.mem_append.2 ((em (i ∈ U)).imp mem_toList.2 fun h =>
      mem_toList.2 (mem_compl.2 h)))
  refine ⟨fun k => roabpProd M U.toList s k, fun k => roabpProd M Uᶜ.toList k t,
    fun k => roabpProd_mem_supported M _ (fun i hi => mem_coe.2 (mem_toList.1 hi)) _ _,
    fun k => roabpProd_mem_supported M _
      (fun i hi => fun h => mem_compl.1 (mem_toList.1 hi) (mem_coe.1 h)) _ _, ?_⟩
  rw [roabpProd, List.map_append, List.prod_append, Matrix.mul_apply]
  rfl

/-- **Polynomial-size hitting sets for multilinear any-order ROABPs** ([Shpilka2026],
Theorem 1.1, in characteristic zero). `anyOrderHittingSet F n w` hits every multilinear
polynomial in `n` variables computed by width-`w` read-once oblivious branching programs in
every variable order. -/
theorem isHittingSet_anyOrderHittingSet_roabp [CharZero F] :
    IsHittingSet (anyOrderHittingSet F n w)
      {f | (∀ i, f.degreeOf i ≤ 1) ∧ IsAnyOrderROABP w f} :=
  fun f hf => isHittingSet_anyOrderHittingSet f ⟨hf.1, hf.2.splitRankLE⟩

end ROABP

end Cslib.Circuits.Arithmetic
