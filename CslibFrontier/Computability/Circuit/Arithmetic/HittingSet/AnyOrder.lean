/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShiftSet
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartDerivative
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPartEval

/-!
# Hitting sets for multilinear any-order ROABPs

Over a field of characteristic zero there is an explicit set of points, of size polynomial in
`n` and `w`, on which no nonzero multilinear polynomial in `n` variables computed by read-once
oblivious algebraic branching programs of width `w` in every variable order vanishes
(`isHittingSet_anyOrderHittingSet_roabp`). This is Theorem 1.1 of Shpilka [Shpilka2026] in
characteristic zero. The source also covers positive characteristic, by a hitting set that is
not in the library, and set-multilinear depth-three circuits (its Theorem 1.2); neither is
formalized here.

The class that is actually hit is larger and has no branching program in it
(`isHittingSet_anyOrderHittingSet`): the multilinear polynomials of split rank at most `w`
across every split of the variables (`MvPolynomial.SplitRankLE`). A polynomial computed by
width-`w` programs in every order is in this class (`IsAnyOrderROABP.splitRankLE`), which is the
easy direction of Nisan's characterisation. The class is closed under limits of coefficients, so
it also contains the border of the branching-program class; no notion of border is defined.

## Proof

Let `f` be nonzero in the class.

1. Some shift `a` from `concentratingShifts` gives `G = f (X + a)` a monomial `m` with
   `r ≤ ⌊lg w⌋` variables (`exists_mem_concentratingShifts_perfectHashFamily`). If `r = 0` then
   `f a ≠ 0`.
2. Some colouring `h` of the variables with `r` colours, from `Cslib.perfectHashFamily`, is
   injective on the variables of `m`. The colour part `g = colorPart h G`, the sum of the
   monomials of `G` with exactly one variable of each colour, contains `m`
   (`colorPart_ne_zero`, the source's Lemma 3.1).
3. `g` lies in a space of dimension at most `2 ^ r * w` closed under partial derivatives
   (`exists_pderiv_closed_colorPart`, Lemma 3.3), so it is nonzero at a point `b` of
   `logHittingSet` (`isHittingSet_logHittingSet`).
4. `g b` is a combination of values of `G` at the points `t • b` restricted to the variables
   with colours outside a set `J`, over `t` in any set of more than `n` scalars
   (`exists_eval_ne_zero_of_eval_colorPart_ne_zero`, Lemma 3.2). So `f` is nonzero at
   `a + t • b` restricted in this way.

The set of all these points is `anyOrderHittingSet F n w` ([Shpilka2026], eq. (7) and
Lemma 3.4, with singleton blocks).

## Main definitions

* `anyOrderHittingSet`: the hitting set.
* `roabpProd`, `IsAnyOrderROABP`: read-once oblivious branching programs, in every order.

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

open scoped Classical in
/-- The hitting set for multilinear polynomials in `n` variables of split rank at most `w`
across every split: the concentrating shifts `a`, together with the points
`a + t • b` restricted to the variables whose colour is outside `J`, for a colouring `h` with
`r ≤ ⌊lg w⌋` colours from the perfect hash family, a set `J` of colours, a point `b` of the
hitting set for partial-derivative spaces of dimension `2 ^ r * w` and `t = 0, …, n`. -/
noncomputable def anyOrderHittingSet : Finset (Fin n → F) :=
  concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1)) ∪
    (range (Nat.log 2 w + 1)).biUnion fun r =>
      (concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1)) ×ˢ perfectHashFamily n r ×ˢ
        (univ : Finset (Finset (Fin r))) ×ˢ logHittingSet F n (2 ^ r * w) n ×ˢ range (n + 1)).image
        fun ⟨a, h, J, b, t⟩ v => a v + if h v ∈ J then 0 else (t : F) * b v

variable {F n w}

omit [CharZero F] in
private theorem support_colorPart_subset {σ : Type*} {r : ℕ} (c : σ → Fin r)
    (G : MvPolynomial σ F) : (colorPart c G).support ⊆ G.support := fun d hd => by
  classical
  rw [colorPart, support_weightedHomogeneousComponent] at hd
  exact Finset.mem_of_mem_filter d hd

/-- **Hitting set for multilinear polynomials of small split rank.** Over a field of
characteristic zero, `anyOrderHittingSet F n w` hits every multilinear polynomial in `n`
variables that is a sum of `w` products across every split of its variables. -/
theorem isHittingSet_anyOrderHittingSet :
    IsHittingSet (anyOrderHittingSet F n w)
      {f | (∀ i, f.degreeOf i ≤ 1) ∧
        ∀ U : Finset (Fin n), SplitRankLE (U : Set (Fin n)) w f} := by
  classical
  rintro f ⟨hmul, hsplit⟩ hf0
  obtain ⟨a, ha, m, hm, hmL⟩ :=
    exists_mem_concentratingShifts_perfectHashFamily hf0 hmul fun Y _ => hsplit Y
  set G := shift a f with hG
  have hGmul : ∀ i, G.degreeOf i ≤ 1 := fun i => (degreeOf_shift_le a f i).trans (hmul i)
  have hGdeg : G.totalDegree ≤ n :=
    (totalDegree_le_card_of_degreeOf_le_one hGmul).trans_eq (Fintype.card_fin n)
  rcases Nat.eq_zero_or_pos m.support.card with h0 | hpos
  · refine ⟨a, mem_union_left _ ha, ?_⟩
    have hm0 : m = 0 := Finsupp.support_eq_empty.1 (card_eq_zero.1 h0)
    have h := eval_shift a 0 f
    rw [eval_zero, constantCoeff_eq] at h
    simp only [Pi.zero_apply, zero_add] at h
    rw [← h]
    exact hm0 ▸ mem_support_iff.1 hm
  · obtain ⟨h, hh, hinj⟩ := isPerfectHashFamily_perfectHashFamily n _ hpos m.support rfl
    have hg0 : colorPart h G ≠ 0 := colorPart_ne_zero h hm
      (fun v => (monomial_le_degreeOf v hm).trans (hGmul v)) hinj rfl
    obtain ⟨V, hV, hfin, hrank, hgV⟩ := exists_pderiv_closed_colorPart h (w := w) (G := G)
      fun I => by
        have hI := (hsplit (univ.filter fun v => h v ∈ I)).shift a
        have hset : ((univ.filter fun v => h v ∈ I : Finset (Fin n)) : Set (Fin n)) =
            h ⁻¹' (I : Set (Fin m.support.card)) := by
          ext v
          simp
        rwa [hset] at hI
    have hgdeg : (colorPart h G).totalDegree ≤ n :=
      (totalDegree_le_of_support_subset (support_colorPart_subset h G)).trans hGdeg
    obtain ⟨b, hb, hbg⟩ := isHittingSet_logHittingSet (2 ^ m.support.card * w) n
      (colorPart h G) ⟨hgdeg, V, hV, hfin, hrank, hgV⟩ hg0
    obtain ⟨t, ht, J, hJ⟩ := exists_eval_ne_zero_of_eval_colorPart_ne_zero h
      (Λ := (range (n + 1)).image Nat.cast)
      (by
        rw [card_image_of_injective _ Nat.cast_injective, card_range]
        exact Nat.lt_succ_of_le hGdeg) hbg
    obtain ⟨t', ht', rfl⟩ := mem_image.1 ht
    rw [eval_shift] at hJ
    refine ⟨fun v => a v + if h v ∈ J then 0 else (t' : F) * b v, mem_union_right _
      (mem_biUnion.2 ⟨m.support.card, mem_range.2 (Nat.lt_succ_of_le hmL), mem_image.2
        ⟨(a, h, J, b, t'), ?_, rfl⟩⟩), ?_⟩
    · simp only [mem_product, mem_univ, true_and]
      exact ⟨ha, hh, hb, ht'⟩
    · have hpt : (fun v => a v + if h v ∈ J then 0 else (t' : F) * b v) =
          fun i => (if h i ∈ J then 0 else (t' : F) * b i) + a i := funext fun v => add_comm _ _
      rw [hpt]
      exact hJ

variable (F n w) in
/-- The hitting set has size polynomial in `n` and `w`: with `L = ⌊lg w⌋`, at most
`(n² 2 ^ (25 (L + 1)) + 1) (n 2 ^ (L + 1) + 1)` shifts, each with at most
`1 + ∑ r ≤ L, n 2 ^ (25 r) 2 ^ r (n (n (2 ^ r w)² + 2 ^ r w) + 1) (n + 1)` points. -/
theorem card_anyOrderHittingSet_le :
    (anyOrderHittingSet F n w).card ≤
      (n * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) * (n * 2 ^ (Nat.log 2 w + 1) + 1) *
        (1 + ∑ r ∈ range (Nat.log 2 w + 1), n * 2 ^ (25 * r) *
          (2 ^ r * ((n * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (n + 1)))) := by
  classical
  unfold anyOrderHittingSet
  set A := concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1)) with hA
  calc _ ≤ A.card + ∑ r ∈ range (Nat.log 2 w + 1), A.card * (n * 2 ^ (25 * r) *
          (2 ^ r * ((n * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (n + 1)))) := by
        refine (card_union_le _ _).trans (add_le_add_right (card_biUnion_le.trans
          (sum_le_sum fun r _ => card_image_le.trans ?_)) _)
        simp only [card_product, card_univ, Fintype.card_finset, Fintype.card_fin, card_range]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (card_perfectHashFamily_le n r)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (card_logHittingSet_le _ _))))
    _ = A.card * (1 + ∑ r ∈ range (Nat.log 2 w + 1), n * 2 ^ (25 * r) *
          (2 ^ r * ((n * (n * (2 ^ r * w) ^ 2 + 2 ^ r * w) + 1) * (n + 1)))) := by
        rw [mul_add, mul_one, mul_sum]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_concentratingShifts_perfectHashFamily_le n w)

/-! ### Read-once oblivious branching programs -/

section ROABP

variable {F : Type*} [Field F] {n w : ℕ}

open Polynomial in
/-- The matrix computed by a read-once oblivious branching program of width `w` that reads the
variables in the order of the list `l`: the product of the matrices `M i`, with entries
univariate polynomials evaluated at the variable `X i`. -/
@[expose] noncomputable def roabpProd (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (l : List (Fin n)) :
    Matrix (Fin w) (Fin w) (MvPolynomial (Fin n) F) :=
  (l.map fun i => (M i).map (Polynomial.aeval (X i : MvPolynomial (Fin n) F))).prod

open Polynomial in
/-- `f` is computed by a read-once oblivious branching program of width `w` in every order of
the variables: for every list of all the variables without repetition, `f` is an entry of the
product of some `w × w` matrices of univariate polynomials read in that order. The matrices may
depend on the order. -/
@[expose] def IsAnyOrderROABP (w : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∀ l : List (Fin n), l.Nodup → (∀ i, i ∈ l) →
    ∃ (M : Fin n → Matrix (Fin w) (Fin w) F[X]) (s t : Fin w), f = roabpProd M l s t

open Polynomial in
private theorem roabpProd_mem_supported (M : Fin n → Matrix (Fin w) (Fin w) F[X])
    {S : Set (Fin n)} : ∀ l : List (Fin n), (∀ i ∈ l, i ∈ S) → ∀ s t : Fin w,
      roabpProd M l s t ∈ supported F S
  | [], _, s, t => by
    rw [roabpProd, List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | i :: l, hl, s, t => by
    rw [roabpProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    refine sum_mem fun k _ => mul_mem ?_
      (roabpProd_mem_supported M l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) k t)
    have hX : (X i : MvPolynomial (Fin n) F) ∈ supported F S :=
      Algebra.subset_adjoin ⟨i, hl i List.mem_cons_self, rfl⟩
    rw [Matrix.map_apply, ← Subtype.coe_mk (X i) hX, ← Polynomial.aeval_subalgebra_coe]
    exact Subtype.coe_prop _

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
