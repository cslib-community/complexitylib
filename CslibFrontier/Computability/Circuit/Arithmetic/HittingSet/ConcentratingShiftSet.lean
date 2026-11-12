/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShift
public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Basic
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.Nullstellensatz

/-!
# An explicit set of concentrating shifts

From a family `P` of colourings `Fin n → Fin k` of the variables, perfect for sets of `k`
variables, this file builds a point with coordinates in `F[s, t]` that is generic in the sense
of `exists_mem_support_shift_card_lt`, and from it a finite set of shifts in `Fⁿ`.

The `j`-th coordinate of the point is `∑ₑ Lₑ(s) t ^ 2 ^ hₑ(j)` (`genericShift`), where `hₑ` runs
over `P` and `Lₑ` is the Lagrange basis on the nodes `0, 1, …, |P| - 1`. For a set `Y` of `k`
variables choose `hₑ` injective on `Y` and set `s` to the `e`-th node: the coordinates become
`t ^ 2 ^ hₑ(j)`, and the products over the subsets of `Y` are distinct powers of `t`, by
uniqueness of binary expansions. So these products are linearly independent already before the
substitution (`genericShift_independent`).

A coefficient of `f (X + γ)` is then a polynomial in `s, t` of degree at most `n |P|` in `s` and
`n 2 ^ k` in `t`. If it is nonzero it is nonzero at a point of the grid
`{0, …, n |P|} × {0, …, n 2 ^ k}`, and the values of the generic point on this grid are the set
`concentratingShifts F P`.

The role of the seed variable `s` is that of the seed of the Klivans–Spielman generator in
[ForbesSaptharishiShpilka2014, Lemma 4.4]; the construction from a perfect hash family is ours.
Characteristic zero is used only to have the nodes `0, 1, …` distinct.

## Main definitions

* `genericShift`: the generic point over `F[s, t]`.
* `concentratingShifts`: its values on a grid.

## Main results

* `genericShift_independent`: the generic point of a perfect family is generic.
* `exists_mem_concentratingShifts`: some shift in the set gives a monomial with fewer than `k`
  variables.
* `card_concentratingShifts_le`: the set has at most `(n |P| + 1) (n 2 ^ k + 1)` points.
* `exists_mem_concentratingShifts_perfectHashFamily`,
  `card_concentratingShifts_perfectHashFamily_le`: the same with `Cslib.perfectHashFamily` and
  `k = ⌊lg w⌋ + 1`, a set of size polynomial in `n` and `w`.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Theorem 2.3 and Corollary 2.4 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] {n k : ℕ}

/-- The generic shift built from a family `P` of colourings `Fin n → Fin k`: its `j`-th coordinate
is `∑ₑ Lₑ(s) t ^ 2 ^ hₑ(j)` in `F[s, t]`, where `hₑ` runs over `P` and `Lₑ` is the Lagrange basis
on the nodes `0, 1, …`. Setting `s` to the `e`-th node leaves `t ^ 2 ^ hₑ(j)`. -/
noncomputable def genericShift (P : Finset (Fin n → Fin k)) (j : Fin n) :
    MvPolynomial (Fin 2) F :=
  ∑ e : Fin P.card,
    Polynomial.aeval (X 0 : MvPolynomial (Fin 2) F)
        (Lagrange.basis univ (fun e : Fin P.card => ((e : ℕ) : F)) e) *
      X 1 ^ 2 ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ)

variable {F}

private theorem node_injective (N : ℕ) : Function.Injective fun e : Fin N => ((e : ℕ) : F) :=
  Nat.cast_injective.comp Fin.val_injective

private theorem aeval_genericShift (P : Finset (Fin n → Fin k)) (e₀ : Fin P.card) (j : Fin n) :
    aeval ![Polynomial.C ((e₀ : ℕ) : F), Polynomial.X] (genericShift F P j) =
      Polynomial.X ^ 2 ^ ((P.equivFin.symm e₀ : Fin n → Fin k) j : ℕ) := by
  classical
  rw [genericShift, map_sum, Finset.sum_eq_single e₀]
  · rw [map_mul, map_pow, aeval_X, ← Polynomial.aeval_algHom_apply, aeval_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Polynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      Lagrange.eval_basis_self (node_injective _).injOn (mem_univ _), map_one, one_mul]
  · intro e _ he
    rw [map_mul, ← Polynomial.aeval_algHom_apply, aeval_X]
    simp only [Matrix.cons_val_zero]
    rw [← Polynomial.algebraMap_eq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      Lagrange.eval_basis_of_ne (v := fun e : Fin P.card => ((e : ℕ) : F)) he (mem_univ _),
      map_zero, zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- The generic shift of a perfect family of colourings satisfies the independence hypothesis of
`exists_mem_support_shift_card_lt`. -/
theorem genericShift_independent {P : Finset (Fin n → Fin k)}
    (hP : IsPerfectHashFamily P k)
    (Y : Finset (Fin n)) (hY : Y.card = k) (c : Finset (Fin n) → F)
    (hc : ∑ T ∈ Y.powerset, c T • ∏ j ∈ T, genericShift F P j = 0) :
    ∀ T ∈ Y.powerset, c T = 0 := by
  classical
  obtain ⟨h, hhP, hinj⟩ := hP Y hY
  set e₀ := P.equivFin ⟨h, hhP⟩ with he₀
  have hh : (P.equivFin.symm e₀ : Fin n → Fin k) = h := by rw [he₀, Equiv.symm_apply_apply]
  let d : Finset (Fin n) → ℕ := fun T => ∑ j ∈ T, 2 ^ (h j : ℕ)
  have hd : Set.InjOn d (Y.powerset : Set (Finset (Fin n))) := by
    intro S hS T hT hST
    have hS' := mem_powerset.1 (mem_coe.1 hS)
    have hT' := mem_powerset.1 (mem_coe.1 hT)
    have himg : S.image (fun j => (h j : ℕ)) = T.image fun j => (h j : ℕ) := by
      refine Finset.geomSum_injective le_rfl ?_
      have hi : ∀ U ⊆ Y, Set.InjOn (fun j => (h j : ℕ)) U := fun U hU a ha b hb hab =>
        hinj (hU ha) (hU hb) (Fin.val_injective hab)
      change ∑ i ∈ S.image _, 2 ^ i = ∑ i ∈ T.image _, 2 ^ i
      rw [Finset.sum_image (hi S hS'), Finset.sum_image (hi T hT')]
      exact hST
    have hsub : ∀ {A B : Finset (Fin n)}, A ⊆ Y → B ⊆ Y →
        A.image (fun j => (h j : ℕ)) = B.image (fun j => (h j : ℕ)) → A ⊆ B := by
      intro A B hA hB hAB j hj
      obtain ⟨j', hj', hjj'⟩ := mem_image.1 (hAB ▸ mem_image_of_mem (fun j => (h j : ℕ)) hj)
      rwa [← hinj (hB hj') (hA hj) (Fin.val_injective hjj')]
    exact (hsub hS' hT' himg).antisymm (hsub hT' hS' himg.symm)
  have hφ := congrArg (aeval ![Polynomial.C ((e₀ : ℕ) : F), Polynomial.X]) hc
  simp only [map_sum, map_smul, map_prod, aeval_genericShift, hh, map_zero,
    Finset.prod_pow_eq_pow_sum] at hφ
  intro T hT
  have hcoef := congrArg (fun q : Polynomial F => q.coeff (d T)) hφ
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, smul_eq_mul] at hcoef
  rw [Finset.sum_eq_single T] at hcoef
  · simpa [d] using hcoef
  · intro S hS hne
    rw [ite_eq_right fun h' : d T = d S => hne (hd (mem_coe.2 hS) (mem_coe.2 hT) h'.symm),
      mul_zero]
  · exact fun h' => absurd hT h'

omit [CharZero F] in
private theorem degreeOf_aeval_X_le (l i : Fin 2) (q : Polynomial F) :
    (Polynomial.aeval (X l : MvPolynomial (Fin 2) F) q).degreeOf i ≤
      if i = l then q.natDegree else 0 := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun c hc => ?_)
  rw [smul_eq_C_mul]
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_pow_le _ _ _).trans ?_)
  rw [degreeOf_X]
  split_ifs with h
  · rw [mul_one]; exact Nat.lt_succ_iff.1 (mem_range.1 hc)
  · rw [mul_zero]

private theorem degreeOf_genericShift_le (P : Finset (Fin n → Fin k)) (j : Fin n) :
    (genericShift F P j).degreeOf 0 ≤ P.card ∧ (genericShift F P j).degreeOf 1 ≤ 2 ^ k := by
  classical
  constructor
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e _ =>
      (degreeOf_mul_le _ _ _).trans ?_)
    have h1 := degreeOf_aeval_X_le (F := F) 0 0
      (Lagrange.basis univ (fun e : Fin P.card => ((e : ℕ) : F)) e)
    rw [ite_eq_left rfl, Lagrange.natDegree_basis (node_injective _).injOn (mem_univ _),
      card_univ, Fintype.card_fin] at h1
    have h2 := degreeOf_pow_le (0 : Fin 2) (X 1 : MvPolynomial (Fin 2) F)
      (2 ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ))
    rw [degreeOf_X_of_ne (R := F) (i := (0 : Fin 2)) (j := 1) (by decide), mul_zero] at h2
    omega
  · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e _ =>
      (degreeOf_mul_le _ _ _).trans ?_)
    have h1 := degreeOf_aeval_X_le (F := F) 0 1
      (Lagrange.basis univ (fun e : Fin P.card => ((e : ℕ) : F)) e)
    rw [ite_eq_right (by decide)] at h1
    have h2 := degreeOf_pow_le (1 : Fin 2) (X 1 : MvPolynomial (Fin 2) F)
      (2 ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ))
    rw [degreeOf_X, ite_eq_left rfl, mul_one] at h2
    have h3 : 2 ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Fin.is_lt _).le
    omega

variable (F) in
open scoped Classical in
/-- The values of the generic shift on a grid: an explicit set of shifts of size at most
`(n * P.card + 1) * (n * 2 ^ k + 1)`. -/
noncomputable def concentratingShifts (P : Finset (Fin n → Fin k)) : Finset (Fin n → F) :=
  (range (n * P.card + 1) ×ˢ range (n * 2 ^ k + 1)).image fun x j =>
    eval ![(x.1 : F), (x.2 : F)] (genericShift F P j)

omit [CharZero F] in
/-- The set of shifts has at most `(n * P.card + 1) * (n * 2 ^ k + 1)` points. -/
theorem card_concentratingShifts_le (P : Finset (Fin n → Fin k)) :
    (concentratingShifts F P).card ≤ (n * P.card + 1) * (n * 2 ^ k + 1) :=
  by
  classical
  exact card_image_le.trans_eq (by rw [card_product, card_range, card_range])

/-- **Support-concentrating shifts.** Let `P` be a perfect family of colourings of `n` variables
with `k` colours and `w < 2 ^ k`. Every nonzero multilinear polynomial in `n` variables of split
rank at most `w` across every set of `k` variables has, after shifting by some point of
`concentratingShifts F P`, a monomial with fewer than `k` variables. -/
theorem exists_mem_concentratingShifts {P : Finset (Fin n → Fin k)}
    (hP : IsPerfectHashFamily P k) {w : ℕ} (hw : w < 2 ^ k)
    {f : MvPolynomial (Fin n) F} (hf0 : f ≠ 0) (hmul : ∀ i, f.degreeOf i ≤ 1)
    (hf : ∀ Y : Finset (Fin n), Y.card = k → SplitRankLE (Y : Set (Fin n)) w f) :
    ∃ a ∈ concentratingShifts F P, ∃ m ∈ (shift a f).support, m.support.card < k := by
  classical
  obtain ⟨m, hm, hmk⟩ := exists_mem_support_shift_card_lt (R := MvPolynomial (Fin 2) F) hw
    (genericShift_independent hP) hf0 hmul hf
  set c := (shift (genericShift F P) f).coeff m with hc
  have hc0 : c ≠ 0 := mem_support_iff.1 hm
  let S : Fin 2 → Finset F :=
    ![(range (n * P.card + 1)).image Nat.cast, (range (n * 2 ^ k + 1)).image Nat.cast]
  have ht : f.totalDegree ≤ n :=
    (totalDegree_le_card_of_degreeOf_le_one hmul).trans_eq (Fintype.card_fin n)
  have hdeg : ∀ i, c.degreeOf i < (S i).card := by
    intro i
    fin_cases i
    · have h := degreeOf_coeff_shift_le (genericShift F P) f 0
        (fun j => (degreeOf_genericShift_le P j).1) m
      change _ < ((range (n * P.card + 1)).image Nat.cast).card
      rw [card_image_of_injective _ Nat.cast_injective, card_range]
      exact Nat.lt_succ_of_le (h.trans (Nat.mul_le_mul_right _ ht))
    · have h := degreeOf_coeff_shift_le (genericShift F P) f 1
        (fun j => (degreeOf_genericShift_le P j).2) m
      change _ < ((range (n * 2 ^ k + 1)).image Nat.cast).card
      rw [card_image_of_injective _ Nat.cast_injective, card_range]
      exact Nat.lt_succ_of_le (h.trans (Nat.mul_le_mul_right _ ht))
  obtain ⟨x, hx, hxc⟩ : ∃ x : Fin 2 → F, (∀ i, x i ∈ S i) ∧ eval x c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0 (eq_zero_of_eval_zero_at_prod_finset c S hdeg hcon)
  obtain ⟨a, ha, hxa⟩ := mem_image.1 (hx 0)
  obtain ⟨b, hb, hxb⟩ := mem_image.1 (hx 1)
  have hxe : x = ![(a : F), (b : F)] := by
    funext i
    fin_cases i
    · exact hxa.symm
    · exact hxb.symm
  refine ⟨fun j => eval x (genericShift F P j),
    mem_image.2 ⟨(a, b), mem_product.2 ⟨ha, hb⟩, hxe ▸ rfl⟩, m, mem_support_iff.2 ?_, hmk⟩
  have hmap := congrArg (fun q => q.coeff m)
    (map_shift (aeval x : MvPolynomial (Fin 2) F →ₐ[F] F) (genericShift F P) f)
  simp only [coeff_map, RingHom.coe_coe, aeval_eq_eval] at hmap
  rw [← hmap]
  exact hxc

/-- **Support-concentrating shifts, with the perfect hash family of the library.** Every nonzero
multilinear polynomial in `n` variables of split rank at most `w` across every set of
`⌊lg w⌋ + 1` variables has, after shifting by some point of an explicit set, a monomial with at
most `⌊lg w⌋` variables. -/
theorem exists_mem_concentratingShifts_perfectHashFamily {w : ℕ} {f : MvPolynomial (Fin n) F}
    (hf0 : f ≠ 0) (hmul : ∀ i, f.degreeOf i ≤ 1)
    (hf : ∀ Y : Finset (Fin n), Y.card = Nat.log 2 w + 1 → SplitRankLE (Y : Set (Fin n)) w f) :
    ∃ a ∈ concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1)),
      ∃ m ∈ (shift a f).support, m.support.card ≤ Nat.log 2 w := by
  obtain ⟨a, ha, m, hm, hmk⟩ := exists_mem_concentratingShifts
    (isPerfectHashFamily_perfectHashFamily n _ (Nat.succ_pos _))
    (Nat.lt_pow_succ_log_self (by norm_num) w) hf0 hmul hf
  exact ⟨a, ha, m, hm, Nat.lt_succ_iff.1 hmk⟩

omit [CharZero F] in
/-- The explicit set of shifts for width `w` has at most
`(n² 2 ^ (25 (⌊lg w⌋ + 1)) + 1) (n 2 ^ (⌊lg w⌋ + 1) + 1)` points, which is polynomial in `n`
and `w`. -/
theorem card_concentratingShifts_perfectHashFamily_le (n w : ℕ) :
    (concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1))).card ≤
      (n * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) * (n * 2 ^ (Nat.log 2 w + 1) + 1) :=
  (card_concentratingShifts_le _).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (card_perfectHashFamily_le _ _)) _))

end Cslib.Circuits.Arithmetic
