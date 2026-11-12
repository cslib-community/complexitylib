/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Concentrating
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingMonomial
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingReduction
public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Defs
public import Mathlib.LinearAlgebra.Lagrange
import CslibFrontier.Foundations.Data.Nat.Radix.Unique
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# An explicit set of concentrating shifts for any individual degree

From a family `P` of colourings `Fin n → Fin k` of the variables, perfect for sets of `k`
variables, and a degree bound `δ`, this file builds a concentrating point with coordinates in
`F[τ][s]` (`IsConcentrating`), and from it a finite set of shifts in `Fⁿ`.

The `j`-th coordinate of the point is `∑ₑ Lₑ(s) τ ^ (δ + 1) ^ hₑ(j)` (`seedPoint`), where `hₑ`
runs over `P` and `Lₑ` is the Lagrange basis on the nodes `0, 1, …, |P| - 1`. For a set `Y` of
`k` variables choose `hₑ` injective on `Y` and let `c` be the `e`-th node. At `s = c` the
coordinates are `τ ^ (δ + 1) ^ hₑ(j)`, and the exponents `(δ + 1) ^ hₑ(j)`, `j ∈ Y`, separate the
monomials in `Y` of individual degree at most `δ`, by uniqueness of expansions in base `δ + 1`.
A combination `∑ᵢ ρᵢ pᵢ(X + γ)` that violates the definition of a concentrating point gives,
after dividing `∑ᵢ ρᵢ pᵢ` by the largest power of `s - c` that divides it and setting `s = c`, a
violating combination for the point `τ ^ (δ + 1) ^ hₑ(j)`, with the coefficients of the expansions
of the `ρᵢ` around `c` (`Polynomial.taylor`) as its scalars. There is none
(`eq_zero_of_scale_X_pow_vanishing`).

A coefficient of `f (X + γ)` is then a polynomial of degree at most `n δ |P|` in `s` and
`n δ (δ + 1) ^ k` in `τ`. If it is nonzero it is nonzero at a point of the grid
`{0, …, n δ |P|} × {0, …, n δ (δ + 1) ^ k}`, and the values of the point on this grid are the set
`boundedDegreeShifts F δ P`.

The seed variable `s` plays the role of the seed of the Klivans–Spielman generator in
[ForbesSaptharishiShpilka2014, Lemma 4.4]. The construction and the proof are not taken from a
source; the result is the statement of [Shpilka2026, Corollary 2.4] with a different set of
shifts.
Characteristic zero is used to have the nodes `0, 1, …` distinct.

## Main definitions

* `seedPoint`: the point over `F[τ][s]`.
* `boundedDegreeShifts`: its values on a grid.

## Main results

* `isConcentrating_seedPoint`: the point of a perfect family is concentrating.
* `exists_mem_boundedDegreeShifts`: some shift in the set gives a monomial with fewer than `k`
  variables.
* `card_boundedDegreeShifts_le`: the set has at most
  `(n δ |P| + 1) (n δ (δ + 1) ^ k + 1)` points.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Corollary 2.4 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial
open scoped Polynomial


section Specialization

variable {σ F A : Type*} [Field F] [CommRing A]

/-- If every monomial of the shift `H (X + γ)` contains the variable `j`, then the scaled
polynomial `H (γ ⊙ X)` vanishes at `X j = 1`. -/
private theorem aeval_update_aeval_C_mul_X_eq_zero [DecidableEq σ] {γ : σ → A}
    {H : MvPolynomial σ A} {j : σ} (hj : ∀ m ∈ (shift γ H).support, m j ≠ 0) :
    aeval (Function.update (X : σ → MvPolynomial σ A) j 1)
      (aeval (fun v => C (γ v) * X v) H) = 0 := by
  set g : σ → MvPolynomial σ A := fun v => if v = j then 0 else C (γ v) * X v - C (γ v) with hg
  have h0 : aeval g (shift γ H) = 0 := by
    rw [aeval_def, eval₂_eq]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (hj m hm))
      (by simp [hg, hj m hm]), mul_zero]
  rw [← h0, shift, ← AlgHom.comp_apply, ← AlgHom.comp_apply, comp_aeval, comp_aeval]
  congr 2
  funext v
  by_cases hv : v = j
  · subst hv
    simp [hg]
  · simp [hg, hv]

/-- The coefficient extraction behind the lowest-order part: a quotient by `(X - c) ^ i` of a
combination of constants takes at `c` the value of the combination of the `i`-th coefficients of
the expansions around `c`. -/
private theorem eval_eq_sum_taylor_coeff {w i : ℕ} {c : A} {q : A[X]} {ρ : Fin w → A[X]}
    {a : Fin w → A} (h : (Polynomial.X - Polynomial.C c) ^ i * q = ∑ l, ρ l * Polynomial.C (a l)) :
    q.eval c = ∑ l, (Polynomial.taylor c (ρ l)).coeff i * a l := by
  have h' := congrArg (fun r => (Polynomial.taylor c r).coeff i) h
  simp only [Polynomial.taylor_mul, Polynomial.taylor_pow, map_sub, Polynomial.taylor_X,
    Polynomial.taylor_C, add_sub_cancel_right, map_sum, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C] at h'
  rw [← h', ← Polynomial.taylor_coeff_zero, ← Polynomial.coeff_X_pow_mul _ i 0, zero_add]

variable [Algebra F A]

/-- **The lowest-order part at a point.** A nonzero combination `H = ∑ ρ l • p l` over `A[s]` of
polynomials over `F` is `(s - c) ^ i` times a polynomial whose value `H'(c)` at `s = c` is
nonzero, and `H'(c)` is the combination of the `p l` with the `i`-th coefficients of the
expansions of the `ρ l` around `c`. -/
private theorem exists_eq_C_pow_mul {w : ℕ} (c : A) (p : Fin w → MvPolynomial σ F)
    (ρ : Fin w → A[X]) (hH : ∑ l, C (ρ l) * map (algebraMap F A[X]) (p l) ≠ 0) :
    ∃ (i : ℕ) (H' : MvPolynomial σ A[X]),
      ∑ l, C (ρ l) * map (algebraMap F A[X]) (p l) = C ((Polynomial.X - Polynomial.C c) ^ i) * H' ∧
      map (Polynomial.evalRingHom c) H' ≠ 0 ∧
      map (Polynomial.evalRingHom c) H' =
        ∑ l, C ((Polynomial.taylor c (ρ l)).coeff i) * map (algebraMap F A) (p l) := by
  classical
  set H := ∑ l, C (ρ l) * map (algebraMap F A[X]) (p l) with hHdef
  obtain ⟨m₀, hm₀, hmin⟩ := Finset.exists_min_image H.support
    (fun m => (H.coeff m).rootMultiplicity c) (support_nonempty.2 hH)
  set i := (H.coeff m₀).rootMultiplicity c with hi
  obtain ⟨H', hH'⟩ : C ((Polynomial.X - Polynomial.C c) ^ i) ∣ H := by
    refine (C_dvd_iff_dvd_coeff _ _).2 fun m => ?_
    by_cases hm : m ∈ H.support
    · exact (Polynomial.le_rootMultiplicity_iff (mem_support_iff.1 hm)).1 (hmin m hm)
    · rw [notMem_support_iff.1 hm]
      exact dvd_zero _
  have hcoeff : ∀ m, H.coeff m = (Polynomial.X - Polynomial.C c) ^ i * H'.coeff m := fun m => by
    rw [hH', coeff_C_mul]
  refine ⟨i, H', hH', fun h0 => ?_, ?_⟩
  · have hroot : Polynomial.X - Polynomial.C c ∣ H'.coeff m₀ := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom,
        ← coeff_map, h0]
      rfl
    have hdvd : (Polynomial.X - Polynomial.C c) ^ (i + 1) ∣ H.coeff m₀ := by
      rw [hcoeff, pow_succ]
      exact mul_dvd_mul_left _ hroot
    exact absurd ((Polynomial.le_rootMultiplicity_iff (mem_support_iff.1 hm₀)).2 hdvd)
      (Nat.not_succ_le_self _)
  · ext m
    have h := hcoeff m
    rw [hHdef, coeff_sum] at h
    simp only [coeff_C_mul, coeff_map, Polynomial.algebraMap_apply] at h
    simp only [coeff_map, coeff_sum, coeff_C_mul, Polynomial.coe_evalRingHom]
    exact eval_eq_sum_taylor_coeff h.symm

end Specialization

variable (F : Type*) [Field F] [CharZero F] {n k : ℕ}

/-- The point built from a family `P` of colourings `Fin n → Fin k` and a degree bound `δ`: its
`j`-th coordinate is `∑ₑ Lₑ(s) τ ^ (δ + 1) ^ hₑ(j)` in `F[τ][s]`, where `hₑ` runs over `P` and
`Lₑ` is the Lagrange basis on the nodes `0, 1, …`. Setting the seed `s` to the `e`-th node leaves
`τ ^ (δ + 1) ^ hₑ(j)`. -/
noncomputable def seedPoint (δ : ℕ) (P : Finset (Fin n → Fin k)) (j : Fin n) : F[X][X] :=
  ∑ e : Fin P.card,
    (Lagrange.basis univ (fun e : Fin P.card => ((e : ℕ) : F)) e).map Polynomial.C *
      Polynomial.C (Polynomial.X ^ (δ + 1) ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ))

variable {F}

omit [CharZero F] in
private theorem eval_C_seedPoint (δ : ℕ) (P : Finset (Fin n → Fin k)) (c : F) (j : Fin n) :
    (seedPoint F δ P j).eval (Polynomial.C c) = ∑ e : Fin P.card,
      Polynomial.C ((Lagrange.basis univ (fun e : Fin P.card => ((e : ℕ) : F)) e).eval c) *
        Polynomial.X ^ (δ + 1) ^ ((P.equivFin.symm e : Fin n → Fin k) j : ℕ) := by
  simp only [seedPoint, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, Polynomial.eval_C]

private theorem eval_node_seedPoint (δ : ℕ) (P : Finset (Fin n → Fin k)) (e₀ : Fin P.card)
    (j : Fin n) : (seedPoint F δ P j).eval (Polynomial.C ((e₀ : ℕ) : F)) =
      Polynomial.X ^ (δ + 1) ^ ((P.equivFin.symm e₀ : Fin n → Fin k) j : ℕ) := by
  classical
  rw [eval_C_seedPoint, Finset.sum_eq_single e₀]
  · have hinj : Function.Injective fun e : Fin P.card => ((e : ℕ) : F) :=
      Nat.cast_injective.comp Fin.val_injective
    rw [Lagrange.eval_basis_self hinj.injOn (mem_univ _), map_one, one_mul]
  · intro e _ he
    rw [Lagrange.eval_basis_of_ne (v := fun e : Fin P.card => ((e : ℕ) : F)) he (mem_univ _),
      map_zero, zero_mul]
  · exact fun h => absurd (mem_univ _) h

private theorem natDegree_seedPoint_le (δ : ℕ) (P : Finset (Fin n → Fin k)) (j : Fin n) :
    (seedPoint F δ P j).natDegree ≤ P.card := by
  classical
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun e _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, add_zero]
  refine Polynomial.natDegree_map_le.trans ?_
  have hinj : Function.Injective fun e : Fin P.card => ((e : ℕ) : F) :=
    Nat.cast_injective.comp Fin.val_injective
  rw [Lagrange.natDegree_basis hinj.injOn (mem_univ _), card_univ, Fintype.card_fin]
  exact Nat.sub_le _ _

omit [CharZero F] in
private theorem natDegree_eval_C_seedPoint_le (δ : ℕ) (P : Finset (Fin n → Fin k)) (c : F)
    (j : Fin n) : ((seedPoint F δ P j).eval (Polynomial.C c)).natDegree ≤ (δ + 1) ^ k := by
  rw [eval_C_seedPoint]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Fin.is_lt _).le)

/-- **The seed point is concentrating.** For a perfect family `P` of colourings with `k` colours
and `w < 2 ^ k`, no nonzero combination of `w` shifts by `seedPoint F δ P` of polynomials in a set
`Y` of `k` variables, of individual degree at most `δ`, has all its monomials divisible by every
variable of `Y`. -/
theorem isConcentrating_seedPoint {P : Finset (Fin n → Fin k)} (hP : IsPerfectHashFamily P k)
    {w : ℕ} (hw : w < 2 ^ k) (δ : ℕ) : IsConcentrating F (seedPoint F δ P) k w δ := by
  classical
  intro Y hY p hp ρ hS hdeg
  by_contra hcon
  push Not at hcon
  obtain ⟨h, hhP, hinj⟩ := hP Y hY
  set e₀ := P.equivFin ⟨h, hhP⟩ with he₀
  have hh : (P.equivFin.symm e₀ : Fin n → Fin k) = h := by rw [he₀, Equiv.symm_apply_apply]
  set γ := seedPoint F δ P with hγ
  set H : MvPolynomial (Fin n) F[X][X] := ∑ i, C (ρ i) * map (algebraMap F F[X][X]) (p i)
    with hHdef
  -- the combination is the shift of `H` over `F[τ][s]`
  have hSH : ∑ i, C (ρ i) * shift γ (p i) = shift γ H := by
    simp only [hHdef, shift, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rfl
  rw [hSH] at hS hdeg hcon
  have hH0 : H ≠ 0 := fun h0 => hS (by rw [h0, map_zero])
  have hHdeg : ∀ j, H.degreeOf j ≤ δ := fun j => by
    rw [← shift_neg_shift γ H]
    exact (degreeOf_shift_le _ _ j).trans (hdeg j)
  obtain ⟨i₀, H', hHH', hne, hform⟩ :=
    exists_eq_C_pow_mul (Polynomial.C ((e₀ : ℕ) : F)) p ρ hH0
  rw [← hHdef] at hHH'
  have hC : (C ((Polynomial.X - Polynomial.C (Polynomial.C ((e₀ : ℕ) : F))) ^ i₀) :
      MvPolynomial (Fin n) F[X][X]) ≠ 0 :=
    (C_ne_zero).2 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
  refine hne ?_
  rw [hform]
  refine eq_zero_of_scale_X_pow_vanishing (δ := δ) (E := fun v => (δ + 1) ^ (h v : ℕ)) hY hw
    ?_ hp _ ?_ ?_
  · -- the weights separate the monomials in `Y` of individual degree at most `δ`
    rintro b ⟨hbY, hbδ⟩ b' ⟨hbY', hbδ'⟩ hbb'
    have hinj' : Set.InjOn (fun v => (h v : ℕ)) Y := fun a ha a' ha' haa' =>
      hinj ha ha' (Fin.val_injective haa')
    have hYeq := Nat.eq_of_sum_mul_pow_eq hinj' (fun j _ => Nat.lt_succ_of_le (hbδ j))
      (fun j _ => Nat.lt_succ_of_le (hbδ' j)) hbb'
    ext j
    by_cases hj : j ∈ Y
    · exact hYeq j hj
    · rw [Finsupp.notMem_support_iff.1 fun hjb => hj (hbY hjb),
        Finsupp.notMem_support_iff.1 fun hjb => hj (hbY' hjb)]
  · -- the individual degree does not grow
    intro j
    rw [← hform]
    refine degreeOf_le_iff.2 fun m hm => (monomial_le_degreeOf j ?_).trans (hHdeg j)
    rw [mem_support_iff, hHH', coeff_C_mul]
    refine mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)) fun h0 => ?_
    exact mem_support_iff.1 (support_map_subset _ _ hm) h0
  · -- the scaled polynomial vanishes at `X j = 1`
    intro j hj
    have hvan := aeval_update_aeval_C_mul_X_eq_zero (γ := γ) (H := H) (j := j)
      fun m hm => hcon m hm j hj
    simp only [hHH', map_mul, aeval_C, algebraMap_eq] at hvan
    have h3 := congrArg (map (Polynomial.evalRingHom (Polynomial.C ((e₀ : ℕ) : F))))
      ((mul_eq_zero.1 hvan).resolve_left hC)
    rw [map_zero, aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁, map_bind₁] at h3
    have e1 : (fun i => map (Polynomial.evalRingHom (Polynomial.C ((e₀ : ℕ) : F)))
        (Function.update (X : Fin n → MvPolynomial (Fin n) F[X][X]) j 1 i)) =
        Function.update X j 1 := by
      funext v
      by_cases hv : v = j
      · subst hv
        simp
      · simp [Function.update_of_ne hv]
    have e2 : (fun v => map (Polynomial.evalRingHom (Polynomial.C ((e₀ : ℕ) : F)))
        (C (γ v) * X v)) = fun v => C (Polynomial.X ^ (δ + 1) ^ (h v : ℕ) : F[X]) * X v := by
      funext v
      rw [map_mul, map_C, map_X, Polynomial.coe_evalRingHom, hγ, eval_node_seedPoint, hh]
    rwa [e1, e2, hform] at h3

private theorem exists_eval_natCast_ne_zero {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    {q : A[X]} (hq : q ≠ 0) {N : ℕ} (hN : q.natDegree ≤ N) :
    ∃ x ∈ range (N + 1), q.eval (x : A) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hq (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q
    ((range (N + 1)).image Nat.cast) (fun y hy => ?_) ?_)
  · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact hcon x hx
  · rw [card_image_of_injective _ Nat.cast_injective, card_range]
    exact Nat.lt_succ_of_le hN

variable (F) in
open scoped Classical in
/-- The values of the seed point on a grid: an explicit set of shifts of size at most
`(n * δ * P.card + 1) * (n * δ * (δ + 1) ^ k + 1)`. -/
noncomputable def boundedDegreeShifts (δ : ℕ) (P : Finset (Fin n → Fin k)) : Finset (Fin n → F) :=
  (range (n * δ * P.card + 1) ×ˢ range (n * δ * (δ + 1) ^ k + 1)).image fun x j =>
    ((seedPoint F δ P j).eval (Polynomial.C (x.1 : F))).eval (x.2 : F)

/-- **Support-concentrating shifts for any individual degree.** Let `P` be a perfect family of
colourings of `n` variables with `k` colours and `w < 2 ^ k`. Every nonzero polynomial in `n`
variables of individual degree at most `δ` and of split rank at most `w` across every set of `k`
variables has, after shifting by some point of `boundedDegreeShifts F δ P`, a monomial with fewer
than `k` variables. -/
theorem exists_mem_boundedDegreeShifts {P : Finset (Fin n → Fin k)} (hP : IsPerfectHashFamily P k)
    {w δ : ℕ} (hw : w < 2 ^ k) {f : MvPolynomial (Fin n) F} (hf0 : f ≠ 0)
    (hdeg : ∀ i, f.degreeOf i ≤ δ)
    (hf : ∀ Y : Finset (Fin n), Y.card = k → MvPolynomial.SplitRankLE (Y : Set (Fin n)) w f) :
    ∃ a ∈ boundedDegreeShifts F δ P, ∃ m ∈ (MvPolynomial.shift a f).support,
      m.support.card < k := by
  classical
  obtain ⟨m, hm, hmk⟩ := exists_mem_support_shift_card_lt_of_isConcentrating
    (isConcentrating_seedPoint hP hw δ) hf0 hdeg hf
  have ht : f.totalDegree ≤ n * δ :=
    (totalDegree_le_card_mul_of_degreeOf_le hdeg).trans_eq (by rw [Fintype.card_fin])
  obtain ⟨s₀, hs₀, hs⟩ := exists_eval_natCast_ne_zero (mem_support_iff.1 hm)
    (N := n * δ * P.card) ((natDegree_coeff_shift_le _ f (natDegree_seedPoint_le δ P) m).trans
      (Nat.mul_le_mul_right _ ht))
  have h1 : (shift (fun j => (seedPoint F δ P j).eval (Polynomial.C (s₀ : F))) f).coeff m ≠ 0 := by
    have hmap := congrArg (fun q => q.coeff m) (map_shift
      ((Polynomial.aeval (Polynomial.C (s₀ : F)) : F[X][X] →ₐ[F[X]] F[X]).restrictScalars F)
      (seedPoint F δ P) f)
    simp only [coeff_map, RingHom.coe_coe, AlgHom.coe_restrictScalars',
      Polynomial.coe_aeval_eq_eval] at hmap
    rw [← hmap, Polynomial.C_eq_natCast]
    exact hs
  obtain ⟨τ₀, hτ₀, hτ⟩ := exists_eval_natCast_ne_zero h1 (N := n * δ * (δ + 1) ^ k)
    ((natDegree_coeff_shift_le _ f (natDegree_eval_C_seedPoint_le δ P _) m).trans
      (Nat.mul_le_mul_right _ ht))
  refine ⟨fun j => ((seedPoint F δ P j).eval (Polynomial.C (s₀ : F))).eval (τ₀ : F),
    mem_image.2 ⟨(s₀, τ₀), mem_product.2 ⟨hs₀, hτ₀⟩, rfl⟩, m, mem_support_iff.2 ?_, hmk⟩
  have hmap := congrArg (fun q => q.coeff m) (map_shift (Polynomial.aeval (τ₀ : F) : F[X] →ₐ[F] F)
    (fun j => (seedPoint F δ P j).eval (Polynomial.C (s₀ : F))) f)
  simp only [coeff_map, RingHom.coe_coe, Polynomial.coe_aeval_eq_eval] at hmap
  rw [← hmap]
  exact hτ

omit [CharZero F] in
/-- The set of shifts has at most `(n * δ * P.card + 1) * (n * δ * (δ + 1) ^ k + 1)` points. -/
theorem card_boundedDegreeShifts_le (δ : ℕ) (P : Finset (Fin n → Fin k)) :
    (boundedDegreeShifts F δ P).card ≤ (n * δ * P.card + 1) * (n * δ * (δ + 1) ^ k + 1) := by
  classical
  exact card_image_le.trans_eq (by rw [card_product, card_range, card_range])

end Cslib.Circuits.Arithmetic
