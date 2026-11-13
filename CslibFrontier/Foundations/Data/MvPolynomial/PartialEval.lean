/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Finsupp.Weight

/-!
# Assigning constants to some of the variables of a polynomial

Over an infinite integral domain, a nonzero polynomial in the variables `α ⊕ β` stays nonzero
after some assignment of constants to the variables `α`, the variables `β` being kept
(`MvPolynomial.exists_aeval_sumElim_ne_zero`). The polynomial is viewed as a polynomial in the
variables `β` over `MvPolynomial α R` (`MvPolynomial.sumAlgEquiv`); one of its coefficients is
nonzero, hence nonzero at some point of `R ^ α` (`MvPolynomial.funext`), and evaluating the
coefficients at that point gives the assignment.

Substituting variables for the variables `i ∈ A` of a multilinear polynomial and constants for
the others gives a polynomial each of whose monomials is the product of the variables substituted
for a subset of `A`: at most `2 ^ #A` monomials, of total degree at most `#A`
(`MvPolynomial.card_support_aeval_le_of_degreeOf_le_one`,
`MvPolynomial.totalDegree_aeval_le_card_of_degreeOf_le_one`).

## Main results

* `MvPolynomial.exists_aeval_sumElim_ne_zero`: a nonzero polynomial stays nonzero under some
  assignment of constants to part of its variables.
* `MvPolynomial.support_aeval_subset_of_degreeOf_le_one`: the monomials of a partially
  specialized multilinear polynomial.
* `MvPolynomial.card_support_aeval_le_of_degreeOf_le_one`,
  `MvPolynomial.totalDegree_aeval_le_card_of_degreeOf_le_one`: their number and degree.
-/

public section

namespace MvPolynomial

open Finset

section Infinite

variable {R α β : Type*} [CommRing R] [IsDomain R] [Infinite R]

/-- **Partial evaluation.** Over an infinite integral domain, a nonzero polynomial in the variables
`α ⊕ β` stays nonzero after some assignment of constants to the variables `α`. -/
theorem exists_aeval_sumElim_ne_zero {p : MvPolynomial (α ⊕ β) R} (hp : p ≠ 0) :
    ∃ v : α → R, aeval (Sum.elim (fun a => C (v a)) X) p ≠ 0 := by
  set e := (sumAlgEquiv R β α).toAlgHom.comp (rename Sum.swap)
  have he : e p ≠ 0 := by
    simpa [e, map_eq_zero_iff _ (rename_injective _ Sum.swap_leftInverse.injective)] using hp
  obtain ⟨s, hs⟩ := ne_zero_iff.1 he
  obtain ⟨v, hv⟩ : ∃ v : α → R, eval v ((e p).coeff s) ≠ 0 := by
    by_contra! h
    exact hs (funext fun v => by simpa using h v)
  refine ⟨v, fun h => hv ?_⟩
  have hcomp : (mapAlgHom (aeval v)).comp e = aeval (Sum.elim (fun a => C (v a)) X) := by
    refine algHom_ext fun x => ?_
    cases x <;> simp [e]
  have hmap : map (eval v) (e p) = (mapAlgHom (aeval v)).comp e p := rfl
  rw [← coeff_map, hmap, hcomp, h]
  simp

end Infinite

/-! ### Specializing a multilinear polynomial -/

section Multilinear

variable {R σ τ : Type*} [CommSemiring R]

/-- Substituting monomials `monomial (d i) 1` for the variables `i ∈ A` and constants for the
others in a multilinear polynomial gives a polynomial whose monomials are the products of the
`monomial (d i) 1` over subsets of `A`. -/
theorem support_aeval_subset_of_degreeOf_le_one [DecidableEq τ] {p : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) {g : σ → MvPolynomial τ R} {A : Finset σ}
    {d : σ → τ →₀ ℕ} (hA : ∀ i ∈ A, g i = monomial (d i) 1)
    (hC : ∀ i ∉ A, ∃ c, g i = C c) :
    (aeval g p).support ⊆ A.powerset.image fun U => ∑ i ∈ U, d i := by
  classical
  choose! c hc using hC
  conv_lhs => rw [p.as_sum, map_sum]
  refine support_sum.trans (biUnion_subset.2 fun s hs => ?_)
  have hs1 (i : σ) (hi : i ∈ s.support) : s i = 1 :=
    le_antisymm (degreeOf_le_iff.1 (hp i) s hs)
      (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
  have hprod : (s.prod fun i k => g i ^ k) = C (∏ i ∈ s.support with i ∉ A, c i) *
      monomial (∑ i ∈ s.support with i ∈ A, d i) 1 := by
    rw [Finsupp.prod, ← prod_filter_mul_prod_filter_not s.support (· ∈ A), mul_comm, map_prod,
      monomial_sum_one]
    congr 1 <;> refine prod_congr rfl fun i hi => ?_ <;> rw [mem_filter] at hi <;>
      rw [hs1 i hi.1, pow_one]
    · exact hc i hi.2
    · exact hA i hi.2
  rw [aeval_monomial, hprod, algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]
  exact support_monomial_subset.trans <| singleton_subset_iff.2 <|
    mem_image.2 ⟨_, mem_powerset.2 fun i hi => (mem_filter.1 hi).2, rfl⟩

private theorem exists_monomial_of_eq_X {g : σ → MvPolynomial τ R} {A : Finset σ}
    (hA : ∀ i ∈ A, ∃ x, g i = X x) :
    ∃ d : σ → τ →₀ ℕ, ∀ i ∈ A, g i = monomial (d i) 1 ∧ (d i).degree = 1 := by
  choose! d hd using fun i (hi : i ∈ A) =>
    let ⟨x, hx⟩ := hA i hi
    (⟨Finsupp.single x 1, hx, Finsupp.degree_single x 1⟩ :
      ∃ d : τ →₀ ℕ, g i = monomial d 1 ∧ d.degree = 1)
  exact ⟨d, hd⟩

/-- Substituting variables for the variables of `A` and constants for the others in a multilinear
polynomial gives at most `2 ^ #A` monomials. -/
theorem card_support_aeval_le_of_degreeOf_le_one {p : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) {g : σ → MvPolynomial τ R} {A : Finset σ}
    (hA : ∀ i ∈ A, ∃ x, g i = X x) (hC : ∀ i ∉ A, ∃ c, g i = C c) :
    #(aeval g p).support ≤ 2 ^ #A := by
  classical
  obtain ⟨d, hd⟩ := exists_monomial_of_eq_X hA
  refine (card_le_card <| support_aeval_subset_of_degreeOf_le_one hp (fun i hi => (hd i hi).1)
    hC).trans (card_image_le.trans (card_powerset A).le)

/-- Substituting variables for the variables of `A` and constants for the others in a multilinear
polynomial gives total degree at most `#A`. -/
theorem totalDegree_aeval_le_card_of_degreeOf_le_one {p : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) {g : σ → MvPolynomial τ R} {A : Finset σ}
    (hA : ∀ i ∈ A, ∃ x, g i = X x) (hC : ∀ i ∉ A, ∃ c, g i = C c) :
    (aeval g p).totalDegree ≤ #A := by
  classical
  obtain ⟨d, hd⟩ := exists_monomial_of_eq_X hA
  refine Finset.sup_le fun s hs => ?_
  obtain ⟨U, hU, rfl⟩ := mem_image.1
    (support_aeval_subset_of_degreeOf_le_one hp (fun i hi => (hd i hi).1) hC hs)
  change Finsupp.degree _ ≤ _
  rw [map_sum, sum_congr rfl fun i hi => (hd i (mem_powerset.1 hU hi)).2, sum_const, smul_eq_mul,
    mul_one]
  exact card_le_card (mem_powerset.1 hU)

end Multilinear

end MvPolynomial
