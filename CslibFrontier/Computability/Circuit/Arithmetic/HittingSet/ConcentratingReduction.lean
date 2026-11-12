/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Concentrating

/-!
# Concentrating points give monomials of small support

Let `f` be a nonzero polynomial of individual degree at most `δ` and of split rank at most `w`
across every set of `k` variables (`MvPolynomial.SplitRankLE`). If the point `γ` is concentrating
for `k`, `w`, `δ` (`IsConcentrating`), then `f (X + γ)` has a monomial with fewer than `k`
variables (`exists_mem_support_shift_card_lt_of_isConcentrating`).

This is the form, for any individual degree, of the argument of
`CslibFrontier/Computability/Circuit/Arithmetic/HittingSet/ConcentratingShift.lean`, which treats
multilinear polynomials. There a substitution isolates the monomial of least support; a monomial
of higher degree is not determined by its support, so here partial derivatives do the isolating.
The argument is not taken from a source. In the literature the statement for any individual
degree is obtained from rank condensers
[ForbesSaptharishiShpilka2014, Theorem 4.1 with Corollary 3.22].

## Proof

Take a monomial `m₀` of `G = f (X + γ)` with the fewest variables, and suppose it has `k`
variables `Y` among its variables. Let `μ` be the part of `m₀` outside `Y`, and let `S` be the
derivative `∂^μ G` with the variables outside `Y` set to zero. The monomials of `S` are the
monomials `m` in the variables of `Y` with `m + μ` a monomial of `G`. So `S` has the monomial
`m₀ - μ`, and by the minimality of `m₀` each of its monomials contains every variable of `Y`. On
the other hand `f = ∑ᵢ pᵢ qᵢ` with `pᵢ` in the variables of `Y` and `qᵢ` in the others; the
derivatives pass `pᵢ (X + γ)`, and setting the variables outside `Y` to zero turns
`∂^μ qᵢ (X + γ)` into a constant `ρᵢ`. So `S = ∑ᵢ ρᵢ pᵢ (X + γ)`, of individual degree at most
`δ`, and a concentrating point gives it a monomial that misses a variable of `Y`.

## Main results

* `exists_mem_support_shift_card_lt_of_isConcentrating`: the shift by a concentrating point of a
  nonzero polynomial of small split rank and bounded individual degree has a monomial of small
  support.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

/-- **Small-support concentration at a concentrating point.** If `γ` is concentrating for `k`,
`w`, `δ` and `f` is a nonzero polynomial of individual degree at most `δ` and of split rank at
most `w` across every set of `k` variables, then `f (X + γ)` has a monomial with fewer than `k`
variables. -/
theorem exists_mem_support_shift_card_lt_of_isConcentrating {σ F R : Type*} [Field F]
    [CommRing R] [IsDomain R] [CharZero R] [Algebra F R] {γ : σ → R} {k w δ : ℕ}
    (hγ : IsConcentrating F γ k w δ) {f : MvPolynomial σ F} (hf0 : f ≠ 0)
    (hdeg : ∀ i, f.degreeOf i ≤ δ)
    (hf : ∀ Y : Finset σ, Y.card = k → MvPolynomial.SplitRankLE (Y : Set σ) w f) :
    ∃ m ∈ (MvPolynomial.shift γ f).support, m.support.card < k := by
  classical
  set G : MvPolynomial σ R := shift γ f with hG
  have hG0 : G ≠ 0 := fun h => hf0 (shift_injective (algebraMap F R).injective γ
    (h.trans (map_zero _).symm))
  obtain ⟨m₀, hm₀, hmin⟩ := Finset.exists_min_image G.support (fun m => m.support.card)
    (support_nonempty.2 hG0)
  refine ⟨m₀, hm₀, ?_⟩
  by_contra hk
  obtain ⟨Y, hYM, hYk⟩ := Finset.exists_subset_card_eq (not_lt.1 hk)
  obtain ⟨p, q, hp, hq, hfpq⟩ := hf Y hYk
  -- the part `μ` of `m₀` outside `Y`, as a tuple `α` of variables
  set μ : σ →₀ ℕ := m₀.filter (· ∉ Y) with hμ
  obtain ⟨N, α, hα⟩ := μ.exists_fin_sum_single_one_eq
  have hαY : ∀ i, α i ∉ (Y : Set σ) := fun i hi => by
    have h : μ (α i) = 0 := Finsupp.filter_apply_neg _ _ (not_not.2 (mem_coe.1 hi))
    rw [← hα, Finset.sum_apply', Finset.sum_eq_zero_iff] at h
    simpa using h i (mem_univ i)
  -- the derivative along `α` with the variables outside `Y` set to zero, and its monomials
  set S : MvPolynomial σ R :=
    aeval (fun v => if v ∈ (Y : Set σ) then X v else 0) (iteratedPDeriv α G) with hS
  have hcoeff : ∀ m, S.coeff m ≠ 0 ↔ (∀ i ∈ m.support, i ∈ Y) ∧ G.coeff (m + μ) ≠ 0 := fun m => by
    have h := coeff_iteratedPDeriv_ne_zero_iff α G m
    rw [hα] at h
    by_cases hm : ∀ i ∈ m.support, i ∈ (Y : Set σ)
    · rw [hS, coeff_aeval_ite_mem_X_zero, ite_eq_left hm, h]
      exact (and_iff_right fun i hi => mem_coe.1 (hm i hi)).symm
    · rw [hS, coeff_aeval_ite_mem_X_zero, ite_eq_right hm]
      exact iff_of_false (fun h0 => h0 rfl) fun h0 => hm h0.1
  have hS0 : S ≠ 0 := fun h0 => (hcoeff (m₀.filter (· ∈ Y))).2
    ⟨fun j hj => by_contra fun hjY =>
      Finsupp.mem_support_iff.1 hj (Finsupp.filter_apply_neg _ _ hjY), by
      rw [hμ, Finsupp.filter_add_filter_not]
      exact mem_support_iff.1 hm₀⟩ (by rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])
  have hfull : ∀ m ∈ S.support, ∀ j ∈ Y, m j ≠ 0 := fun m hm j hj hmj => by
    obtain ⟨hmY, hmG⟩ := (hcoeff m).1 (mem_support_iff.1 hm)
    have h1 := hmin _ (mem_support_iff.2 hmG)
    have h2 : (m + μ).support ⊆ Y.erase j ∪ m₀.support \ Y :=
      Finsupp.support_add.trans (union_subset_union
        (fun i hi => mem_erase.2 ⟨fun h => Finsupp.mem_support_iff.1 hi (h ▸ hmj), hmY i hi⟩)
        (by rw [hμ, Finsupp.support_filter]; exact fun i hi => mem_sdiff.2 (mem_filter.1 hi)))
    have h3 := (card_le_card h2).trans (card_union_le _ _)
    rw [card_erase_of_mem hj, card_sdiff_of_subset hYM, hYk] at h3
    have h4 := card_pos.2 ⟨j, hj⟩
    omega
  have hSdeg : ∀ j, S.degreeOf j ≤ δ := fun j => degreeOf_le_iff.2 fun m hm =>
    (le_of_le_of_eq (Nat.le_add_right _ _) (Finsupp.add_apply m μ j).symm).trans
      ((monomial_le_degreeOf j (mem_support_iff.2 ((hcoeff m).1 (mem_support_iff.1 hm)).2)).trans
        ((degreeOf_shift_le γ f j).trans (hdeg j)))
  -- the same operator applied to the decomposition of `f` across `Y`
  have hsum : S = ∑ i, C (constantCoeff (iteratedPDeriv α (shift γ (q i)))) * shift γ (p i) := by
    rw [hS, hG, hfpq]
    simp only [map_sum, map_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [iteratedPDeriv_mul_of_mem_supported (shift_mem_supported (hp i) γ) _ hαY, map_mul,
      mul_comm]
    congr 1
    · rw [← algebraMap_eq, ← aeval_zero]
      exact aeval_congr_of_mem_supported
        (iteratedPDeriv_mem_supported (shift_mem_supported (hq i) γ) α) fun j hj => by
          simp only [show j ∉ (Y : Set σ) from hj, ↓reduceIte, Pi.zero_apply]
    · exact (aeval_congr_of_mem_supported (shift_mem_supported (hp i) γ) fun j hj => by
        simp only [hj, ↓reduceIte]).trans (aeval_X_left_apply _)
  rw [hsum] at hS0 hSdeg hfull
  obtain ⟨m, hm, j, hj, hmj⟩ := hγ Y hYk p hp _ hS0 hSdeg
  exact hfull m hm j hj hmj

end Cslib.Circuits.Arithmetic
