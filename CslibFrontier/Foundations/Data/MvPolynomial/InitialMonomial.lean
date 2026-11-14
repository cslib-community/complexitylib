/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Polynomials with distinct initial monomials are linearly independent

Weigh the monomials by a function `ω` into a linear order. If each polynomial of a family has a
monomial of strictly least weight among its monomials, and these initial monomials are pairwise
distinct, then the family is linearly independent: in a nontrivial relation, the initial monomial
of least weight among the polynomials that occur appears in one polynomial only.

## Main results

* `MvPolynomial.linearIndependent_of_initial_monomial`: the statement above.
-/

public section

namespace MvPolynomial

open Finset

variable {ι σ R α : Type*} [CommRing R] [NoZeroDivisors R] [LinearOrder α]

/-- Polynomials `v i` whose monomials of strictly least weight `b i` are pairwise distinct are
linearly independent. -/
theorem linearIndependent_of_initial_monomial (ω : (σ →₀ ℕ) → α) {v : ι → MvPolynomial σ R}
    {b : ι → σ →₀ ℕ} (hb : Function.Injective b) (hv : ∀ i, (v i).coeff (b i) ≠ 0)
    (hlt : ∀ i, ∀ m ∈ (v i).support, m ≠ b i → ω (b i) < ω m) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hci₀⟩ := hne
  obtain ⟨i, hi, hmin⟩ := exists_min_image (s.filter (c · ≠ 0)) (fun i => ω (b i))
    ⟨i₀, mem_filter.2 ⟨hi₀, hci₀⟩⟩
  rw [mem_filter] at hi
  have h : (∑ i ∈ s, c i • v i).coeff (b i) = 0 := by rw [hc]; rfl
  rw [coeff_sum, sum_eq_single_of_mem i hi.1, coeff_smul, smul_eq_mul] at h
  · exact mul_ne_zero hi.2 (hv i) h
  · intro i' hi' hne'
    rw [coeff_smul, smul_eq_mul]
    by_contra h0
    exact (hmin i' (mem_filter.2 ⟨hi', left_ne_zero_of_mul h0⟩)).not_gt
      (hlt i' (b i) (mem_support_iff.2 (right_ne_zero_of_mul h0)) (hb.ne hne'.symm))

end MvPolynomial
