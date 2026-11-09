/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Order.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Odd supports of exponent vectors

The *odd support* `Finsupp.oddSupport m` of an exponent vector `m : σ →₀ ℕ` is the set of
coordinates at which `m` is odd. A monomial `x ^ m` in variables `xᵢ` ranging over `{1, -1}`
equals the product of the variables in its odd support, because `xᵢ ^ 2 = 1`. Odd supports add
by symmetric difference (`Finsupp.oddSupport_add`), so they turn products of monomials into
symmetric differences of sets. The odd support of `∑ i ∈ S, single i 1`, the exponent vector of
`∏ i ∈ S, xᵢ`, is `S` (`Finsupp.oddSupport_sum_single`). These facts are how the multilinear
reduction modulo `xᵢ ^ 2 = 1` enters the sum-of-squares degree lower bound for parity systems
(`Cslib.Logic.PL.ParitySystem.pseudoExpectation`).

## Main definitions

* `Finsupp.oddSupport`: the coordinates at which an exponent vector is odd.

## Main results

* `Finsupp.mem_oddSupport`: `i ∈ oddSupport m ↔ m i % 2 = 1`.
* `Finsupp.oddSupport_add`: odd supports add by symmetric difference.
* `Finsupp.oddSupport_sum_single`: the odd support of the exponent vector of `∏ i ∈ S, xᵢ` is
  `S`.
* `Finsupp.card_oddSupport_le_degree`: the odd support has at most `degree m` elements.
-/

public section

namespace Finsupp

open Finset
open scoped symmDiff

variable {σ : Type*}

/-- The *odd support* of an exponent vector: the coordinates at which it is odd. -/
def oddSupport (m : σ →₀ ℕ) : Finset σ :=
  {i ∈ m.support | m i % 2 = 1}

/-- A coordinate is in the odd support exactly when the exponent there is odd. -/
theorem mem_oddSupport {m : σ →₀ ℕ} {i : σ} : i ∈ oddSupport m ↔ m i % 2 = 1 := by
  rw [oddSupport, mem_filter, mem_support_iff, and_iff_right_iff_imp]
  intro h h0
  rw [h0] at h
  exact absurd h (by decide)

/-- The zero exponent vector has empty odd support. -/
@[simp] theorem oddSupport_zero : oddSupport (0 : σ →₀ ℕ) = ∅ := by
  ext i
  simp [mem_oddSupport]

/-- **Odd supports add by symmetric difference**: a sum is odd exactly where one summand is odd
and the other is even. -/
theorem oddSupport_add [DecidableEq σ] (m n : σ →₀ ℕ) :
    oddSupport (m + n) = oddSupport m ∆ oddSupport n := by
  ext i
  rw [mem_symmDiff, mem_oddSupport, mem_oddSupport, mem_oddSupport, add_apply]
  omega

/-- The exponent vector of `xᵢ ^ 2` has empty odd support. -/
@[simp] theorem oddSupport_single_two (i : σ) : oddSupport (single i 2) = ∅ := by
  classical
  ext j
  rw [mem_oddSupport, single_apply]
  split_ifs <;> simp

/-- The odd support of `∑ i ∈ S, single i 1`, the exponent vector of `∏ i ∈ S, xᵢ`, is `S`. -/
@[simp] theorem oddSupport_sum_single (S : Finset σ) :
    oddSupport (∑ i ∈ S, single i 1) = S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [sum_insert hi, oddSupport_add, ih]
    ext j
    rw [mem_symmDiff, mem_oddSupport, single_apply, mem_insert]
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [Ne.symm hj, hj]

/-- The odd support of `m` has at most `degree m` elements. -/
theorem card_oddSupport_le_degree (m : σ →₀ ℕ) : #(oddSupport m) ≤ m.degree := by
  rw [degree_apply, card_eq_sum_ones]
  refine (Finset.sum_le_sum fun i hi => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have := mem_oddSupport.1 hi
  omega

end Finsupp
