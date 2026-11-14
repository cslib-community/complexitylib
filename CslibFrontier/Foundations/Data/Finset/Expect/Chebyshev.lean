/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, finite-average probability inequalities)

public import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Chebyshev bounds for uniform finite averages

A function exceeds a positive absolute threshold on a set of density at most its second moment
divided by the squared threshold. Apply this to `fun i => f i - c` for deviations about any
center `c`, including the uniform mean. Both strict and non-strict tails are available.

## Main results

* `Fintype.dens_le_abs_le_expect_sq_div_sq`: non-strict absolute tail.
* `Fintype.dens_lt_abs_le_expect_sq_div_sq`: strict absolute tail.
-/

public section

namespace Fintype

open Finset
open scoped BigOperators

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The density of an absolute tail is bounded by the second moment divided by the threshold
squared. Subtract a chosen center from `f` to obtain Chebyshev's inequality. -/
theorem dens_le_abs_le_expect_sq_div_sq (f : ι → 𝕜) {ε : 𝕜} (hε : 0 < ε) :
    (dens {i | ε ≤ |f i|} : 𝕜) ≤ (𝔼 i, f i ^ 2) / ε ^ 2 := by
  classical
  have h := mul_dens_filter_le_expect (f := fun i => f i ^ 2)
    (fun _ => sq_nonneg _) (ε ^ 2)
  simp only [sq_le_sq, abs_of_pos hε] at h
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h

/-- The same second-moment bound holds for a strict absolute tail. -/
theorem dens_lt_abs_le_expect_sq_div_sq (f : ι → 𝕜) {ε : 𝕜} (hε : 0 < ε) :
    (dens {i | ε < |f i|} : 𝕜) ≤ (𝔼 i, f i ^ 2) / ε ^ 2 := by
  classical
  have hsub : ({i | ε < |f i|} : Finset ι) ⊆ ({i | ε ≤ |f i|} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.le
  have h : (dens {i | ε < |f i|} : 𝕜) ≤ (dens {i | ε ≤ |f i|} : 𝕜) := by
    exact_mod_cast dens_le_dens hsub
  exact h.trans (dens_le_abs_le_expect_sq_div_sq f hε)

end Fintype
