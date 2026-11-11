/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Additive bits of subset sums

An additive map `φ : M →+ Bool` (into the Boolean ring, where addition is exclusive or) sends the
sum `∑ t, if x t then v t else 0` of the vectors `v t` selected by a bit string `x` to the parity of
`x` on the fixed set of indices `t` with `φ (v t) = true`
(`Cslib.BitString.map_sum_ite_eq_parityOn`). For example, a coordinate of an element of a vector
space over `𝔽₂`, read as a bit, is additive. So that coordinate of a sum selected by `x` is a parity
of `x` over a set that does not depend on `x`. This is how a field element computed linearly from
the bits of `x` becomes a row of parity gates.

## Main results

* `Cslib.BitString.map_sum_ite_eq_parityOn`: an additive bit of a subset sum is a parity of the
  selecting string.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι M : Type*} [Fintype ι] [AddCommMonoid M]

/-- **An additive bit of a subset sum is a parity.** For an additive map `φ : M →+ Bool`, the bit
`φ (∑ t, if x t then v t else 0)` of the sum of the vectors `v t` selected by `x` is the parity of
`x` on the indices `t` with `φ (v t) = true`. -/
theorem map_sum_ite_eq_parityOn (φ : M →+ Bool) (v : ι → M) (x : ι → Bool) :
    φ (∑ t, if x t then v t else 0) = parityOn {t | φ (v t) = true} x := by
  classical
  rw [map_sum, parityOn_eq_sum, sum_filter]
  refine sum_congr rfl fun t _ => ?_
  cases x t <;> cases h : φ (v t) <;> simp [h, Bool.zero_eq_false]

end Cslib.BitString
