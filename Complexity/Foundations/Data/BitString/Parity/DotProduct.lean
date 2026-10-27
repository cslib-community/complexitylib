/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Data.Matrix.Mul

/-!
# Inner products of bit strings as parities

Over the two-element Boolean ring, the inner product `x ⬝ᵥ w = Σᵢ xᵢ wᵢ` of two bit strings is the
parity of `x` on the support of `w` (`Cslib.BitString.dotProduct_eq_parityOn`). Parities on nonempty
sets are balanced (`Cslib.card_filter_parityOn_eq`), so the inner product with a fixed nonzero
string takes each value on half of the strings.

## Main results

* `Cslib.BitString.dotProduct_eq_parityOn`: the inner product with `w` is the parity on the support
  of `w`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι]

/-- The inner product with `w` is the parity on the support of `w`. -/
theorem dotProduct_eq_parityOn (x w : ι → Bool) : x ⬝ᵥ w = parityOn {i | w i = true} x := by
  rw [parityOn_eq_sum, dotProduct, sum_filter]
  exact sum_congr rfl fun i _ => by cases w i <;> cases x i <;> rfl

end Cslib.BitString
