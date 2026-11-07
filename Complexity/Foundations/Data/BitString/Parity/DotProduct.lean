/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# Inner products of bit strings as parities

Over the two-element Boolean ring, the inner product `x ⬝ᵥ w = Σᵢ xᵢ wᵢ` of two bit strings is the
parity of `x` on the support of `w` (`Cslib.BitString.dotProduct_eq_parityOn`). Parities on nonempty
sets are balanced (`Cslib.card_filter_parityOn_eq`), so the inner product with a fixed nonzero
string takes each value on half of the strings (`Cslib.BitString.card_dotProduct_eq_false`).
Consequently a nonzero string lies in the kernel of exactly `2 ^ ((d - 1) c)` of the `2 ^ (d c)`
matrices with `c` rows (`Cslib.BitString.card_kernel`).

## Main results

* `Cslib.BitString.dotProduct_eq_parityOn`: the inner product with `w` is the parity on the support
  of `w`.
* `Cslib.BitString.card_dotProduct_eq_false`: half of the strings are orthogonal to a nonzero `w`.
* `Cslib.BitString.card_kernel`: the matrices whose kernel contains a nonzero `w`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι]

/-- The inner product with `w` is the parity on the support of `w`. -/
theorem dotProduct_eq_parityOn (x w : ι → Bool) : x ⬝ᵥ w = parityOn {i | w i = true} x := by
  rw [parityOn_eq_sum, dotProduct, sum_filter]
  exact sum_congr rfl fun i _ => by cases w i <;> cases x i <;> rfl

section Kernel

variable {c d : ℕ}

/-- The rows orthogonal to a nonzero `w`: `2 ^ (d - 1)` of the `2 ^ d`. -/
theorem card_dotProduct_eq_false {w : Fin d → Bool} (hw : w ≠ 0) :
    #{x : Fin d → Bool | x ⬝ᵥ w = false} = 2 ^ (d - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, w j = true := by
    by_contra h
    simp only [not_exists, Bool.not_eq_true] at h
    exact hw (funext h)
  simp only [dotProduct_eq_parityOn]
  rw [card_filter_parityOn_eq ⟨j, by simpa using hj⟩, Fintype.card_fin]

/-- Matrices with `c` rows whose kernel contains a nonzero `w`: `2 ^ ((d - 1) c)`. -/
theorem card_kernel {w : Fin d → Bool} (hw : w ≠ 0) :
    #{A : Fin c → Fin d → Bool | ∀ i, A i ⬝ᵥ w = false} = (2 ^ (d - 1)) ^ c := by
  rw [← card_dotProduct_eq_false hw, ← Fintype.card_piFinset_const]
  congr 1
  ext A
  simp [Fintype.mem_piFinset]

end Kernel

end Cslib.BitString
