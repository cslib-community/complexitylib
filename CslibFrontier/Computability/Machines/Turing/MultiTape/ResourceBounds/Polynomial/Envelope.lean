/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial

/-!
# A common coefficient and degree for polynomial bounds

`PolyBounded.exists_le_succ_pow` absorbs a polynomial's coefficient and degree into one constant
`K * (size + 1) ^ K` that may be enlarged freely, and `PolyBounded.exists_le_self_pow` does the same
with `size ^ K` when the size is positive. These are useful when assembling resource envelopes whose
time bound also contains a separate, possibly exponential, factor.
-/

public section

namespace Turing.MultiTapeTM.PolyBounded

/-- A polynomial bound can use one constant as both coefficient and degree, and any larger
constant also works. -/
theorem exists_le_succ_pow {α : Type*} {size u : α → ℕ} (h : PolyBounded size u) :
    ∃ K : ℕ, ∀ K' ≥ K, ∀ a, u a ≤ K' * (size a + 1) ^ K' := by
  obtain ⟨c, d, hu⟩ := h.exists_le
  exact ⟨c + d, fun K' hK' a => (hu a).trans
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))⟩

/-- A polynomial bound at positive sizes can use one constant as both coefficient and degree.
No bound at size zero is asserted. -/
theorem exists_le_self_pow {α : Type*} {size u : α → ℕ} (h : PolyBounded size u) :
    ∃ K : ℕ, ∀ a, 1 ≤ size a → u a ≤ K * size a ^ K := by
  obtain ⟨c, d, hu⟩ := h.exists_le
  refine ⟨c * 2 ^ d + d, fun a ha => (hu a).trans ?_⟩
  calc
    c * (size a + 1) ^ d ≤ c * (2 * size a) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (c * 2 ^ d) * size a ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]
    _ ≤ (c * 2 ^ d + d) * size a ^ (c * 2 ^ d + d) := by gcongr <;> omega

end Turing.MultiTapeTM.PolyBounded
