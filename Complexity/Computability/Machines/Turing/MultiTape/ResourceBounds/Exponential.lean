/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Polynomial bounds below exponentials

A resource function polynomially bounded in an input size `size` is within a constant multiple of
`2 ^ size` (`Turing.MultiTapeTM.PolyBounded.exists_le_mul_two_pow`), the form of
`Cslib.PolynomiallyBounded.exists_le_mul_two_pow` for arbitrary inputs. Exponential resource
bounds absorb the polynomial costs of their subroutines this way.

## Main results

* `Turing.MultiTapeTM.PolyBounded.exists_le_mul_two_pow`: a polynomially bounded resource
  function is `O(2 ^ size)`.
-/

public section

namespace Turing.MultiTapeTM.PolyBounded

/-- A polynomially bounded resource function is within a constant multiple of `2 ^ size`. -/
theorem exists_le_mul_two_pow {α : Type*} {size u : α → ℕ} (h : PolyBounded size u) :
    ∃ C, ∀ a, u a ≤ C * 2 ^ size a := by
  obtain ⟨c, d, hcd⟩ := h.exists_le
  obtain ⟨C, hC⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => c * (n + 1) ^ d) (by fun_prop)
  exact ⟨C, fun a => (hcd a).trans (hC _)⟩

end Turing.MultiTapeTM.PolyBounded
