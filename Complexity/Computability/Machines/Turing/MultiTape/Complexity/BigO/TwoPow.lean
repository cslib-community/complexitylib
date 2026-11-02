/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Exponential

/-!
# Exponentials of polynomial-time exponents

For an exponent `L x` computable in unary in polynomial time, `2 ^ L x` is computable in unary
within time `O(2 ^ |x| + 4 ^ L x)` and space `O(2 ^ |x| + 2 ^ L x)`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`): compute `L x`,
then double `L x` times (`Turing.MultiTapeTM.ComputableInO.unary_two_pow`). The polynomial cost
of computing the exponent is absorbed by `2 ^ |x|`
(`Turing.MultiTapeTM.PolyBounded.exists_le_mul_two_pow`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`: `2 ^ L x` in
  unary within exponential time and space.
-/

public section

namespace Turing.MultiTapeTM

/-- **`2 ^ L x` in unary**, for an exponent `L x` computable in unary in polynomial time, within
time `O(2 ^ |x| + 4 ^ L x)` and space `O(2 ^ |x| + 2 ^ L x)`. -/
theorem ComputableInPolyTime.exists_computableInO_unary_two_pow {α : Type} {enc : α ↪ List Bool}
    {L : α → ℕ} (hL : ComputableInPolyTime L enc encUnary) :
    ∃ C, ComputableInO (fun x => 2 ^ L x) enc encUnary
      (fun x => C * 2 ^ (enc x).length + 4 ^ L x) (fun x => C * 2 ^ (enc x).length + 2 ^ L x) := by
  obtain ⟨T, S, hT, hS, h⟩ := hL.exists_computableInO
  obtain ⟨C₁, hC₁⟩ := hT.exists_le_mul_two_pow
  obtain ⟨C₂, hC₂⟩ := hS.exists_le_mul_two_pow
  refine ⟨C₁ + C₂, (ComputableInO.unary_two_pow.comp h).mono_le (fun x => ?_) fun x => ?_⟩
  · have h₁ := hC₁ x
    have h₂ : (L x + 1) * 2 ^ L x ≤ 4 ^ L x := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
      exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self
    have h₃ : C₁ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h₁ := hC₂ x
    have h₃ : C₂ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end Turing.MultiTapeTM
