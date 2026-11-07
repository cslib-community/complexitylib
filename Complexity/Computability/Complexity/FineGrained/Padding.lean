/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow

/-!
# Exponential time by padding

A decision procedure that runs in polynomial time on padded inputs `(a, 2 ^ ν a)`, with the
padding in unary, gives a decision procedure for the original instances within time
`2 ^ (δ μ a)` times a polynomial, for an exponent `ν ≤ μ` computable in unary in polynomial time
(`Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime_pad`). The machine writes the padding
and runs the polynomial-time procedure
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`). The constant `δ` comes from
the degree of the polynomial bound, and is not explicit.

This is how a dynamic program over `2 ^ k` states, polynomial-time in the number of its states, is
stated as an exponential-time or fpt algorithm in the parameter `k` on multi-tape machines.

## Main results

* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime_pad`: polynomial time on inputs
  padded by `2 ^ ν a` gives `DecidableInExpTime` in any `μ ≥ ν`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Exponential time by padding.** If `Ψ` is polynomial-time on pairs `(a, N)` with `N` in unary,
and `A` is decided by `Ψ` on the padded inputs `(a, 2 ^ ν a)`, for a unary exponent `ν ≤ μ`
computable in polynomial time, then `A` is decidable within time `2 ^ (δ μ a)` times a polynomial,
for some `δ`. -/
theorem DecidableInExpTime.of_computableInPolyTime_pad {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ ν : α → ℕ} {Ψ : α × ℕ → Bool}
    (hΨ : ComputableInPolyTime Ψ (encPair enc encUnary) encBool)
    (hν : ComputableInPolyTime ν enc encUnary) (hνμ : ∀ a, ν a ≤ μ a)
    (hA : ∀ a, a ∈ A ↔ Ψ (a, 2 ^ ν a) = true) :
    ∃ δ : ℝ, DecidableInExpTime A enc μ δ := by
  obtain ⟨C, D, h⟩ := hΨ.exists_computableInO_pad hν
  refine ⟨D, DecidableInExpTime.of_computableInO h hA C D fun a => ?_⟩
  have h2 : (2 : ℝ) ^ (D * ν a) ≤ (2 : ℝ) ^ ((D : ℝ) * (μ a : ℝ)) := by
    rw [show (D : ℝ) * (μ a : ℝ) = ((D * μ a : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left D (hνμ a))
  push_cast
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)

end Cslib.Complexity
