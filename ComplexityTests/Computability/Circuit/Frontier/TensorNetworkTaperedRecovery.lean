/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TaperedRecovery

/-!
# Tests for tapered Hermite recovery with finite precision

The grid of two slots (`a = 1`) has the nodes `-2, -1, 1`. With `u = 2` and `h = 3`, the odd nodes
have multiplicity `6` and the node `-2`, of valuation one, has multiplicity `3`. The precision
theorem applies over `K = ℚ` with `B = ℤ_(2)`: its hypotheses are met by exact jets.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.TaperedRecovery

open Cslib.Circuits.Frontier Polynomial

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

example : recoveryNodes 1 = {-2, -1, 1} := by decide

example : taperMult 2 3 1 = 6 ∧ taperMult 2 3 (-1) = 6 := by
  simp [taperMult, padicValInt]

example : taperMult 2 3 (-2) = 3 := by
  simp [taperMult, padicValInt]

/-- The total multiplicity of the two odd nodes alone is `2 * 6`. -/
example : 2 ^ 1 * (3 * 2) ≤ ∑ t ∈ recoveryNodes 1, taperMult 2 3 t :=
  le_sum_taperMult 1 2 3

/-- **Non-vacuity.** For `F = X` (degree `1 = M (2 L - 1)` with `M = 1`, `L = 1`), `u = 1` and
`h = 3`, exact jets recover `F(0)` modulo every `2 ^ p`. -/
theorem exists_taperedRecovery_X (p : ℕ) :
    ∃ b ∈ ℤ₍₂₎, taperedRecovery 0 1 3 (fun t => (X : ℚ[X]).comp (C (t : ℚ) + C (2 ^ (0 + 1)) * X)) =
      (X : ℚ[X]).eval 0 + 2 ^ p * b :=
  exists_taperedRecovery_eq_add_of_params (K := ℚ) (M := 1) ℤ₍₂₎ (fun c hc => hc) le_rfl le_rfl
    (by norm_num) (by norm_num) (by rw [natDegree_X]; norm_num) _
    (fun t _ j _ => ⟨0, zero_mem _, by rw [mul_zero, add_zero]⟩)

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.TaperedRecovery
