/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Continuity
import Complexity.Computability.Circuit.Complexity

/-! The modulus of continuity of De Morgan circuit complexity: a single changed input moves the
complexity of a projection, the modulus vanishes at zero and is subadditive, the square-root upper
bounds instantiated, and the lower bound `2 ^ 4 ≤ 16 ω_{8,1}(2 ^ 4)`. -/

namespace ComplexityTests.CircuitHamming.Continuity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### A single changed input -/

/-- The projection on one input and the constant `false` differ on one input. -/
theorem hammingDist_proj_false :
    hammingDist (single fun x : BitString 1 => x 0) (single fun _ => false) = 1 := by
  decide

/-- **A single changed input moves the complexity**: `hammingDist_single`, `1 ≤ ω_{1,1}(1)`,
subadditivity `ω_{1,1}(2) ≤ 2 ω_{1,1}(1)`, `ω_{3,2}(0) = 0`, and attainment of `ω_{2,1}(1)`. -/
example :
    hammingDist (single fun x : BitString 1 => x 0) (single fun _ => false) =
      hammingDist (fun x : BitString 1 => x 0) (fun _ => false) ∧
    1 ≤ complexityModulus interpretation 1 1 1 ∧
    complexityModulus interpretation 1 1 2 ≤ 2 * complexityModulus interpretation 1 1 1 ∧
    complexityModulus interpretation 3 2 0 = 0 ∧
    ∃ f g : BitString 2 → Fin 1 → Bool, hammingDist f g ≤ 1 ∧
      Nat.dist (complexity interpretation f) (complexity interpretation g) =
        complexityModulus interpretation 2 1 1 := by
  refine ⟨by rw [hammingDist_single], ?_, complexityModulus_le_mul, complexityModulus_zero,
    exists_dist_complexity_eq_complexityModulus⟩
  have hfalse : 1 ≤ complexity interpretation (single fun _ : BitString 1 => false) :=
    one_le_complexity_single fun i h => by
      have := congrFun h fun _ => true
      simp at this
  refine le_trans ?_ (dist_complexity_le_complexityModulus hammingDist_proj_false.le)
  rw [complexity_single_proj, Nat.dist_zero_left]
  exact hfalse

/-! ### Square-root continuity -/

/-- Single-output and multi-output square-root continuity upper bounds at `ε = 1`, and the lower
bound `1 ≤ ω_{8,1}(16)` at `p = 4`. -/
example :
    (∃ p₀ : ℕ, ∀ p ≥ p₀,
      (complexityModulus interpretation (2 * p) 1 (2 ^ p) : ℝ) ≤ (1 + 1) * 2 ^ p) ∧
    (∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p,
      (complexityModulus interpretation (2 * p) m (2 ^ p) : ℝ) ≤ (3 + 1) * 2 ^ p) ∧
    1 ≤ complexityModulus interpretation (2 * 4) 1 (2 ^ 4) := by
  refine ⟨complexityModulus_two_pow_single_output_le 1 one_pos,
    complexityModulus_two_pow_le 1 one_pos, ?_⟩
  have h := two_pow_le_sixteen_mul_complexityModulus (p := 4) le_rfl
  exact Nat.one_le_iff_ne_zero.2 fun h0 => by rw [h0] at h; exact absurd h (by norm_num)

end ComplexityTests.CircuitHamming.Continuity
