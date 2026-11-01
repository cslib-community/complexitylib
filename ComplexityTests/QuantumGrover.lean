/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Grover

/-! Grover's algorithm: concrete instances. -/

namespace ComplexityTests.QuantumGrover

open Cslib.Quantum

-- With `N = 4`, Grover's algorithm finds the marked item with probability at least `3 / 4` using
-- at most `π √4 / 4 = π / 2` queries.
example (z : Fin 4) :
    1 - ((4 : ℕ) : ℝ)⁻¹ ≤ regProb (run (grover 4) (uniform 4) (marked z)
        ⌊Real.pi / (4 * groverAngle 4)⌋₊) z ∧
      (⌊Real.pi / (4 * groverAngle 4)⌋₊ : ℝ) ≤ Real.pi * Real.sqrt (4 : ℕ) / 4 :=
  grover_success (by norm_num) z

-- Grover's algorithm is a query algorithm with a unit initial state that succeeds with probability
-- `3 / 4 ≥ 2 / 3`, so it satisfies the hypothesis of the BBBV bound, a non-vacuous instance.
example : ‖uniform 4‖ = 1 := norm_uniform (by norm_num)

example : ((4 : ℕ) : ℝ) - 2 ≤ 144 * ((⌊Real.pi / (4 * groverAngle 4)⌋₊ : ℕ) : ℝ) ^ 2 :=
  card_sub_two_le (grover 4) (norm_uniform (by norm_num)) _ fun z =>
    le_trans (by norm_num) (grover_success (by norm_num) z).1

-- Before any query, the marked item has probability `sin² θ`.
example (z : Fin 4) :
    regProb (run (grover 4) (uniform 4) (marked z) 0) z = Real.sin (groverAngle 4) ^ 2 := by
  simpa using regProb_run_grover (by norm_num) z 0

-- With `N = 4` the Grover angle is `arcsin(1/2) = π / 6`, so `(2 · 1 + 1) θ = π / 2`: a single
-- query finds the marked item with certainty.
theorem groverAngle_four : groverAngle 4 = Real.pi / 6 := by
  have h : (Real.sqrt ((4 : ℕ) : ℝ))⁻¹ = Real.sin (Real.pi / 6) := by
    rw [Real.sin_pi_div_six, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [groverAngle, h, Real.arcsin_sin] <;> linarith [Real.pi_pos]

example (z : Fin 4) : regProb (run (grover 4) (uniform 4) (marked z) 1) z = 1 := by
  rw [regProb_run_grover (by norm_num), groverAngle_four,
    show (2 * ((1 : ℕ) : ℝ) + 1) * (Real.pi / 6) = Real.pi / 2 by push_cast; ring,
    Real.sin_pi_div_two, one_pow]

end ComplexityTests.QuantumGrover
