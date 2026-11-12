/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.LowerBound
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.UpperBound

/-!
# Homogeneous depth-five circuits for `IMM`: both bounds

For `n = 2` one block of two layers gives a circuit for `IMM_{2,2}` with `8 + 4 + 4 = 16` gates.
Over the rationals, for all sufficiently large `n`, some circuit for `IMM_{n,n}` has size at
most `n ^ (√n + 4)` and every circuit has size at least `n ^ (√n / 400)`.
-/

public section

namespace CslibFrontierTests.DepthFiveUpper

open Cslib.Circuits.DepthFive Cslib.Circuits.Arithmetic

/-- One block of two layers computes `IMM_{2,2}` with sixteen gates. -/
theorem exists_circuit_imm_two :
    ∃ d : Circuit ℚ (Fin 2 × Fin 2 × Fin 2), d.polynomial = imm ℚ 2 2 ∧ d.size = 16 :=
  exists_circuit_imm_of_le_mul ℚ (r := 1) (t := 2) (by norm_num)

/-- Over the rationals the size of `IMM_{n,n}` is `n ^ Θ(√n)`. -/
theorem size_imm_rat : ∃ n₀ : ℕ, ∀ (n : ℕ) [NeZero n], n₀ ≤ n →
    (∃ d : Circuit ℚ (Fin n × Fin n × Fin n),
      d.polynomial = imm ℚ n n ∧ (d.size : ℝ) ≤ (n : ℝ) ^ (√(n : ℝ) + 4)) ∧
    ∀ c : Circuit ℚ (Fin n × Fin n × Fin n), c.polynomial = imm ℚ n n →
      (n : ℝ) ^ (√(n : ℝ) / 400) ≤ c.size := by
  obtain ⟨n₀, h⟩ := exists_forall_rpow_le_size.{0}
  exact ⟨max n₀ 2, fun n _ hn =>
    ⟨exists_circuit_size_le_rpow ℚ (le_of_max_le_right hn), h ℚ n (le_of_max_le_left hn)⟩⟩

end CslibFrontierTests.DepthFiveUpper
