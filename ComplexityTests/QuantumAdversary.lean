/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Adversary
import Complexity.Computability.QueryComplexity.Quantum.UnknownSearch
import ComplexityTests.QuantumPolynomial

/-! Spectral sensitivity and the quartic bound `D(f) ≤ 20736 T⁴`: the spectral sensitivity of
parity, and the bounds applied to the exact one-query algorithm `readBit` and to the `OR_N`
algorithm `orSearch`, so their hypotheses are satisfiable by non-constant functions. -/

namespace ComplexityTests.QuantumAdversary

open Cslib Cslib.Quantum Cslib.BitString Cslib.QueryComplexity Finset
open ComplexityTests.QuantumPolynomial

/-- Every coordinate is sensitive for parity. -/
theorem sensitiveCoords_parity {n : ℕ} (x : BitString n) : sensitiveCoords (parity n) x = univ :=
  eq_univ_of_forall fun i => mem_sensitiveCoords.2 <| by
    rw [IsSensitiveCoord, parity, parityOn_update_not (mem_univ i)]
    cases parityOn univ x <;> decide

/-- **The spectral sensitivity of parity is `n`**: its sensitivity graph is the whole cube, the
constant function `1` is an eigenvector of `A_f` for `n`, and `λ ≤ s ≤ n`. -/
theorem spectralSensitivity_parity (n : ℕ) : spectralSensitivity (parity n) = n := by
  refine le_antisymm ((spectralSensitivity_le_sensitivity _).trans
    (Nat.cast_le.2 (sensitivity_le_card _))) ?_
  refine le_spectralSensitivity_of_le_sum (v := fun _ => 1) (fun _ => zero_le_one)
    (fun h => one_ne_zero (congrFun h fun _ => false)) fun x => ?_
  simp [sensitiveCoords_parity]

-- Huang's theorem in spectral form: `deg(PARITY_n) = n ≤ λ(PARITY_n)² = n²`.
example (n : ℕ) : (degree (parity n) : ℝ) ≤ spectralSensitivity (parity n) ^ 2 :=
  degree_le_spectralSensitivity_sq _

example : spectralSensitivity (parity 3) = 3 := spectralSensitivity_parity 3

-- The exact one-query algorithm `readBit` for `OR_1` satisfies the bounded-error hypothesis.
theorem abs_measureProb_readBit_sub_le (x : Fin 1 → Bool) :
    |measureProb (run readBit ψ₀ x 1) accept - bitVal ℝ (threshold 1 1 x)| ≤ 1 / 3 := by
  rw [measureProb_readBit_threshold]
  norm_num

example : spectralSensitivity (threshold 1 1) ≤ 36 * (1 : ℕ) :=
  spectralSensitivity_le_thirty_six_mul readBit norm_ψ₀ 1 accept abs_measureProb_readBit_sub_le

example : degree (threshold 1 1) ≤ 1296 * 1 ^ 2 :=
  degree_le_mul_sq readBit norm_ψ₀ 1 accept abs_measureProb_readBit_sub_le

example : DecisionTree.complexity (threshold 1 1) ≤ 20736 * 1 ^ 4 :=
  complexity_le_mul_pow_four readBit norm_ψ₀ 1 accept abs_measureProb_readBit_sub_le

-- `orSearch` computes `OR_N` with error `1/3` in `T = 2 · orRange N` queries, so
-- `D(OR_N) ≤ 20736 T⁴` and, since `deg(OR_N) = N`, `N ≤ 1296 T²`.
example (N : ℕ) (hN : 0 < N) :
    DecisionTree.complexity (threshold N 1) ≤ 20736 * (orRange N + orRange N) ^ 4 :=
  complexity_le_mul_pow_four (orSearch N) (norm_orSearchInit hN) _ (orAccept N)
    (abs_measureProb_run_orSearch_sub_le hN)

example (N : ℕ) (hN : 0 < N) : N ≤ 1296 * (orRange N + orRange N) ^ 2 :=
  degree_threshold_one_right.symm.trans_le
    (degree_le_mul_sq (orSearch N) (norm_orSearchInit hN) _ (orAccept N)
      (abs_measureProb_run_orSearch_sub_le hN))

end ComplexityTests.QuantumAdversary
