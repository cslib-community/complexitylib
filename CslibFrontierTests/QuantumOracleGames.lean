/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Game.Quantum
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontierTests.QuantumOracleUniform

/-! Resource budgets for a growing native family, and a conditional concrete-to-asymptotic client.
The concrete security premise is explicit; this test does not assert a protocol reduction. -/

namespace CslibFrontierTests.QuantumOracleGames

open Cslib Cslib.Quantum Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.QuantumOracleUniform
open scoped NNReal

-- These budgets are independent: more qubits or queries do not pay for a missing gate.
example : (phaseFamily.description 1 0).instructions.Within 4 ⟨4, 2, 2⟩ := by decide

example : ¬ (phaseFamily.description 1 0).instructions.Within 4 ⟨100, 1, 100⟩ := by decide

example : ¬ (phaseFamily.description 1 0).instructions.Within 4 ⟨100, 100, 1⟩ := by decide

-- A single native-computable schedule covers every input shorter than a polynomial cap.
example : ∃ B : ℕ → ℕ, ComputableInPolyTime B encUnary encUnary ∧ PolynomiallyBounded B ∧
    ∀ n ℓ, ℓ ≤ (n + 1) ^ 2 →
      (phaseFamily.description n ℓ).width + (phaseFamily.description n ℓ).instructions.length ≤
        B n :=
  phaseFamily.exists_computable_resource_bound (by fun_prop)

-- A concrete surface can depend differently on all three resources. The caller supplies the
-- actual game bound; polynomial budgets make this particular surface negligible.
example (game₁ game₂ : UniformOracleCircuitFamily → ℕ → Game)
    (h : Game.IndistinguishableWithin game₁ game₂
      (Game.WithinOracleCircuits fun n => (n + 1) ^ 2)
      (fun n r => ((r.queries ^ 2 + r.gates * r.qubits : ℕ) : ℝ≥0) / 2 ^ n)) :
    Game.Indistinguishable game₁ game₂ (fun _ => True) := by
  refine Game.Indistinguishable.of_uniformOracleCircuits (by fun_prop) h ?_
  intro qubits gates queries hqubits hgates hqueries
  simpa only [div_eq_mul_inv] using
    negligible_inv_two_pow.polynomiallyBounded_mul ((hqueries.pow 2).add (hgates.mul hqubits))

end CslibFrontierTests.QuantumOracleGames
