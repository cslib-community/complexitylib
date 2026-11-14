/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Game.Quantum
public import CslibFrontier.Crypto.Negligible.Dyadic
public import CslibFrontierTests.QuantumOracleUniform

/-! Resource budgets for a growing native family, and a conditional concrete-to-asymptotic client.
The concrete security premise is explicit; this test does not assert a protocol reduction. -/

public section

namespace CslibFrontierTests.QuantumOracleGames

open Cslib Cslib.Quantum Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.QuantumOracleUniform
open scoped NNReal

-- These budgets are independent: more qubits, queries or description bits do not pay for a
-- missing gate.
example : (phaseFamily.description 1 0).instructions.Within 4
    (encOracleCircuitDescription (phaseFamily.description 1 0)).length
    ⟨4, 2, 2, (encOracleCircuitDescription (phaseFamily.description 1 0)).length⟩ := by decide

example : ¬ (phaseFamily.description 1 0).instructions.Within 4
    (encOracleCircuitDescription (phaseFamily.description 1 0)).length
    ⟨100, 1, 100, 1000⟩ := by decide

example : ¬ (phaseFamily.description 1 0).instructions.Within 4
    (encOracleCircuitDescription (phaseFamily.description 1 0)).length
    ⟨100, 100, 1, 1000⟩ := by decide

def shortDescription : OracleCircuitDescription :=
  ⟨2, 0, 0, 0, 0, []⟩

def longDescription : OracleCircuitDescription :=
  ⟨2, 1, 0, 0, 0, []⟩

-- Equal legacy resources do not imply equal encodings: register metadata is charged exactly.
example : shortDescription.WellFormed ⟨0, 0⟩ ∧ longDescription.WellFormed ⟨0, 0⟩ := by
  constructor
  · constructor <;> simp [shortDescription]
  · constructor <;> simp [longDescription]

example : shortDescription.width = longDescription.width ∧
    shortDescription.instructions.gateCount = longDescription.instructions.gateCount ∧
    shortDescription.instructions.queryCount = longDescription.instructions.queryCount := by
  decide

example : (encOracleCircuitDescription shortDescription).length <
    (encOracleCircuitDescription longDescription).length := by decide

example : shortDescription.instructions.Within shortDescription.width
    (encOracleCircuitDescription shortDescription).length
    ⟨2, 0, 0, (encOracleCircuitDescription shortDescription).length⟩ := by decide

example : ¬longDescription.instructions.Within longDescription.width
    (encOracleCircuitDescription longDescription).length
    ⟨2, 0, 0, (encOracleCircuitDescription shortDescription).length⟩ := by decide

-- A single native-computable schedule covers every input shorter than a polynomial cap.
example : ∃ B : ℕ → ℕ, ComputableInPolyTime B encUnary encUnary ∧ PolynomiallyBounded B ∧
    ∀ n ℓ, ℓ ≤ (n + 1) ^ 2 →
      (phaseFamily.description n ℓ).width + (phaseFamily.description n ℓ).instructions.length ≤
        B n :=
  let ⟨B, hB, hp, hdesc⟩ := phaseFamily.exists_computable_resource_bound (by fun_prop)
  ⟨B, hB, hp, fun n ℓ hℓ =>
    (phaseFamily.description n ℓ).width_add_length_le_encoding_length.trans (hdesc n ℓ hℓ)⟩

-- A concrete surface can depend differently on all four resources. The caller supplies the
-- actual game bound; polynomial budgets make this particular surface negligible.
example (game₁ game₂ : UniformOracleCircuitFamily → ℕ → Game)
    (h : Game.IndistinguishableWithin game₁ game₂
      (Game.WithinOracleCircuits fun n => (n + 1) ^ 2)
      (fun n r => ((r.queries ^ 2 + r.gates * r.qubits + r.descriptionBits : ℕ) : ℝ≥0) /
        2 ^ n)) :
    Game.Indistinguishable game₁ game₂ (fun _ => True) := by
  refine Game.Indistinguishable.of_uniformOracleCircuits (by fun_prop) h ?_
  intro qubits gates queries descriptionBits hqubits hgates hqueries hdescriptionBits
  simpa only [div_eq_mul_inv] using
    negligible_inv_two_pow.polynomiallyBounded_mul
      (((hqueries.pow 2).add (hgates.mul hqubits)).add hdescriptionBits)

end CslibFrontierTests.QuantumOracleGames
