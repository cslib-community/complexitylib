/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Quantum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! A growing native circuit reads the first challenge bit through the shared ensemble game. -/

public section

namespace CslibFrontierTests.NativeQuantumIndistinguishability

open Cslib Cslib.Crypto Cslib.Crypto.NativeQuantum Cslib.Quantum Turing.MultiTapeTM

/-- Swap the first challenge bit into the measured output wire. An extra zero qubit makes the
description valid even for the empty challenge. -/
abbrev firstBitDescription (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + 1
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := 1
  instructions := ((GateCode.swapCodes (2 * n + 1)).map fun g => (false, g)).map
    OracleGateCode.gate

private theorem polyTime_firstBitDescription : ComputableInPolyTime
    (fun s : OracleInputSize =>
      firstBitDescription s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [firstBitDescription, GateCode.swapCodes, List.map]
  fun_prop

private theorem wellFormed_firstBitDescription (n ℓ : ℕ) :
    (firstBitDescription n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨by dsimp only [firstBitDescription]; omega,
    by dsimp only [firstBitDescription]; omega,
    by dsimp only [firstBitDescription]; omega, ?_⟩
  intro instruction hinstruction
  simp only [List.mem_map] at hinstruction
  obtain ⟨phaseCode, hphaseCode, rfl⟩ := hinstruction
  obtain ⟨code, hcode, rfl⟩ := hphaseCode
  exact (GateCode.isClassical_swapCodes (N := 2 * n + 1 + ℓ + 1)
    (by omega) (by omega) code hcode).2

/-- One native generator handles every parameter and every challenge length. -/
abbrev firstBitFamily : UniformOracleCircuitFamily :=
  ⟨firstBitDescription, by exact polyTime_firstBitDescription,
    by exact wellFormed_firstBitDescription⟩

private theorem toCircuit_firstBitDescription (n ℓ : ℕ)
    (H : (Fin 0 → Bool) → Fin 0 → Bool) :
    OracleCircuit.toCircuit (2 * n + 1 + ℓ + 1) H
        (firstBitDescription n ℓ).instructions =
      Circuit.ofCodes (2 * n + 1 + ℓ + 1) (GateCode.swapCodes (2 * n + 1)) := by
  rw [OracleCircuit.toCircuit_map_gate, Circuit.ofPhaseCodes_map]

private theorem classical_firstBitDescription (n ℓ : ℕ) :
    GateCode.IsClassical (2 * n + 1 + ℓ + 1) (GateCode.swapCodes (2 * n + 1)) :=
  GateCode.isClassical_swapCodes (by omega) (by omega)

/-- The native family consumes the complete word and returns its first bit. -/
theorem output_firstBitFamily (n : ℕ) (b : Bool) (rest : List Bool)
    (H : (Fin 0 → Bool) → Fin 0 → Bool) :
    firstBitFamily.output n (b :: rest) H (ket Fin.elim0) (norm_ket _) = PMF.pure [b] := by
  rw [UniformOracleCircuitFamily.output_eq]
  have hrun : firstBitFamily.run n (b :: rest) H (ket Fin.elim0) =
      ket (GateCode.classicalRun (GateCode.swapCodes (2 * n + 1))
        (inputState (2 * n + 1 + (b :: rest).length + 1)
          (encPair encUnary encBits (n, b :: rest)))) := by
    rw [UniformOracleCircuitFamily.run_apply,
      toCircuit_firstBitDescription, UniformOracleCircuitFamily.initialState_ket]
    simp only [List.ofFn_zero, List.append_nil]
    exact Circuit.eval_ofCodes_ket
      (classical_firstBitDescription n (b :: rest).length) _
  simp only [hrun, measureOut_ket]
  apply congrArg PMF.pure
  change [GateCode.classicalRun (GateCode.swapCodes (2 * n + 1)) _ ⟨0, by omega⟩] = [b]
  apply congrArg List.singleton
  let y := GateCode.classicalRun (GateCode.swapCodes (2 * n + 1))
    (inputState (2 * n + 1 + (b :: rest).length + 1)
      (encPair encUnary encBits (n, b :: rest)))
  change y ⟨0, by omega⟩ = b
  rw [← readBit_of_lt y (by omega), GateCode.readBit_classicalRun_swapCodes (by omega) (by omega)]
  rw [readBit_inputState (by simp)]
  simp [encPair_apply, encUnary_apply, encBits_apply]

/-- Certain first bit `true`. -/
noncomputable def trueEnsemble (_ : ℕ) : PMF (List Bool) :=
  PMF.pure [true]

/-- Certain first bit `false`. -/
noncomputable def falseEnsemble (_ : ℕ) : PMF (List Bool) :=
  PMF.pure [false]

theorem supportsLength_trueEnsemble : SupportsLength trueEnsemble (fun _ => 1) := by
  simp [SupportsLength, SupportsLengthAt, trueEnsemble]

theorem supportsLength_falseEnsemble : SupportsLength falseEnsemble (fun _ => 1) := by
  simp [SupportsLength, SupportsLengthAt, falseEnsemble]

theorem distinguishingGame_true (n : ℕ) :
    distinguishingGame trueEnsemble firstBitFamily n = PMF.pure true := by
  rw [distinguishingGame_eq_bind, trueEnsemble, PMF.pure_bind, test_eq,
    show (fun _ : Fin 0 => false) = Fin.elim0 from Subsingleton.elim _ _,
    output_firstBitFamily, PMF.pure_map]
  rfl

theorem distinguishingGame_false (n : ℕ) :
    distinguishingGame falseEnsemble firstBitFamily n = PMF.pure false := by
  rw [distinguishingGame_eq_bind, falseEnsemble, PMF.pure_bind, test_eq,
    show (fun _ : Fin 0 => false) = Fin.elim0 from Subsingleton.elim _ _,
    output_firstBitFamily, PMF.pure_map]
  rfl

/-- The generic native ensemble game exposes an exact gap on this deliberately easy pair. -/
theorem advantage_true_false (n : ℕ) :
    Game.advantage (distinguishingGame trueEnsemble firstBitFamily n)
      (distinguishingGame falseEnsemble firstBitFamily n) = 1 := by
  rw [distinguishingGame_true, distinguishingGame_false, Game.advantage_pure_true_left]
  simp [Game.failProbability, PMF.pure_apply]

private theorem trueEnsemble_within :
    IndistinguishableWithin trueEnsemble trueEnsemble (fun _ => 1) (fun _ _ => 0) := by
  intro n budget family _
  exact (Game.advantage_self (distinguishingGame trueEnsemble family n)).le

-- The resource bridge composes with a concrete zero bound and the checked support-length proof.
example : ComputationallyIndistinguishable trueEnsemble trueEnsemble :=
  ComputationallyIndistinguishable.of_within trueEnsemble_within
    supportsLength_trueEnsemble supportsLength_trueEnsemble (by fun_prop) (by fun_prop)

end CslibFrontierTests.NativeQuantumIndistinguishability
