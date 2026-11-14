/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Quantum.Mixture
public import CslibFrontier.Crypto.Computational.HQC.DQCSD
public import CslibFrontierTests.Crypto.NativeQuantumIndistinguishability

/-! Ordinary-module clients of native mixture closure: exact unequal errors, cancellation,
length boundaries and the landed fixed-parity HQC assumption interfaces. -/

public section

open Cslib Cslib.Crypto Cslib.Crypto.NativeQuantum Cslib.Probability Cslib.Quantum
open CslibFrontierTests.NativeQuantumIndistinguishability
open scoped NNReal

namespace CslibFrontierTests.NativeQuantumMixture

noncomputable abbrev bitEnsemble (b : Bool) : ℕ → PMF (List Bool) :=
  if b then trueEnsemble else falseEnsemble

private theorem distinguishingGame_bit (b : Bool) (n : ℕ) :
    distinguishingGame (bitEnsemble b) firstBitFamily n = PMF.pure b := by
  cases b <;> simp [bitEnsemble, distinguishingGame_true, distinguishingGame_false]

-- One branch has error one and the other has error zero. The same resource budget is passed
-- unchanged to the branch assumptions.
example : IndistinguishableWithin
    (fun n => (PMF.uniformOfFintype Bool).bind (fun _ => trueEnsemble n))
    (fun n => (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble b n))
    (fun _ => 1) (fun _ _ => 1 / 2) := by
  have h (b : Bool) : IndistinguishableWithin trueEnsemble (bitEnsemble b)
      (fun _ => 1) (fun _ _ => if b then 0 else 1) := by
    intro n budget family _
    cases b
    · exact Game.advantage_le_one _ _
    · exact (Game.advantage_self _).le
  simpa using IndistinguishableWithin.bind_uniformBool h

-- An actual uniform native circuit attains the averaged bound at every security parameter.
theorem averaged_bound_attained (n : ℕ) : Game.advantage
    (distinguishingGame
      (fun n => (PMF.uniformOfFintype Bool).bind (fun _ => trueEnsemble n)) firstBitFamily n)
    (distinguishingGame
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble b n)) firstBitFamily n)
      = 1 / 2 := by
  simp only [distinguishingGame, PMF.bind_bind]
  change Game.advantage
    ((PMF.uniformOfFintype Bool).bind fun _ => distinguishingGame trueEnsemble firstBitFamily n)
    ((PMF.uniformOfFintype Bool).bind fun b =>
      distinguishingGame (bitEnsemble b) firstBitFamily n) = _
  simp only [distinguishingGame_true, distinguishingGame_bit, PMF.bind_const, PMF.bind_pure]
  rw [Game.advantage_pure_true_left]
  norm_num [Game.failProbability, PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat]

-- Opposite branch gaps cancel: the mixed ensembles are identical even though each branch
-- is perfectly distinguishable by firstBitFamily.
theorem mixture_complement_eq (n : ℕ) :
    (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble b n) =
      (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble (!b) n) := by
  ext x
  simp [PMF.bind_apply, PMF.uniformOfFintype_apply, add_comm]

example (n : ℕ) : Game.advantage
    (distinguishingGame
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble b n)) firstBitFamily n)
    (distinguishingGame
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble (!b) n)) firstBitFamily n)
      = 0 := by
  have h := funext mixture_complement_eq
  rw [h, Game.advantage_self]

example (b : Bool) (n : ℕ) :
    Game.advantage (distinguishingGame (bitEnsemble b) firstBitFamily n)
      (distinguishingGame (bitEnsemble (!b)) firstBitFamily n) = 1 := by
  cases b
  · simpa only [bitEnsemble, Bool.false_eq_true, ↓reduceIte, Bool.not_false] using
      (Game.advantage_comm _ _).trans (advantage_true_false n)
  · exact advantage_true_false n

-- The same first-bit circuit has three gates and no oracle queries, and fits the common cap.
example (n : ℕ) : Game.WithinOracleCircuits (fun _ => 1) n ⟨2 * n + 3, 3, 0⟩
    firstBitFamily := by
  intro ℓ hℓ
  change ℓ ≤ 1 at hℓ
  refine ⟨by dsimp [firstBitFamily, firstBitDescription]; omega, ?_, ?_⟩ <;>
    simp [GateCode.swapCodes, OracleCircuit.gateCount,
      OracleCircuit.queryCount, OracleGateCode.isQuery]

example : SupportsLength
    (fun n => (PMF.uniformOfFintype Bool).bind (fun b => bitEnsemble b n)) (fun _ => 1) :=
  SupportsLength.bind (fun b => by
    cases b
    · exact supportsLength_falseEnsemble
    · exact supportsLength_trueEnsemble) _

example : SupportsLength
    (fun _ => (PMF.uniformOfFintype Bool).bind (fun _ => PMF.pure ([] : List Bool)))
    (fun _ => 0) :=
  SupportsLength.bind (fun _ => by simp [SupportsLength, SupportsLengthAt]) _

example (n : ℕ) : ¬ SupportsLengthAt
    (fun _ => (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure [b])) (fun _ => 0) n := by
  intro h
  have hb := (supportsLengthAt_bind_iff _ _ _ _).mp h false
    (PMF.mem_support_uniformOfFintype false)
  simp [SupportsLengthAt] at hb

-- Both source-named assumptions use the same native model and their exact native encodings.
example (params : HQC.DQCSDParameters)
    (ε : Bool → ℕ → OracleCircuit.Resources → ℝ≥0)
    (h : ∀ b, HQC.NativeQuantumTwoDQCSDPWithin params (fun _ => b) (ε b)) :
    IndistinguishableWithin
      (fun n => (PMF.uniformOfFintype Bool).bind
        (fun b => HQC.twoRealEnsemble params (fun _ => b) n))
      (fun n => (PMF.uniformOfFintype Bool).bind
        (fun b => HQC.twoUniformEnsemble params (fun _ => b) n))
      (HQC.twoWordLength params) (fun n budget => (ε false n budget + ε true n budget) / 2) :=
  IndistinguishableWithin.bind_uniformBool fun b =>
    (HQC.nativeQuantumTwoDQCSDPWithin_iff_indistinguishableWithin _ _ _).mp (h b)

example (params : HQC.DQCSDParameters)
    (h : ∀ b, HQC.NativeQuantumTwoDQCSDP params (fun _ => b)) :
    ComputationallyIndistinguishable
      (fun n => (PMF.uniformOfFintype Bool).bind
        (fun b => HQC.twoRealEnsemble params (fun _ => b) n))
      (fun n => (PMF.uniformOfFintype Bool).bind
        (fun b => HQC.twoUniformEnsemble params (fun _ => b) n)) :=
  ComputationallyIndistinguishable.bind_uniformBool fun b =>
    (HQC.nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable _ _).mp (h b)

-- The second parity comes from the public-key weight schedule, not from the three-block
-- secret-weight schedule. Keeping it independent prevents accidentally identifying the two.
example (params : HQC.DQCSDTruncatedParameters) (keyWeight : ℕ → ℕ)
    (ε : Bool → ℕ → OracleCircuit.Resources → ℝ≥0)
    (h : ∀ b, HQC.NativeQuantumThreeDQCSDPTWithin params (fun _ => b)
      (fun n => HQC.syndromeParity (keyWeight n) b) (ε b)) :
    IndistinguishableWithin
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => HQC.threeRealEnsemble params
        (fun _ => b) (fun n => HQC.syndromeParity (keyWeight n) b) n))
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => HQC.threeUniformEnsemble params
        (fun _ => b) (fun n => HQC.syndromeParity (keyWeight n) b) n))
      (HQC.threeWordLength params) (fun n budget => (ε false n budget + ε true n budget) / 2) :=
  IndistinguishableWithin.bind_uniformBool fun b =>
    (HQC.nativeQuantumThreeDQCSDPTWithin_iff_indistinguishableWithin _ _ _ _).mp (h b)

example (params : HQC.DQCSDTruncatedParameters) (keyWeight : ℕ → ℕ)
    (h : ∀ b, HQC.NativeQuantumThreeDQCSDPT params (fun _ => b)
      (fun n => HQC.syndromeParity (keyWeight n) b)) :
    ComputationallyIndistinguishable
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => HQC.threeRealEnsemble params
        (fun _ => b) (fun n => HQC.syndromeParity (keyWeight n) b) n))
      (fun n => (PMF.uniformOfFintype Bool).bind (fun b => HQC.threeUniformEnsemble params
        (fun _ => b) (fun n => HQC.syndromeParity (keyWeight n) b) n)) :=
  ComputationallyIndistinguishable.bind_uniformBool fun b =>
    (HQC.nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable _ _ _).mp (h b)

end CslibFrontierTests.NativeQuantumMixture
