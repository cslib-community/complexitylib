/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.HQC.DQCSD
import CslibFrontier.Probability.PMF.Support
import CslibFrontierTests.Crypto.NativeQuantumIndistinguishability
import Mathlib.Data.Fin.VecNotation

/-! Concrete encodings, source ensembles, and native quantum bridges for HQC DQCSD. -/

public section

namespace CslibFrontierTests.HQCDQCSD

open Cslib Cslib.Crypto Cslib.Crypto.HQC Cslib.Crypto.NativeQuantum Cslib.Quantum
open CslibFrontierTests.NativeQuantumIndistinguishability
open scoped NNReal

/-- A nonvacuous one-bit 2-DQCSD-P family. -/
private def unitParameters : DQCSDParameters where
  blockLength := fun _ => 1
  weight := fun _ => 1
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega

/-- A nonvacuous two-bit family retaining one coordinate in 3-DQCSD-PT. -/
private def truncatedParameters : DQCSDTruncatedParameters where
  blockLength := fun _ => 2
  weight := fun _ => 1
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega
  truncation := fun _ => 1
  truncation_pos := by intro; omega
  truncation_lt := by intro; omega

private def twoSample : SyndromeSample 2 :=
  ⟨![true, false], ![false, true]⟩

private def threeSample : TruncatedSyndromeSample 2 1 :=
  ⟨![true, false], ![false, true], ![true, true], ![false]⟩

-- Both serializers preserve the source tuple order and have no delimiter or variable-width field.
example : twoSample.toWord = [true, false, false, true] := by decide

example : threeSample.toWord = [true, false, false, true, true, true, false] := by decide

example (κ : ℕ) : twoWordLength unitParameters κ = 2 := by rfl

example (κ : ℕ) : threeWordLength truncatedParameters κ = 7 := by rfl

-- The four source ensembles meet the exact fixed-width contracts used by the hardness predicates.
example : SupportsLength (twoRealEnsemble unitParameters (fun _ => true)) (fun _ => 2) := by
  convert supportsLength_twoRealEnsemble unitParameters (fun _ => true) using 1
  funext κ
  rfl

example : SupportsLength (twoUniformEnsemble unitParameters (fun _ => true)) (fun _ => 2) := by
  convert supportsLength_twoUniformEnsemble unitParameters (fun _ => true) using 1
  funext κ
  rfl

example : SupportsLength
    (threeRealEnsemble truncatedParameters (fun _ => true) (fun _ => false)) (fun _ => 7) := by
  convert supportsLength_threeRealEnsemble
    truncatedParameters (fun _ => true) (fun _ => false) using 1
  funext κ
  rfl

example : SupportsLength
    (threeUniformEnsemble truncatedParameters (fun _ => true) (fun _ => false)) (fun _ => 7) := by
  convert supportsLength_threeUniformEnsemble
    truncatedParameters (fun _ => true) (fun _ => false) using 1
  funext κ
  rfl

private theorem test_twoSample_eq_true (κ : ℕ) (sample : SyndromeSample 1)
    (hpublic : parity 1 sample.publicBlock = true) :
    test firstBitFamily κ sample.toWord = PMF.pure true := by
  have hbit : sample.publicBlock 0 = true := by
    simpa [parity, parityOn_eq_sum, Fin.sum_univ_succ] using hpublic
  have hword : sample.toWord = true :: [sample.value 0] := by
    rw [SyndromeSample.toWord, List.ofFn_fin_append]
    simp [hbit]
  rw [hword, test_eq,
    show (fun _ : Fin 0 => false) = Fin.elim0 from Subsingleton.elim _ _,
    output_firstBitFamily, PMF.pure_map]
  rfl

private theorem distinguishingGame_twoReal_unit (κ : ℕ) :
    distinguishingGame (twoRealEnsemble unitParameters (fun _ => true)) firstBitFamily κ =
      PMF.pure true := by
  rw [distinguishingGame_eq_bind, twoRealEnsemble, PMF.bind_map]
  apply Probability.PMF.bind_eq_pure_of_forall_mem_support
  intro sample hsample
  apply test_twoSample_eq_true
  exact (parity_of_mem_support_realSyndromeLaw (unitParameters.weight_le κ) true hsample).1

private theorem distinguishingGame_twoUniform_unit (κ : ℕ) :
    distinguishingGame (twoUniformEnsemble unitParameters (fun _ => true)) firstBitFamily κ =
      PMF.pure true := by
  rw [distinguishingGame_eq_bind, twoUniformEnsemble, PMF.bind_map]
  apply Probability.PMF.bind_eq_pure_of_forall_mem_support
  intro sample hsample
  apply test_twoSample_eq_true
  simp only [uniformSyndromeLaw, Cslib.Probability.PMF.monad_bind_eq_bind,
    Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsample
  obtain ⟨publicBlock, hpublic, value, _, rfl⟩ := hsample
  exact (BitString.mem_support_uniformParity true publicBlock).mp hpublic

-- The generic native game consumes the exact encoded source words. This deliberately simple
-- first-bit family sees zero gap because both source laws preserve the public parity constraint.
example (κ : ℕ) :
    Game.advantage
      (distinguishingGame (twoRealEnsemble unitParameters (fun _ => true)) firstBitFamily κ)
      (distinguishingGame (twoUniformEnsemble unitParameters (fun _ => true)) firstBitFamily κ) =
        0 := by
  rw [distinguishingGame_twoReal_unit, distinguishingGame_twoUniform_unit]
  exact Game.advantage_self _

-- Concrete bounds for the instantiated source distributions pass through the source-specific
-- bridge. The assumptions here are intentionally not asserted by the test.
example
    (h : NativeQuantumTwoDQCSDPWithin unitParameters (fun _ => true) (fun _ _ => 0)) :
    NativeQuantumTwoDQCSDP unitParameters (fun _ => true) := by
  apply NativeQuantumTwoDQCSDP.of_within h
  · change PolynomiallyBounded fun _ => 1
    fun_prop
  · fun_prop

example
    (h : NativeQuantumThreeDQCSDPTWithin truncatedParameters
      (fun _ => true) (fun _ => false) (fun _ _ => 0)) :
    NativeQuantumThreeDQCSDPT truncatedParameters (fun _ => true) (fun _ => false) := by
  apply NativeQuantumThreeDQCSDPT.of_within h
  · change PolynomiallyBounded fun _ => 2
    fun_prop
  · fun_prop

/-! ### Ordinary-module use through the shared native quantum interfaces -/

theorem twoWithin_sharedInterface (p : DQCSDParameters) (primitive : ℕ → Bool)
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumTwoDQCSDPWithin p primitive ε) :
    NativeQuantum.IndistinguishableWithin
      (twoRealEnsemble p primitive)
      (twoUniformEnsemble p primitive)
      (twoWordLength p) ε :=
  (nativeQuantumTwoDQCSDPWithin_iff_indistinguishableWithin p primitive ε).mp h

theorem twoAsymptotic_sharedInterface (p : DQCSDParameters) (primitive : ℕ → Bool)
    (h : NativeQuantumTwoDQCSDP p primitive) :
    NativeQuantum.ComputationallyIndistinguishable
      (twoRealEnsemble p primitive)
      (twoUniformEnsemble p primitive) :=
  (nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable p primitive).mp h

theorem threeWithin_sharedInterface (p : DQCSDTruncatedParameters)
    (primitive prime : ℕ → Bool) {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumThreeDQCSDPTWithin p primitive prime ε) :
    NativeQuantum.IndistinguishableWithin
      (threeRealEnsemble p primitive prime)
      (threeUniformEnsemble p primitive prime)
      (threeWordLength p) ε :=
  (nativeQuantumThreeDQCSDPTWithin_iff_indistinguishableWithin
    p primitive prime ε).mp h

theorem threeAsymptotic_sharedInterface (p : DQCSDTruncatedParameters)
    (primitive prime : ℕ → Bool) (h : NativeQuantumThreeDQCSDPT p primitive prime) :
    NativeQuantum.ComputationallyIndistinguishable
      (threeRealEnsemble p primitive prime)
      (threeUniformEnsemble p primitive prime) :=
  (nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable
    p primitive prime).mp h

end CslibFrontierTests.HQCDQCSD
