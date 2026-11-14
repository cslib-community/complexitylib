/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.Correctness
import CslibFrontierTests.Crypto.HQCPKE

/-! Checked clients for the ideal HQC full-noise DFR bridge. -/

public section

namespace CslibFrontierTests.HQCCorrectness

open Cslib Cslib.BitString Cslib.Crypto.HQC Cslib.Crypto.Protocols Cslib.Probability

example : weight (truncate HQCPKE.toyParams
    (pkeDecryptionNoise HQCPKE.toyParams HQCPKE.x HQCPKE.y HQCPKE.coins)) ≤
      weight (pkeDecryptionNoise HQCPKE.toyParams HQCPKE.x HQCPKE.y HQCPKE.coins) :=
  weight_truncate_le _ _

example :
    ExplicitCoinPKE.DeltaCorrect
      (toExplicitCoinPKE HQCPKE.toyParams HQCPKE.repetitionEncode HQCPKE.repetitionDecode)
      (pkeFullNoiseFailureProbability HQCPKE.toyParams) :=
  pkeDeltaCorrect_fullNoiseFailureProbability HQCPKE.toyParams HQCPKE.repetitionEncode
    HQCPKE.repetitionDecode HQCPKE.repetition_corrects

/-- A one-bit, positive-weight instance whose complete decryption noise always exceeds radius
zero. It checks that the source event and its probability are not vacuous. -/
abbrev failureParams : PKEParams where
  n := 1
  k := 1
  ell := 0
  omega := 1
  omegaR := 1
  omegaE := 1
  delta := 0
  ell_le_n := by decide
  omega_le_n := by decide
  omegaR_le_n := by decide
  omegaE_le_n := by decide

local instance : NeZero failureParams.codeLen := ⟨by decide⟩

def failureEncode (m : PKEMessage failureParams) : Codeword failureParams := m

def failureDecode (w : Codeword failureParams) : PKEMessage failureParams := w

theorem failureDecoder_corrects : DecoderCorrects failureParams failureEncode failureDecode := by
  unfold DecoderCorrects failureEncode failureDecode
  decide

def one : RingWord failureParams := ![true]

def failingCoins : PKECoins failureParams := ⟨one, one, one⟩

example : pkeFullNoiseFailure failureParams one one failingCoins := by
  change failureParams.delta < weight
    (pkeDecryptionNoise failureParams one one failingCoins)
  decide

private theorem failureExperiment_support_eq :
    (ProbComp.eval (pkeFullNoiseFailureExperiment failureParams)).support = {true} := by
  have hall : ∀ b ∈ (ProbComp.eval (pkeFullNoiseFailureExperiment failureParams)).support,
      b = true := by
    intro b hb
    obtain ⟨y, hy, x, hx, coins, hcoins, hb⟩ :=
      (mem_support_pkeFullNoiseFailureExperiment_iff failureParams).mp hb
    have hone : ∀ z : RingWord failureParams, weight z = 1 → z = one := by
      decide
    have hy' := hone y
      (weight_of_mem_support_sampleFixedWeight failureParams failureParams.omega_le_n hy)
    have hx' := hone x
      (weight_of_mem_support_sampleFixedWeight failureParams failureParams.omega_le_n hx)
    obtain ⟨hr2, he, hr1⟩ := pkeSampleCoins_support failureParams hcoins
    have hr2' := hone coins.r2 hr2
    have he' := hone coins.e he
    have hr1' := hone coins.r1 hr1
    have hcoins' : coins = failingCoins := by
      cases coins with
      | mk r2 e r1 =>
          change r2 = one at hr2'
          change e = one at he'
          change r1 = one at hr1'
          subst r2
          subst e
          subst r1
          rfl
    rw [hb]
    rw [hx', hy', hcoins']
    decide
  apply Set.Subset.antisymm
  · intro b hb
    exact Set.mem_singleton_iff.mpr (hall b hb)
  · intro b hb
    simp only [Set.mem_singleton_iff] at hb
    subst b
    obtain ⟨b, hb⟩ :=
      (ProbComp.eval (pkeFullNoiseFailureExperiment failureParams)).support_nonempty
    have hb' := hall b hb
    simpa only [hb'] using hb

example : pkeFullNoiseFailureProbability failureParams = 1 := by
  exact (pkeFullNoiseFailureProbability_eq_one_iff failureParams).2
    failureExperiment_support_eq

private theorem fullNoiseFailureMass_le_one (P : PKEParams) :
    pkeFullNoiseFailureMass P ≤ 1 := by
  rw [pkeFullNoiseFailureMass_eq_iterated_expect]
  refine (ProbComp.expect_mono fun _ => ?_).trans_eq (ProbComp.expect_const _ 1)
  refine (ProbComp.expect_mono fun _ => ?_).trans_eq (ProbComp.expect_const _ 1)
  refine (ProbComp.expect_mono fun _ => ?_).trans_eq (ProbComp.expect_const _ 1)
  refine (ProbComp.expect_mono fun _ => ?_).trans_eq (ProbComp.expect_const _ 1)
  refine (ProbComp.expect_mono fun _ => ?_).trans_eq (ProbComp.expect_const _ 1)
  split <;> simp only [le_refl, zero_le]

example :
    (toExplicitCoinPKE failureParams failureEncode failureDecode).DeltaCorrect 1 := by
  apply pkeDeltaCorrect_of_fullNoiseFailureProbability_le failureParams failureEncode failureDecode
    failureDecoder_corrects
  rw [pkeFullNoiseFailureProbability_eq_toReal_mass]
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp) (fullNoiseFailureMass_le_one failureParams)

end CslibFrontierTests.HQCCorrectness
