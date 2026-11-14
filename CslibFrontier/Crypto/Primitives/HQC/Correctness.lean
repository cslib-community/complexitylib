/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.PKE
import CslibFrontier.Languages.Probabilistic.Expect
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Probability.PMF.ToReal

/-!
# Ideal HQC decryption-failure correctness

This file bridges the ideal expanded HQC-PKE algebra to the `δ`-correctness interface used by the
Fujisaki--Okamoto transform. It follows [HQC2026], Definition 6.2.1 and Equations (11), (13), and
(14), §6.2.2, pp. 64--65.

The source bounds the probability that the complete word
`e' = x * r₂ - r₁ * y + e` has weight greater than `Δ`. HQC decryption sees only the retained
prefix of `e'`. We therefore use the source event as a conservative upper bound: restricting a bit
string cannot increase its Hamming weight. We do not formalize the source's stronger “if and only
if” sentence, which would require a concrete decoder theorem saying that every error beyond its
guaranteed radius fails.

This remains an ideal expanded-value result. It does not prove a numerical decryption-failure
bound, the concrete Reed--Muller/Reed--Solomon decoder, seed/XOF equivalence, or any security
claim.

## Main definitions

* `Cslib.Crypto.HQC.pkeFullNoiseFailure`: the source's full-word failure event.
* `Cslib.Crypto.HQC.pkeFullNoiseFailureExperiment`: the ideal Equation-(14) experiment.
* `Cslib.Crypto.HQC.pkeFullNoiseFailureProbability`: its real-valued probability.

## Main results

* `Cslib.Crypto.HQC.weight_truncate_le`: retained-prefix weight is at most full-word weight.
* `Cslib.Crypto.HQC.mem_support_pkeFullNoiseFailureExperiment_iff`: exact supported outcomes of
  the Equation-(14) experiment.
* `Cslib.Crypto.HQC.pkeFullNoiseFailureMass_eq_iterated_expect`: the source's five independent
  draws as an iterated event-mass expectation.
* `Cslib.Crypto.HQC.pkeMsgFailProb_le_fullNoiseFailProb`: every message's actual failure
  probability is bounded by the full-noise event for its generating witnesses.
* `Cslib.Crypto.HQC.pkeDeltaCorrect_fullNoiseFailureProbability`: ideal HQC-PKE is
  `pkeFullNoiseFailureProbability P`-correct.

## References

* [HQC specification, version 5.1][HQC2026], §6.2.2, pp. 64--65.
-/

public section

namespace Cslib.Crypto.HQC

open Matrix BitString Probability Cslib.Crypto.Protocols

/-- The source's complete decryption-noise failure event `ω(x*r₂ - r₁*y + e) > Δ`. -/
@[expose] def pkeFullNoiseFailure (P : PKEParams) (x y : RingWord P) (coins : PKECoins P) : Prop :=
  P.delta < weight (pkeDecryptionNoise P x y coins)

/-- The ideal expanded Equation-(14) experiment: sample `y`, then `x`, then `(r₂, e, r₁)`, and
test whether the complete decryption noise exceeds the decoder radius. -/
noncomputable def pkeFullNoiseFailureExperiment (P : PKEParams) : ProbComp Bool := do
  let y ← sampleFixedWeight P P.omega
  let x ← sampleFixedWeight P P.omega
  let coins ← pkeSampleCoins P
  return decide (P.delta < weight (pkeDecryptionNoise P x y coins))

/-- The real probability of the ideal Equation-(14) full-noise failure experiment. -/
noncomputable def pkeFullNoiseFailureProbability (P : PKEParams) : ℝ :=
  Pr[pkeFullNoiseFailureExperiment P]

/-- The same ideal full-noise failure probability as an iterated extended-nonnegative
expectation. This form exposes the source's key and encryption sampling layers. -/
noncomputable def pkeFullNoiseFailureMass (P : PKEParams) : ENNReal :=
  (sampleFixedWeight P P.omega).expect fun y =>
    (sampleFixedWeight P P.omega).expect fun x =>
      (ProbComp.eval (pkeSampleCoins P)).toOuterMeasure
        {coins | pkeFullNoiseFailure P x y coins}

/-- The Equation-(14) mass as the source's five independent draws, in order `y`, `x`, `r₂`, `e`,
then `r₁`. The final `0`/`1` score is the indicator of the full-noise failure event. -/
theorem pkeFullNoiseFailureMass_eq_iterated_expect (P : PKEParams) :
    pkeFullNoiseFailureMass P =
      (sampleFixedWeight P P.omega).expect fun y =>
        (sampleFixedWeight P P.omega).expect fun x =>
          (sampleFixedWeight P P.omegaR).expect fun r2 =>
            (sampleFixedWeight P P.omegaE).expect fun e =>
              (sampleFixedWeight P P.omegaR).expect fun r1 =>
                if P.delta < weight (pkeDecryptionNoise P x y ⟨r2, e, r1⟩) then 1 else 0 := by
  rw [pkeFullNoiseFailureMass]
  congr 1 with y
  congr 1 with x
  rw [← pkeSampleCoins_expect P (fun coins =>
    if P.delta < weight (pkeDecryptionNoise P x y coins) then 1 else 0)]
  simp [ProbComp.expect, PMF.toOuterMeasure_eq_tsum_mul_indicator, Set.indicator,
    pkeFullNoiseFailure]

/-- The Equation-(14) Boolean experiment has exactly the iterated full-noise failure mass. -/
theorem eval_pkeFullNoiseFailureExperiment_true (P : PKEParams) :
    ProbComp.eval (pkeFullNoiseFailureExperiment P) true = pkeFullNoiseFailureMass P := by
  classical
  simp [pkeFullNoiseFailureExperiment, pkeFullNoiseFailureMass, ProbComp.expect,
    PMF.toOuterMeasure_eq_tsum_mul_indicator, Set.indicator, pkeFullNoiseFailure]

/-- An outcome is supported by the Equation-(14) experiment exactly when it is the decision bit
for supported source samples `y`, `x`, and `(r₂, e, r₁)`. -/
theorem mem_support_pkeFullNoiseFailureExperiment_iff (P : PKEParams) {b : Bool} :
    b ∈ (ProbComp.eval (pkeFullNoiseFailureExperiment P)).support ↔
      ∃ y ∈ (ProbComp.eval (sampleFixedWeight P P.omega)).support,
        ∃ x ∈ (ProbComp.eval (sampleFixedWeight P P.omega)).support,
          ∃ coins ∈ (ProbComp.eval (pkeSampleCoins P)).support,
            b = decide (P.delta < weight (pkeDecryptionNoise P x y coins)) := by
  simp only [pkeFullNoiseFailureExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]

/-- The real Equation-(14) failure probability is one exactly when its Boolean experiment has
only `true` in its support. -/
theorem pkeFullNoiseFailureProbability_eq_one_iff (P : PKEParams) :
    pkeFullNoiseFailureProbability P = 1 ↔
      (ProbComp.eval (pkeFullNoiseFailureExperiment P)).support = {true} := by
  rw [pkeFullNoiseFailureProbability, ENNReal.toReal_eq_one_iff, PMF.apply_eq_one_iff]

/-- The real probability notation for Equation (14) is the real coercion of its iterated
full-noise mass. -/
theorem pkeFullNoiseFailureProbability_eq_toReal_mass (P : PKEParams) :
    pkeFullNoiseFailureProbability P = (pkeFullNoiseFailureMass P).toReal := by
  rw [pkeFullNoiseFailureProbability, ← eval_pkeFullNoiseFailureExperiment_true]

/-- Restricting a ring word to HQC's retained prefix cannot increase Hamming weight. -/
theorem weight_truncate_le (P : PKEParams) (z : RingWord P) :
    weight (truncate P z) ≤ weight z := by
  exact weight_comp_le z (Fin.castLEEmb _).injective

/-- A decryption failure for an honestly formed key and ciphertext implies that the complete
source noise exceeds the decoder radius. -/
theorem pkeFullNoiseFailure_of_decrypt_ne (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) (h x y : RingWord P)
    (m : PKEMessage P) (coins : PKECoins P)
    (hfail : pkeDecrypt P decode y
      (pkeEncrypt P encode (expandedPublicKey P h x y) m coins) ≠ m) :
    pkeFullNoiseFailure P x y coins := by
  by_contra hnoise
  apply hfail
  apply pkeDecrypt_encrypt_eq_of_weight_le P encode decode hcorrect h x y m coins
  exact (weight_truncate_le P _).trans (Nat.le_of_not_gt hnoise)

/-- The probability of the source full-noise event for fixed key-generation witnesses `x,y`. -/
noncomputable def pkeFullNoiseFailProb (P : PKEParams) (x y : RingWord P) : ℝ :=
  ((ProbComp.eval (pkeSampleCoins P)).toOuterMeasure
    {coins | pkeFullNoiseFailure P x y coins}).toReal

/-- The fixed-key full-noise probability as the source's three independent encryption draws, in
order `r₂`, `e`, then `r₁`. -/
theorem pkeFullNoiseFailProb_eq_iterated_expect (P : PKEParams) (x y : RingWord P) :
    pkeFullNoiseFailProb P x y =
      ((sampleFixedWeight P P.omegaR).expect fun r2 =>
        (sampleFixedWeight P P.omegaE).expect fun e =>
          (sampleFixedWeight P P.omegaR).expect fun r1 =>
            if P.delta < weight (pkeDecryptionNoise P x y ⟨r2, e, r1⟩) then 1 else 0).toReal := by
  rw [pkeFullNoiseFailProb]
  apply congrArg ENNReal.toReal
  rw [← pkeSampleCoins_expect P (fun coins =>
    if P.delta < weight (pkeDecryptionNoise P x y coins) then 1 else 0)]
  simp [ProbComp.expect, PMF.toOuterMeasure_eq_tsum_mul_indicator, Set.indicator,
    pkeFullNoiseFailure]

/-- For an honestly formed expanded key, every message's actual failure probability is at most
the source full-noise probability for its key-generation witnesses. -/
theorem pkeMsgFailProb_le_fullNoiseFailProb (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) (h x y : RingWord P) (m : PKEMessage P) :
    (toExplicitCoinPKE P encode decode).msgFailProb (expandedPublicKey P h x y) y m ≤
      pkeFullNoiseFailProb P x y := by
  rw [ExplicitCoinPKE.msgFailProb, pkeFullNoiseFailProb]
  apply PMF.toOuterMeasure_toReal_mono
  intro coins hfail
  apply pkeFullNoiseFailure_of_decrypt_ne P encode decode hcorrect h x y m coins
  intro hdecrypt
  apply hfail
  change some (pkeDecrypt P decode y
    (pkeEncrypt P encode (expandedPublicKey P h x y) m coins)) = some m
  rw [hdecrypt]

/-- For an honestly formed expanded key, the worst-message failure probability is bounded by the
same message-independent source noise event. -/
theorem pkeKeyPairMaxFailProb_le_fullNoiseFailProb (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) (h x y : RingWord P) :
    (toExplicitCoinPKE P encode decode).keyPairMaxFailProb (expandedPublicKey P h x y) y ≤
      pkeFullNoiseFailProb P x y := by
  rw [ExplicitCoinPKE.keyPairMaxFailProb, Finset.sup'_le_iff]
  intro m _
  exact pkeMsgFailProb_le_fullNoiseFailProb P encode decode hcorrect h x y m

/-- Averaging the worst-message failure probability over ideal key generation is bounded by the
ideal full-noise failure mass. This preserves Definition 6.2.1's expectation over keys. -/
theorem pkeKeyGen_expect_maxFail_le_fullNoiseMass (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) :
    (pkeKeyGen P).expect (fun keys => ENNReal.ofReal
      ((toExplicitCoinPKE P encode decode).keyPairMaxFailProb keys.1 keys.2)) ≤
        pkeFullNoiseFailureMass P := by
  rw [pkeKeyGen_expect]
  simp only [pkeFullNoiseFailureMass]
  apply ProbComp.expect_mono
  intro y
  apply ProbComp.expect_mono
  intro x
  calc
    (ProbComp.uniform (RingWord P)).expect (fun h => ENNReal.ofReal
        ((toExplicitCoinPKE P encode decode).keyPairMaxFailProb
          (expandedPublicKey P h x y) y)) ≤
        (ProbComp.uniform (RingWord P)).expect
          (fun _ => ENNReal.ofReal (pkeFullNoiseFailProb P x y)) := by
      apply ProbComp.expect_mono
      intro h
      exact ENNReal.ofReal_le_ofReal
        (pkeKeyPairMaxFailProb_le_fullNoiseFailProb P encode decode hcorrect h x y)
    _ = ENNReal.ofReal (pkeFullNoiseFailProb P x y) :=
      ProbComp.expect_const _ _
    _ = (ProbComp.eval (pkeSampleCoins P)).toOuterMeasure
          {coins | pkeFullNoiseFailure P x y coins} := by
      rw [pkeFullNoiseFailProb, ENNReal.ofReal_toReal
        (PMF.toOuterMeasure_ne_top _ _)]

/-- The ideal expanded HQC-PKE core is `δ`-correct for the source's full-noise Equation-(14)
failure probability. The left side retains Definition 6.2.1's expectation over generated keys
of the worst failure probability over messages. -/
theorem pkeDeltaCorrect_fullNoiseFailureProbability (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) :
    (toExplicitCoinPKE P encode decode).DeltaCorrect (pkeFullNoiseFailureProbability P) := by
  unfold ExplicitCoinPKE.DeltaCorrect
  change ((pkeKeyGen P).expect (fun keys => ENNReal.ofReal
    ((toExplicitCoinPKE P encode decode).keyPairMaxFailProb keys.1 keys.2))).toReal ≤ _
  rw [pkeFullNoiseFailureProbability_eq_toReal_mass]
  apply ENNReal.toReal_mono
  · rw [← eval_pkeFullNoiseFailureExperiment_true]
    exact PMF.apply_ne_top _ _
  · exact pkeKeyGen_expect_maxFail_le_fullNoiseMass P encode decode hcorrect

/-- Any real upper bound on the source's full-noise Equation-(14) probability is a valid
`δ`-correctness bound for the ideal expanded HQC-PKE core. -/
theorem pkeDeltaCorrect_of_fullNoiseFailureProbability_le (P : PKEParams)
    (encode : PKEMessage P → Codeword P) (decode : Codeword P → PKEMessage P)
    (hcorrect : DecoderCorrects P encode decode) {δ : ℝ}
    (hδ : pkeFullNoiseFailureProbability P ≤ δ) :
    (toExplicitCoinPKE P encode decode).DeltaCorrect δ :=
  (pkeDeltaCorrect_fullNoiseFailureProbability P encode decode hcorrect).mono hδ

end Cslib.Crypto.HQC
