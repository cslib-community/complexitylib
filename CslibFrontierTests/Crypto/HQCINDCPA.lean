/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.HQC.INDCPAClassical
import Mathlib.Data.Fin.VecNotation

/-! Checked key-dependent-message clients for the ideal and native-machine HQC-PKE reductions. -/

public section

namespace CslibFrontierTests.HQCINDCPA

open Cslib Cslib.BitString Cslib.Crypto Cslib.Crypto.HQC Cslib.Probability

/-- A positive toy instance with proper truncation and the source equality `ωᵣ = ωₑ`. -/
abbrev toyParams : PKEParams where
  n := 2
  k := 1
  ell := 1
  omega := 1
  omegaR := 1
  omegaE := 1
  delta := 1
  ell_le_n := by decide
  omega_le_n := by decide
  omegaR_le_n := by decide
  omegaE_le_n := by decide

local instance : NeZero toyParams.n := ⟨by decide⟩
local instance : NeZero toyParams.codeLen := ⟨by decide⟩

/-- At this toy length the message and retained codeword are both one bit. -/
def encode (message : PKEMessage toyParams) : Codeword toyParams := message

/-- A genuine two-stage client whose two challenge messages and saved state depend on the public
key. The second stage combines that state with the retained ciphertext bit. -/
noncomputable def keyDependentAdversary :
    TwoStage (PKEPublicKey toyParams) (MessagePair (PKEMessage toyParams))
      (PKECiphertext toyParams) Bool Bool where
  choose pk := pure
    (⟨(fun _ => parity toyParams.n pk.h), (fun _ => parity toyParams.n pk.s)⟩,
      parity toyParams.n pk.h)
  guess state ciphertext := pure (state ^^ ciphertext.v 0)

/-- A concrete public key on which the adversary chooses distinct key-dependent messages. -/
def distinctMessageKey : PKEPublicKey toyParams :=
  ⟨![true, false], ![false, false]⟩

/-- The actual message pair selected by the first adversary stage on `distinctMessageKey`. -/
def distinctMessages : MessagePair (PKEMessage toyParams) :=
  ⟨(fun _ => parity toyParams.n distinctMessageKey.h),
    (fun _ => parity toyParams.n distinctMessageKey.s)⟩

example : distinctMessages.msg₀ ≠ distinctMessages.msg₁ := by decide

example : ProbComp.eval (indCpaGame toyParams encode keyDependentAdversary) =
    twoRealGame toyParams encode keyDependentAdversary :=
  eval_indCpaGame_eq_twoRealGame toyParams encode keyDependentAdversary

example : twoUniformGame toyParams encode keyDependentAdversary =
    threeRealGame toyParams encode keyDependentAdversary :=
  twoUniformGame_eq_threeRealGame toyParams encode keyDependentAdversary rfl

example : threeUniformGame toyParams encode keyDependentAdversary =
    PMF.uniformOfFintype Bool :=
  threeUniformGame_eq_uniform toyParams encode keyDependentAdversary

example : indCpaAdvantage toyParams encode keyDependentAdversary ≤
    twoDQCSDAdvantage toyParams encode keyDependentAdversary +
      threeDQCSDAdvantage toyParams encode keyDependentAdversary :=
  indCpaAdvantage_le toyParams encode keyDependentAdversary rfl

/-! The machine layer uses transparent expanded-value encodings, not production serialization. -/

example (pk : PKEPublicKey toyParams) : (encPKEPublicKey toyParams pk).length = 7 := by
  rw [length_encPKEPublicKey]
  decide

example (coins : PKECoins toyParams) : (encPKECoins toyParams coins).length = 12 := by
  rw [length_encPKECoins]
  decide

example (ciphertext : PKECiphertext toyParams) :
    (encPKECiphertext toyParams ciphertext).length = 6 := by
  rw [length_encPKECiphertext]
  decide

example (sample : SyndromeSample toyParams.n) :
    (encSyndromeSample toyParams.n sample).length = 7 := by
  rw [length_encSyndromeSample]
  decide

example (sample : TruncatedSyndromeSample toyParams.n toyParams.codeLen) :
    (encTruncatedSyndromeSample toyParams.n toyParams.codeLen sample).length = 21 := by
  rw [length_encTruncatedSyndromeSample]
  decide

example (left right : PKEPublicKey toyParams)
    (h : encPKEPublicKey toyParams left = encPKEPublicKey toyParams right) : left = right :=
  (encPKEPublicKey toyParams).injective h

example (left right : TruncatedSyndromeSample toyParams.n toyParams.codeLen)
    (h : encTruncatedSyndromeSample toyParams.n toyParams.codeLen left =
      encTruncatedSyndromeSample toyParams.n toyParams.codeLen right) : left = right :=
  (encTruncatedSyndromeSample toyParams.n toyParams.codeLen).injective h

/-- The ideal sampler remains visibly separate from a production finite-width sampler. -/
noncomputable def idealCoinSampler (_ : ℕ) : ProbComp (PKECoins toyParams) :=
  pkeSampleCoins toyParams

variable
  (twoStages : TwoDQCSDNativeStages toyParams encode encBool keyDependentAdversary
    idealCoinSampler)
  (threeStages : ThreeDQCSDNativeStages toyParams encode encBool keyDependentAdversary)

example (input : TwoDQCSDInput toyParams) :
    twoStages.resources.total.time input = twoStages.compiled.time input ∧
      twoStages.resources.total.workspace input = twoStages.compiled.workspace input ∧
      twoStages.resources.total.randomBits input = twoStages.compiled.time input := by
  rfl

example (input : ThreeDQCSDInput toyParams) :
    threeStages.resources.total.time input = threeStages.compiled.time input ∧
      threeStages.resources.total.workspace input = threeStages.compiled.workspace input ∧
      threeStages.resources.total.randomBits input = threeStages.compiled.time input := by
  rfl

example (input : TwoDQCSDInput toyParams) :
    twoStages.resources.total.queries input = 0 ∧
      twoStages.resources.total.requestBits input = 0 ∧
      twoStages.resources.total.replyBits input = 0 ∧
      twoStages.resources.total.handlerTime input = 0 := by
  simp

example (input : ThreeDQCSDInput toyParams) :
    threeStages.resources.total.queries input = 0 ∧
      threeStages.resources.total.requestBits input = 0 ∧
      threeStages.resources.total.replyBits input = 0 ∧
      threeStages.resources.total.handlerTime input = 0 := by
  simp

example (input : TwoDQCSDInput toyParams) :
    twoStages.compiled.time input = ClassicalStageMachine.compTime
      (ClassicalStageMachine.compTime
        (ClassicalStageMachine.compTime (twoStages.choose.time input)
          (twoStages.hiddenBit.time input))
        (twoStages.sampler.time input))
      (twoStages.guessVerdict.time input) :=
  twoStages.time_eq input

example (input : ThreeDQCSDInput toyParams) :
    threeStages.compiled.time input = ClassicalStageMachine.compTime
      (ClassicalStageMachine.compTime (threeStages.choose.time input)
        (threeStages.hiddenBit.time input))
      (threeStages.guessVerdict.time input) :=
  threeStages.time_eq input

example (input : ThreeDQCSDInput toyParams) :
    (threeStages.hiddenBit.comp threeStages.choose).workspace input =
      (threeStages.hiddenBit.tapeCount + threeStages.choose.tapeCount + 2) *
        (2 * max
          (max (threeStages.choose.workspace input) (threeStages.hiddenBit.workspace input))
          (threeStages.choose.time input + 2) + 1) :=
  ClassicalStageMachine.workspace_comp threeStages.hiddenBit threeStages.choose input

example (input : TwoDQCSDInput toyParams) :
    twoStages.compiled.runRaw input [] = twoStages.compiled.machine.runClosed
      (twoStages.compiled.time input) [] := rfl

example (input : ThreeDQCSDInput toyParams) :
    threeStages.compiled.runRaw input [] = threeStages.compiled.machine.runClosed
      (threeStages.compiled.time input) [] := rfl

end CslibFrontierTests.HQCINDCPA
