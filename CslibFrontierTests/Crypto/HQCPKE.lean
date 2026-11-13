/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.PKE

/-! Checked ideal HQC-PKE truncation, support, phase and decoder-correction clients. -/

public section

namespace CslibFrontierTests.HQCPKE

open Cslib Cslib.BitString Cslib.Crypto.HQC Cslib.Crypto.Protocols Cslib.Probability

/-- A positive toy instance with proper one-bit truncation and positive source weights. -/
abbrev toyParams : PKEParams where
  n := 4
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

local instance : NeZero toyParams.codeLen := ⟨by decide⟩

example : 0 < toyParams.n ∧ 0 < toyParams.ell ∧ toyParams.ell < toyParams.n ∧
    0 < toyParams.omega ∧ 0 < toyParams.omegaR ∧ 0 < toyParams.omegaE := by
  decide

/-- The length-three repetition code. -/
def repetitionEncode (m : PKEMessage toyParams) : Codeword toyParams :=
  fun _ => m 0

/-- Majority decoding for the length-three repetition code. -/
def repetitionDecode (w : Codeword toyParams) : PKEMessage toyParams :=
  fun _ => (w 0 && w 1) || (w 0 && w 2) || (w 1 && w 2)

/-- A deliberately invalid decoder used to show that the correction contract has content. -/
def falseDecode (_ : Codeword toyParams) : PKEMessage toyParams :=
  fun _ => false

theorem repetition_corrects : DecoderCorrects toyParams repetitionEncode repetitionDecode := by
  unfold DecoderCorrects repetitionEncode repetitionDecode
  decide

theorem falseDecode_not_corrects : ¬DecoderCorrects toyParams repetitionEncode falseDecode := by
  unfold DecoderCorrects repetitionEncode falseDecode
  decide

example : truncate toyParams ![true, false, true, true] = ![true, false, true] := by
  decide

def h : RingWord toyParams := ![true, false, true, false]
def x : RingWord toyParams := ![true, false, false, false]
def y : RingWord toyParams := ![false, true, false, false]
def error : RingWord toyParams := ![false, false, true, false]

/-- Choosing `r₁ = x` and `r₂ = y` makes the two product errors cancel, leaving `error`. -/
def coins : PKECoins toyParams := ⟨y, error, x⟩

example : weight x = toyParams.omega ∧ weight y = toyParams.omega ∧
    weight coins.r2 = toyParams.omegaR ∧ weight coins.e = toyParams.omegaE ∧
      weight coins.r1 = toyParams.omegaR := by
  decide

example : pkeDecryptionNoise toyParams x y coins = error := by
  decide

example : weight (truncate toyParams (pkeDecryptionNoise toyParams x y coins)) ≤
    toyParams.delta := by
  decide

example (m : PKEMessage toyParams) :
    pkeDecryptInput toyParams y
        (pkeEncrypt toyParams repetitionEncode (expandedPublicKey toyParams h x y) m coins) =
      repetitionEncode m + truncate toyParams (pkeDecryptionNoise toyParams x y coins) :=
  pkeDecryptInput_encrypt toyParams repetitionEncode h x y m coins

example (m : PKEMessage toyParams) :
    pkeDecrypt toyParams repetitionDecode y
      (pkeEncrypt toyParams repetitionEncode (expandedPublicKey toyParams h x y) m coins) = m :=
  pkeDecrypt_encrypt_eq_of_weight_le toyParams repetitionEncode repetitionDecode repetition_corrects
    h x y m coins (by decide)

noncomputable def toyPKE :=
  toExplicitCoinPKE toyParams repetitionEncode repetitionDecode

example : toyPKE.encDet = pkeEncrypt toyParams repetitionEncode := rfl

example (m : PKEMessage toyParams) :
    toyPKE.dec y (toyPKE.encDet (expandedPublicKey toyParams h x y) m coins) = some m := by
  exact congrArg some (pkeDecrypt_encrypt_eq_of_weight_le toyParams repetitionEncode
    repetitionDecode repetition_corrects h x y m coins (by decide))

example {keys : PKEPublicKey toyParams × PKESecretKey toyParams}
    (hkeys : keys ∈ (ProbComp.eval toyPKE.keyGen).support) :
    ∃ h x y : RingWord toyParams,
      weight x = toyParams.omega ∧ weight y = toyParams.omega ∧
        keys = (expandedPublicKey toyParams h x y, y) :=
  pkeKeyGen_support toyParams hkeys

example {sample : PKECoins toyParams}
    (hsample : sample ∈ (ProbComp.eval toyPKE.sampleCoins).support) :
    weight sample.r2 = toyParams.omegaR ∧ weight sample.e = toyParams.omegaE ∧
      weight sample.r1 = toyParams.omegaR :=
  pkeSampleCoins_support toyParams hsample

end CslibFrontierTests.HQCPKE
