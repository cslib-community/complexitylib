/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.HQC.INDCPA

/-! Checked key-dependent-message clients for the ideal HQC-PKE IND-CPA reduction. -/

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

end CslibFrontierTests.HQCINDCPA
