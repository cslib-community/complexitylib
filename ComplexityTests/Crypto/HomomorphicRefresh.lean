/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import ComplexityTests.Crypto.HomomorphicExample

/-! Regression checks for homomorphic refresh using the deliberately insecure tagged fixture. -/

namespace ComplexityTests.HomomorphicRefresh

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample

-- The functional instance also inhabits every efficiency hypothesis of NAND refresh.
example : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (encList encBits) (encPair encBits encBits))))
    encBits (fun p =>
      Scheme.refreshNand decryptionCircuits p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply Scheme.isPPTOn_refreshNand encrypt_ppt
    evaluate_ppt decryptionCircuits circuits_poly
  all_goals fun_prop

-- These bundled hypotheses have an actual instance.
example : tagged.Correct ∧ tagged.FixedWidth (fun _ => 1) (fun _ => 2) ∧
    Scheme.Bootstrappable decryptionCircuits :=
  ⟨tagged_correct, tagged_width, tagged_bootstrappable⟩

-- Every evaluation-tagged ciphertext is outside the support of every fresh encryption.
example (n : ℕ) (pk : List Bool) (b message : Bool) :
    [b, true] ∉ (ProbComp.eval (tagged.encrypt n pk message)).support := by
  simp [tagged]

-- The same encrypted key bit is reused in both halves of the augmented circuit.
private theorem encrypted_key : tagged.FreshInputs 0 [true] [true] [[false, false]] := by
  simp [Scheme.FreshInputs, tagged]

-- Refresh consumes an evaluated ciphertext and preserves its decrypted bit and width.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refresh decryptionCircuits 0 [true] [[false, false]] [false, true])).support) :
    tagged.decrypt 0 [true] result = true ∧ result.length = 2 := by
  constructor
  · exact Scheme.decrypt_refresh decryptionCircuits tagged_correct tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] rfl rfl
      [[false, false]] encrypted_key result h
  · exact Scheme.length_refresh decryptionCircuits tagged_width tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] rfl rfl
      [[false, false]] encrypted_key result h

-- Both NAND inputs may be evaluated ciphertexts. This computes NAND(true, false) = true.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refreshNand decryptionCircuits 0 [true] [[false, false]]
        [false, true] [true, true])).support) :
    tagged.decrypt 0 [true] result = true ∧ result.length = 2 := by
  constructor
  · exact Scheme.decrypt_refreshNand decryptionCircuits tagged_correct tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] [true, true] rfl rfl rfl
      [[false, false]] encrypted_key result h
  · exact Scheme.length_refreshNand decryptionCircuits tagged_width tagged_bootstrappable 0
      ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
      [true] [false, true] [true, true] rfl rfl rfl
      [[false, false]] encrypted_key result h

-- Switch from the old key [false] to [true]. The encrypted old key is shared by both inputs.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.refreshNand decryptionCircuits 0 [true] [[true, false]]
        [true, true] [false, true])).support) :
    tagged.decrypt 0 [true] result = true := by
  exact Scheme.decrypt_refreshNand decryptionCircuits tagged_correct tagged_bootstrappable 0
    ([true], [true]) ((keys_supported 0 _).2 ⟨true, rfl⟩)
    [false] [true, true] [false, true] rfl rfl rfl [[true, false]]
    (by simp [Scheme.FreshInputs, tagged]) result h

-- Applying the base evaluator directly to an evaluated encryption of true gives false.
example : ProbComp.eval
    (tagged.evaluate 0 [true] ⟨1, Circuit.wiring Boolean.signature id⟩ [[false, true]]) =
    PMF.pure [true, true] := by
  simp [tagged, evaluatedBit]

-- Refresh can be repeated even though the first output is outside fresh-encryption support.
example : ProbComp.eval (do
    let c ← Scheme.refresh decryptionCircuits 0 [true] [[false, false]] [false, true]
    Scheme.refresh decryptionCircuits 0 [true] [[false, false]] c) = PMF.pure [false, true] := by
  simp [Scheme.refresh, Scheme.encryptBits, tagged, evaluatedBit, decryptionCircuits,
    eval_xorCircuit, decode, BitString.ofList]

-- Empty plaintext words are encrypted without introducing a ciphertext.
example : ProbComp.eval (tagged.encryptBits 0 [true] []) = PMF.pure [] := rfl

end ComplexityTests.HomomorphicRefresh
