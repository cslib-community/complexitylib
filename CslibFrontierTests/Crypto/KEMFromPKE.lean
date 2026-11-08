/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.KEMFromPKE
public import CslibFrontierTests.Crypto.HybridEncryption
import CslibFrontier.Tactic.PPT
import CslibFrontier.Crypto.Negligible.Basic

/-!
# Encrypted-key KEM tests

Exercise the loss-one PKE-to-KEM reduction, native sampling at doubled key length, the zero-key
boundary, and actual composition with the existing one-time pad DEM. The length-only encryption
fixture is secure but not decryptable; the identity-encryption fixture has correct decryption but
reveals the key. These tests keep the two contracts separate.
-/

public section

namespace CslibFrontierTests.Crypto.KEMFromPKE

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.HybridEncryption
open scoped NNReal

/-- The existing length-only encryption fixture has a native certificate. -/
theorem lengthOnlyEncrypt_ppt :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => lengthOnlyEncrypt p.1 p.2.1 p.2.2) := by
  unfold lengthOnlyEncrypt
  ppt

/-- Instantiation of the actual encrypted-key constructor at doubled key length. This is a
security-game fixture: the underlying length-only encryption has no correct decryptor. -/
theorem kemINDCPA_doubleKey_lengthOnly :
    KEMINDCPA (fun n => 2 * n) toyKeyGen
      (encryptKeyEncaps (fun n => 2 * n) lengthOnlyEncrypt) :=
  wordINDCPA_lengthOnly.kemINDCPA_encryptKeyEncaps (by fun_prop)

example : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
    (fun p => encryptKeyEncaps (fun n => 2 * n) lengthOnlyEncrypt p.1 p.2) :=
  isPPTOn_encryptKeyEncaps (by fun_prop) lengthOnlyEncrypt_ppt

example : (kemToPKEAdversary (fun n => 2 * n) eqKemDistinguisher).IsPPT :=
  isPPT_kemToPKEAdversary (by fun_prop) eqKemDistinguisher_ppt

/-- PKE → KEM → hybrid PKE, using the existing arbitrary-key-length one-time pad DEM. -/
theorem indcpaOf_hybrid_doubleKey_lengthOnly :
    INDCPAOf encBits toyKeyGen
      (hybridEncrypt (encryptKeyEncaps (fun n => 2 * n) lengthOnlyEncrypt)
        (otpKeyWordEncrypt (fun n => 2 * n))) :=
  kemINDCPA_doubleKey_lengthOnly.hybrid_indcpa
    (demOneTimeKeyINDCPA_otpKeyWordEncrypt _) toyKeyGen_ppt
    (isPPTOn_encryptKeyEncaps (by fun_prop) lengthOnlyEncrypt_ppt)
    (isPPTOn_otpKeyWordEncrypt (by fun_prop))

/-- The original word decryptor serves directly as the KEM decryptor. This identity-encryption
fixture is correctly decryptable but insecure. -/
example (keyLen : ℕ → ℕ) (n : ℕ) (pk k ct : List Bool)
    (h : (k, ct) ∈ (ProbComp.eval
      (encryptKeyEncaps keyLen (fun _ _ m => pure m) n pk)).support) :
    ct = k := by
  exact decrypt_encryptKeyEncaps (fun _ _ c => c)
    (sk := []) (fun _ _ _ hc => by simpa using hc) h

/-- Zero-length encapsulation encrypts exactly the empty word, with no random key bits. -/
example (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (n : ℕ) (pk : List Bool) :
    ProbComp.eval (encryptKeyEncaps (fun _ => 0) encrypt n pk) =
      (ProbComp.eval (encrypt n pk [])).map (fun ct => ([], ct)) := by
  simp [encryptKeyEncaps, BitString.sampleList]

example : KEMINDCPA (fun _ => 0) toyKeyGen
    (encryptKeyEncaps (fun _ => 0) lengthOnlyEncrypt) :=
  wordINDCPA_lengthOnly.kemINDCPA_encryptKeyEncaps (by fun_prop)

/-- Revealing the sampled key gives positive distinguishing advantage even at key length one.
The ideal experiment guesses the independent key correctly with probability one half. -/
theorem advantage_encryptKeyEncaps_revealing (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemRealGame (fun _ => pure ([], []))
        (encryptKeyEncaps (fun _ => 1) (fun _ _ m => pure m)) eqKemDistinguisher n))
      (ProbComp.eval (kemIdealGame (fun _ => 1) (fun _ => pure ([], []))
        (encryptKeyEncaps (fun _ => 1) (fun _ _ m => pure m)) eqKemDistinguisher n)) =
      (1 : ℝ≥0) / 2 := by
  simp only [kemRealGame, kemRealGameWith,
    kemIdealGame, kemIdealGameWith, encryptKeyEncaps, eqKemDistinguisher,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    BitString.uniformList_succ, BitString.uniformList_zero, encPair_apply, encBits_apply,
    unframe_frame_append, dropFrame_frame_append, PMF.bind_bind, PMF.pure_bind,
    decide_true, PMF.bind_const, Game.advantage, Game.succProbability, PMF.bind_apply,
    PMF.uniformOfFintype_apply,
    Fintype.card_bool, tsum_bool]
  norm_num [NNReal.nndist_eq]
  rw [ENNReal.toNNReal_add] <;>
    norm_num [ENNReal.toNNReal_add, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat, ENNReal.mul_eq_top, ENNReal.inv_eq_top]
  norm_num [NNReal.sub_def, Real.toNNReal_div]
  rw [Real.toNNReal_of_nonpos (by norm_num)]
  positivity


/-- The canonical KEM predicate rejects identity encryption: one uniform distinguisher has
constant advantage one half at every security parameter. -/
theorem not_kemINDCPA_encryptKeyEncaps_revealing :
    ¬ KEMINDCPA (fun _ => 1) (fun _ => pure ([], []))
      (encryptKeyEncaps (fun _ => 1) (fun _ _ m => pure m)) := by
  intro hsecure
  have hneg := hsecure eqKemDistinguisher eqKemDistinguisher_ppt
  simp only [advantage_encryptKeyEncaps_revealing] at hneg
  exact not_negligible_const (by positivity) hneg

end CslibFrontierTests.Crypto.KEMFromPKE
