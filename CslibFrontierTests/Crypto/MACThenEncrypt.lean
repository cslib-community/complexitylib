/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/
import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt

/-!
# Tests for MAC-then-Encrypt and the Chosen-Ciphertext Counterexample

Concrete evaluations, PPT certificates, and counterexample witnesses for
`CslibFrontier/Crypto/Computational/Encryption/MACThenEncrypt.lean`. We instantiate
`macThenEncrypt` and its trailing-bit malleable extension `extendCipher` on explicit concrete
primitives (`echoCipher` and `echoMAC`), verify decryption round-trips and tag rejection, check
exact advantage `1` for `macThenEncryptExtendCIAdversary` and `macThenEncryptExtendCCAAdversary`,
and verify all four negative theorems (`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`,
`OneTimeINDCCA`, `INDCCA`).
-/
namespace CslibFrontierTests.Crypto.MACThenEncrypt
open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-! ### Concrete cipher and MAC primitives -/

/-- Deterministic identity symmetric cipher (PPT on all inputs, decrypting every ciphertext as a
raw encoded string) used to instantiate `macThenEncrypt` and witness the `extendCipher`
counterexample. -/
def echoCipher : SymmetricCipher where
  keyGen _ := pure []
  encrypt _ _ msg := pure msg
  decrypt _ _ ct := some ct
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro _ _ _ _ _ ct hct
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
    subst hct
    rfl

/-- Deterministic echo MAC signing `n`-bit messages by `tag = msg` and checking equality. -/
def echoMAC : MACScheme where
  msgLen n := n
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ msg tag := msg == tag
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ msg _ tag htag
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    exact beq_self_eq_true _

/-- `echoCipher` satisfies plaintext-tag decryption completeness for `echoMAC`. -/
theorem echo_h_dec :
    ∀ n ke km msg tag,
      ke ∈ (ProbComp.eval (echoCipher.keyGen n)).support →
      km ∈ (ProbComp.eval (echoMAC.keyGen n)).support →
      msg.length = n →
      tag ∈ (ProbComp.eval (echoMAC.sign km msg)).support →
      ∀ ct ∈ (ProbComp.eval
          (echoCipher.encrypt n ke (encPair encBits encBits (msg, tag)))).support,
        echoCipher.decrypt n ke ct = some (encPair encBits encBits (msg, tag)) := by
  intro _ _ _ msg tag _ _ _ _ ct hct
  change ct ∈ (ProbComp.eval (pure (encPair encBits encBits (msg, tag)))).support at hct
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
  subst hct
  rfl

/-- Plain MAC-then-Encrypt instantiated on `echoCipher` and `echoMAC`. -/
noncomputable def echoMtE : SymmetricCipher :=
  macThenEncrypt echoCipher echoMAC (fun _ => rfl) echo_h_dec

/-- MAC-then-Encrypt over `echoCipher.extendCipher` and `echoMAC`. -/
noncomputable def echoMtEExt : SymmetricCipher :=
  macThenEncrypt echoCipher.extendCipher echoMAC (fun _ => rfl)
    (h_dec_extendCipher echoCipher echoMAC echo_h_dec)

/-! ### Round-trip, tag-rejection, and trailing-bit malleability checks -/

/-- Valid `(msg, msg)` pairs decrypt to `some msg`, whereas mismatched tags are rejected. -/
example :
    echoMtE.decrypt 2 (encPair encBits encBits ([], []))
        (encPair encBits encBits ([false, true], [false, true])) = some [false, true] ∧
    echoMtE.decrypt 2 (encPair encBits encBits ([], []))
        (encPair encBits encBits ([false, true], [false, false])) = none := by
  simp only [echoMtE, macThenEncrypt, echoCipher, echoMAC]
  decide

/-- Under `echoMtEExt`, flipping the appended trailing `false` bit to `true` yields a distinct
ciphertext with the exact same plaintext decryption. -/
example :
    let k := encPair encBits encBits ([], [])
    let c := encPair encBits encBits ([false, true], [false, true])
    c ++ [false] ≠ c ++ [true] ∧
    echoMtEExt.decrypt 2 k (c ++ [false]) = some [false, true] ∧
    echoMtEExt.decrypt 2 k (c ++ [true]) = some [false, true] := by
  simp only [echoMtEExt, macThenEncrypt, SymmetricCipher.extendCipher, echoCipher, echoMAC]
  decide

/-! ### Parametric preservation and concrete adversarial bounds -/

example {E : SymmetricCipher} (h : E.INDCPA) : E.extendCipher.INDCPA :=
  h.extendCipher

example {E : SymmetricCipher} (h : E.OneTimeINDCPA) : E.extendCipher.OneTimeINDCPA :=
  h.extendCipher

example :
    IsOraclePPT encBool (macThenEncryptExtendCCAAdversary (fun n => 3 * n + 2)) ∧
    IsOraclePPT encBits (macThenEncryptExtendCIAdversary (fun n => 3 * n + 2)) :=
  ⟨isOraclePPT_macThenEncryptExtendCCAAdversary (by polytime),
   isOraclePPT_macThenEncryptExtendCIAdversary (by polytime)⟩

/-- Exact ciphertext length bound `3 * n + 2` for `echoMtEExt` on `n`-bit plaintexts. -/
theorem echoMtEExt_ctBound (n : ℕ) :
    ∀ k ∈ (ProbComp.eval (echoMtEExt.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (echoMtEExt.encrypt n k msg)).support,
        ct.length ≤ 3 * n + 2 := by
  intro k _ msg hmsg ct hct
  simp only [echoMtEExt, macThenEncrypt, SymmetricCipher.extendCipher, echoCipher, echoMAC,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hct
  obtain ⟨tag, rfl, c, rfl, rfl⟩ := hct
  rw [List.length_append, List.length_singleton, encPair_apply]
  dsimp only
  rw [length_frame_append, encBits_apply, hmsg]
  omega

/-- Concrete `ciOneTimeGame` win (`1`) and `ccaOneTimeGame` advantage `1` at `n = 2`. -/
example :
    ProbComp.eval
        (echoMtEExt.ciOneTimeGame (macThenEncryptExtendCIAdversary (fun n => 3 * n + 2)) 2) =
      PMF.pure true ∧
    Game.advantage
        (ProbComp.eval
          (echoMtEExt.ccaOneTimeGame
            (macThenEncryptExtendCCAAdversary (fun n => 3 * n + 2)) false 2))
        (ProbComp.eval
          (echoMtEExt.ccaOneTimeGame
            (macThenEncryptExtendCCAAdversary (fun n => 3 * n + 2)) true 2)) = 1 :=
  ⟨eval_ciOneTimeGame_macThenEncrypt_extendCipher echoCipher echoMAC (fun _ => rfl) echo_h_dec
     (fun n => 3 * n + 2) 2 (echoMtEExt_ctBound 2),
   advantage_ccaOneTimeGame_macThenEncrypt_extendCipher_eq_one echoCipher echoMAC (fun _ => rfl)
     echo_h_dec (fun n => 3 * n + 2) (by decide) (echoMtEExt_ctBound 2)⟩

/-- Concrete failure of ciphertext integrity and CCA security on `echoMtEExt`. -/
example :
    ¬ echoMtEExt.OneTimeCiphertextIntegrity ∧
    ¬ echoMtEExt.CiphertextIntegrity ∧
    ¬ echoMtEExt.OneTimeINDCCA ∧
    ¬ echoMtEExt.INDCCA :=
  ⟨not_oneTimeCiphertextIntegrity_macThenEncrypt_extendCipher echoCipher echoMAC
     (fun _ => rfl) echo_h_dec,
   not_ciphertextIntegrity_macThenEncrypt_extendCipher echoCipher echoMAC
     (fun _ => rfl) echo_h_dec,
   not_oneTimeINDCCA_macThenEncrypt_extendCipher echoCipher echoMAC
     (fun _ => rfl) echo_h_dec,
   not_indcca_macThenEncrypt_extendCipher echoCipher echoMAC
     (fun _ => rfl) echo_h_dec⟩

/-! ### Axiom audit guards -/

/-- info: 'Cslib.Crypto.SymmetricCipher.INDCPA.extendCipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SymmetricCipher.INDCPA.extendCipher

/-- info: 'Cslib.Crypto.SymmetricCipher.OneTimeINDCPA.extendCipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SymmetricCipher.OneTimeINDCPA.extendCipher

/-- info: 'Cslib.Crypto.h_dec_extendCipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms h_dec_extendCipher

/-- info: 'Cslib.Crypto.not_ciphertextIntegrity_macThenEncrypt_extendCipher' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_ciphertextIntegrity_macThenEncrypt_extendCipher

/-- info: 'Cslib.Crypto.not_indcca_macThenEncrypt_extendCipher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_indcca_macThenEncrypt_extendCipher

end CslibFrontierTests.Crypto.MACThenEncrypt
