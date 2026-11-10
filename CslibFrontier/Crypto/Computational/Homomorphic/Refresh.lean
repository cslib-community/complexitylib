/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Basic
public import CslibFrontier.Crypto.Computational.Homomorphic.Circuit
import Mathlib.Data.List.Forall2

/-!
# Homomorphic refresh from decryption circuits

Gentry's refresh algorithm encrypts the public bits of an old ciphertext and evaluates a
decryption circuit using those encryptions and an encrypted old secret key. Connecting two
decryption circuits to NAND derives a homomorphic NAND operation [Gentry2009, Section 2].

The old ciphertexts need only have the declared width: they may be outputs of earlier
homomorphic evaluations. The base evaluation guarantee applies because its immediate inputs
are fresh encryptions of bits. The two copies of the encrypted secret key may be identical.

`Bootstrappable` asserts membership of the actual circuits in the permitted set. Refresh is
constructed below, and its correctness is proved rather than bundled into that assumption.
These results establish functional correctness and fixed output width. They do not yet establish
uniform polynomial running time, a leveled evaluator, IND-CPA security, or fixed-key FHE.

## Main definitions

* `Cslib.Crypto.Homomorphic.DecryptionCircuits`: circuits computing the base decryption algorithm.
* `Cslib.Crypto.Homomorphic.Scheme.Bootstrappable`: permitted decryption and NAND augmentations.
* `Cslib.Crypto.Homomorphic.Scheme.refresh`, `.refreshNand`: explicit probabilistic programs.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.decrypt_refresh`: refresh preserves the decrypted bit.
* `Cslib.Crypto.Homomorphic.Scheme.decrypt_refreshNand`: NAND refresh computes NAND of decrypted
  bits, including for old ciphertexts outside the support of fresh encryption.
* `Cslib.Crypto.Homomorphic.Scheme.length_refresh`, `.length_refreshNand`: refreshed ciphertexts
  have the same width as base ciphertexts, independent of prior evaluation depth.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Circuits

/-- Actual circuits computing decryption on the specified fixed-width inputs. Existence alone
does not certify uniform circuit generation; that is a separate computational obligation. -/
structure DecryptionCircuits (E : Scheme) (secretWidth ciphertextWidth : ℕ → ℕ) where
  /-- Secret-key bits precede ciphertext bits. -/
  circuit : (n : ℕ) → Circuit Boolean.signature (secretWidth n + ciphertextWidth n) 1
  /-- The circuit computes decryption on all well-sized keys and ciphertexts, including outputs
  of earlier homomorphic evaluations. -/
  correct : ∀ n sk c, sk.length = secretWidth n → c.length = ciphertextWidth n →
    (circuit n).eval Boolean.interpretation
      (BitString.ofList (secretWidth n + ciphertextWidth n) (sk ++ c)) 0 = E.decrypt n sk c

namespace Scheme

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Gentry's permitted-circuit condition for identity and NAND augmentations. This condition
does not postulate a refresh algorithm or a correctness theorem for one. -/
structure Bootstrappable : Prop where
  /-- The identity augmentation is the decryption circuit itself. -/
  decrypt_mem : ∀ n, E.permitted n ⟨_, D.circuit n⟩
  /-- NAND of two decryptions is permitted by the base evaluator. -/
  nand_mem : ∀ n, E.permitted n ⟨_, augmentNand (D.circuit n)⟩

/-- Refresh an old ciphertext using its public bits and an encrypted old secret key. -/
def refresh (n : ℕ) (pk : List Bool) (encryptedKey : List (List Bool))
    (ciphertext : List Bool) : ProbComp (List Bool) := do
  let encryptedBits ← E.encryptBits n pk ciphertext
  E.evaluate n pk ⟨_, D.circuit n⟩ (encryptedKey ++ encryptedBits)

/-- Refresh and NAND two old ciphertexts. The same encrypted secret key is used in both blocks. -/
def refreshNand (n : ℕ) (pk : List Bool) (encryptedKey : List (List Bool))
    (first second : List Bool) : ProbComp (List Bool) := do
  let firstBits ← E.encryptBits n pk first
  let secondBits ← E.encryptBits n pk second
  E.evaluate n pk ⟨_, augmentNand (D.circuit n)⟩
    ((encryptedKey ++ firstBits) ++ (encryptedKey ++ secondBits))

/-- Refresh preserves decryption of every well-sized old ciphertext, whether fresh or evaluated. -/
theorem decrypt_refresh (hE : E.Correct) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk ciphertext : List Bool) (hsk : sk.length = secretWidth n)
    (hc : ciphertext.length = ciphertextWidth n) (encryptedKey : List (List Bool))
    (hek : E.FreshInputs n keys.1 sk encryptedKey) (result : List Bool)
    (hresult : result ∈ (ProbComp.eval (refresh D n keys.1 encryptedKey ciphertext)).support) :
    E.decrypt n keys.2 result = E.decrypt n sk ciphertext := by
  rw [refresh, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨encryptedBits, hbits, hresult⟩ := hresult
  have hfresh := (E.mem_support_encryptBits_iff n keys.1 ciphertext encryptedBits).1 hbits
  have heval := hE.decrypt_evaluate n keys hkeys ⟨_, D.circuit n⟩ (hD.decrypt_mem n)
    (sk ++ ciphertext) (encryptedKey ++ encryptedBits)
    (by simp only [List.length_append, hsk, hc]) (List.rel_append hek hfresh) result hresult
  exact heval.trans (D.correct n sk ciphertext hsk hc)

/-- NAND refresh computes NAND of the old decryptions. No fresh-encryption hypothesis is needed
for either old ciphertext, and the encrypted secret key is shared between the two input blocks. -/
theorem decrypt_refreshNand (hE : E.Correct) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk first second : List Bool) (hsk : sk.length = secretWidth n)
    (hfirst : first.length = ciphertextWidth n) (hsecond : second.length = ciphertextWidth n)
    (encryptedKey : List (List Bool)) (hek : E.FreshInputs n keys.1 sk encryptedKey)
    (result : List Bool)
    (hresult : result ∈ (ProbComp.eval
      (refreshNand D n keys.1 encryptedKey first second)).support) :
    E.decrypt n keys.2 result = !(E.decrypt n sk first && E.decrypt n sk second) := by
  rw [refreshNand, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨firstBits, hfirstBits, hresult⟩ := hresult
  rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨secondBits, hsecondBits, hresult⟩ := hresult
  have hfresh₁ := (E.mem_support_encryptBits_iff n keys.1 first firstBits).1 hfirstBits
  have hfresh₂ := (E.mem_support_encryptBits_iff n keys.1 second secondBits).1 hsecondBits
  have hlen₁ : (sk ++ first).length = secretWidth n + ciphertextWidth n := by
    simp only [List.length_append, hsk, hfirst]
  have hlen₂ : (sk ++ second).length = secretWidth n + ciphertextWidth n := by
    simp only [List.length_append, hsk, hsecond]
  have heval := hE.decrypt_evaluate n keys hkeys ⟨_, augmentNand (D.circuit n)⟩ (hD.nand_mem n)
    ((sk ++ first) ++ (sk ++ second))
    ((encryptedKey ++ firstBits) ++ (encryptedKey ++ secondBits))
    (by simp only [List.length_append, hsk, hfirst, hsecond])
    (List.rel_append (List.rel_append hek hfresh₁) (List.rel_append hek hfresh₂)) result hresult
  rw [BitString.ofList_append hlen₁ hlen₂, eval_augmentNand,
    D.correct n sk first hsk hfirst, D.correct n sk second hsk hsecond] at heval
  exact heval

/-- Refresh has the same output width as the base scheme. -/
theorem length_refresh (hE : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk ciphertext : List Bool) (hsk : sk.length = secretWidth n)
    (hc : ciphertext.length = ciphertextWidth n) (encryptedKey : List (List Bool))
    (hek : E.FreshInputs n keys.1 sk encryptedKey) (result : List Bool)
    (hresult : result ∈ (ProbComp.eval (refresh D n keys.1 encryptedKey ciphertext)).support) :
    result.length = ciphertextWidth n := by
  rw [refresh, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨encryptedBits, hbits, hresult⟩ := hresult
  have hfresh := (E.mem_support_encryptBits_iff n keys.1 ciphertext encryptedBits).1 hbits
  exact hE.evaluate_length n keys hkeys _ (hD.decrypt_mem n)
    (sk ++ ciphertext) (encryptedKey ++ encryptedBits)
    (by simp only [List.length_append, hsk, hc]) (List.rel_append hek hfresh) result hresult

/-- NAND refresh has the same output width as the base scheme, independent of prior depth. -/
theorem length_refreshNand (hE : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk first second : List Bool) (hsk : sk.length = secretWidth n)
    (hfirst : first.length = ciphertextWidth n) (hsecond : second.length = ciphertextWidth n)
    (encryptedKey : List (List Bool)) (hek : E.FreshInputs n keys.1 sk encryptedKey)
    (result : List Bool)
    (hresult : result ∈ (ProbComp.eval
      (refreshNand D n keys.1 encryptedKey first second)).support) :
    result.length = ciphertextWidth n := by
  rw [refreshNand, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨firstBits, hfirstBits, hresult⟩ := hresult
  rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hresult
  obtain ⟨secondBits, hsecondBits, hresult⟩ := hresult
  have hfresh₁ := (E.mem_support_encryptBits_iff n keys.1 first firstBits).1 hfirstBits
  have hfresh₂ := (E.mem_support_encryptBits_iff n keys.1 second secondBits).1 hsecondBits
  exact hE.evaluate_length n keys hkeys _ (hD.nand_mem n)
    ((sk ++ first) ++ (sk ++ second))
    ((encryptedKey ++ firstBits) ++ (encryptedKey ++ secondBits))
    (by simp only [List.length_append, hsk, hfirst, hsecond])
    (List.rel_append (List.rel_append hek hfresh₁) (List.rel_append hek hfresh₂)) result hresult

end Scheme

end Cslib.Crypto.Homomorphic
