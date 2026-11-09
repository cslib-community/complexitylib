/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Basic
import CslibFrontier.Languages.Probabilistic.Traverse
import Mathlib.Data.List.GetD

/-!
# Bitwise encryption hybrids

Replace an initial segment of a word by zeros before encrypting its bits. A simulator samples
the surrounding ciphertexts and inserts one challenge ciphertext at the selected coordinate.
The exact distributional identities retain every other ciphertext and its independent
encryption randomness. They also apply inside a larger randomized context.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.encryptBitsHybrid`: encrypt a word with a zero prefix.
* `Cslib.Crypto.Homomorphic.Scheme.spliceEncryptedBit`: insert a bit-encryption challenge.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_spliceEncryptedBit_original`: the original bit gives
  the earlier adjacent hybrid.
* `Cslib.Crypto.Homomorphic.Scheme.eval_spliceEncryptedBit_zero`: a zero bit gives the next
  adjacent hybrid.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

variable (E : Scheme)

/-- Encrypt a word after replacing its first `cut` bits by zeros. The word's length is
preserved even when the requested cut is beyond its end. -/
def encryptBitsHybrid (n : ℕ) (pk bits : List Bool) (cut : ℕ) :
    ProbComp (List (List Bool)) :=
  E.encryptBits n pk (List.replicate (min cut bits.length) false ++ bits.drop cut)

/-- Encrypt the zero prefix and the original suffix, inserting the supplied ciphertext between
them. The challenge is already encrypted and is not encrypted again. -/
def spliceEncryptedBit (n : ℕ) (pk : List Bool) (before : ℕ) (after challenge : List Bool) :
    ProbComp (List (List Bool)) := do
  let front ← E.encryptBits n pk (List.replicate before false)
  let back ← E.encryptBits n pk after
  pure (front ++ challenge :: back)

/-- The initial bit hybrid is the actual bitwise encryption sampler. -/
@[simp] theorem encryptBitsHybrid_zero (n : ℕ) (pk bits : List Bool) :
    E.encryptBitsHybrid n pk bits 0 = E.encryptBits n pk bits := by
  simp [encryptBitsHybrid]

/-- The final bit hybrid encrypts an equal-length zero word. -/
theorem encryptBitsHybrid_length (n : ℕ) (pk bits : List Bool) :
    E.encryptBitsHybrid n pk bits bits.length =
      E.encryptBits n pk (List.replicate bits.length false) := by
  simp [encryptBitsHybrid]

/-- An encryption of the selected original bit supplies the earlier adjacent hybrid. -/
theorem eval_spliceEncryptedBit_original (n : ℕ) (pk bits : List Bool) (cut : ℕ)
    (hcut : cut < bits.length) :
    ProbComp.eval (do
      let challenge ← E.encrypt n pk (bits.getD cut false)
      E.spliceEncryptedBit n pk cut (bits.drop (cut + 1)) challenge) =
        ProbComp.eval (E.encryptBitsHybrid n pk bits cut) := by
  simp only [spliceEncryptedBit, encryptBits, encryptBitsHybrid,
    Nat.min_eq_left hcut.le, List.getD_eq_getElem _ _ hcut, List.drop_eq_getElem_cons hcut]
  exact ProbComp.eval_mapM_splice (E.encrypt n pk) (List.replicate cut false)
    bits[cut] (bits.drop (cut + 1))

/-- An encryption of zero supplies the next adjacent hybrid. -/
theorem eval_spliceEncryptedBit_zero (n : ℕ) (pk bits : List Bool) (cut : ℕ)
    (hcut : cut < bits.length) :
    ProbComp.eval (do
      let challenge ← E.encrypt n pk false
      E.spliceEncryptedBit n pk cut (bits.drop (cut + 1)) challenge) =
        ProbComp.eval (E.encryptBitsHybrid n pk bits (cut + 1)) := by
  simpa only [spliceEncryptedBit, encryptBits, encryptBitsHybrid,
    Nat.min_eq_left (Nat.succ_le_iff.mpr hcut), List.replicate_succ',
    List.append_assoc, List.singleton_append] using
    ProbComp.eval_mapM_splice (E.encrypt n pk) (List.replicate cut false)
      false (bits.drop (cut + 1))

end Cslib.Crypto.Homomorphic.Scheme
