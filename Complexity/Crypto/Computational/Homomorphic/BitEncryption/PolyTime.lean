/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.BitEncryption
public import Complexity.Crypto.Computational.Homomorphic.Efficiency
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PPT

/-!
# Native runtime of bit-encryption hybrids

The certificates construct the zero prefix, encrypt the surrounding words, and copy the supplied
challenge ciphertext into its final position. All supplied data and every output ciphertext are
charged. No semantic correctness or width assumption is needed.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_encryptBitsHybrid`: encrypt the actual mixed word.
* `Cslib.Crypto.Homomorphic.Scheme.isPPTOn_spliceEncryptedBit`: insert an encrypted challenge
  between independently encrypted surrounding words.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

variable {E : Scheme}
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {α : Type} {input : α ↪ List Bool} {n cut before : α → ℕ}
  {pk bits after challenge : α → List Bool}

include hencrypt

/-- Encrypt the mixed word, preserving its length even when the unary cut exceeds it. -/
@[fun_prop]
theorem isPPTOn_encryptBitsHybrid
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hcut : ComputableInPolyTime cut input encUnary) :
    IsPPTOn input (encList encBits)
      (fun a => E.encryptBitsHybrid (n a) (pk a) (bits a) (cut a)) := by
  apply isPPTOn_encryptBits hencrypt hn hpk
  fun_prop

/-- Copy the full supplied ciphertext between independently encrypted zero and original words. -/
@[fun_prop]
theorem isPPTOn_spliceEncryptedBit
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbefore : ComputableInPolyTime before input encUnary)
    (hafter : ComputableInPolyTime after input encBits)
    (hchallenge : ComputableInPolyTime challenge input encBits) :
    IsPPTOn input (encList encBits)
      (fun a => E.spliceEncryptedBit (n a) (pk a) (before a) (after a) (challenge a)) := by
  have hfront := isPPTOn_encryptBits hencrypt hn hpk
    (show ComputableInPolyTime
      (fun a => List.replicate (before a) false) input encBits by fun_prop)
  have hback := isPPTOn_encryptBits hencrypt hn hpk hafter
  unfold spliceEncryptedBit
  ppt

end Cslib.Crypto.Homomorphic.Scheme
