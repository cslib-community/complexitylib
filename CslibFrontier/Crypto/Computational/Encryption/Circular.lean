/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# A single-key circular-security assumption

The public experiment samples one key pair and encrypts every secret-key bit under its own
public key, or encrypts the same number of zero bits. The complete vector and public key are
jointly visible. `CircularSecure` asserts computational indistinguishability of these two
serialized experiments against uniform native strict PPT tests.

For fixed supported secret width, this is a one-key, bitwise specialization of the real-versus-zero
KDM experiment of [Boneh, Halevi, Hamburg and Ostrovsky, Section 2.1]
[BonehHaleviHamburgOstrovsky2008]. The definition also permits varying supported lengths, in which
case the public vector reveals that length. It does not assert general adaptive KDM security.
Ordinary chosen-message security is a separate premise; neither definition mentions a derived
homomorphic scheme. The single public sample can be reused by efficient computations without
assuming independent copies of its contents.

## Main definitions

* `Cslib.Crypto.Encryption.encCircularPublicKey`: a public key and its encrypted secret vector.
* `Cslib.Crypto.Encryption.circularPublicKey`: the actual self-encryption or zero experiment.
* `Cslib.Crypto.Encryption.CircularSecure`: joint one-key self-encryption indistinguishability.

## References

* [D. Boneh, S. Halevi, M. Hamburg, R. Ostrovsky,
  *Circular-Secure Encryption from Decision Diffie-Hellman*][BonehHaleviHamburgOstrovsky2008],
  Section 2.1.
* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009], Section 2.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Turing.MultiTapeTM

/-- Encode the public key and the complete vector of encrypted key bits, with no plaintext
secret component. -/
def encCircularPublicKey : (List Bool × List (List Bool)) ↪ List Bool :=
  encPair encBits (encList encBits)

/-- Sample one key pair, then independently encrypt either every secret bit or equally many
zero bits under that same public key. The result retains their full joint distribution. -/
def circularPublicKey (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (real : Bool) (n : ℕ) : ProbComp (List Bool × List (List Bool)) := do
  let keys ← keyGen n
  let bits := if real then keys.2 else List.replicate keys.2.length false
  let encrypted ← bits.mapM (encrypt n keys.1)
  pure (keys.1, encrypted)

/-- The complete self-encryption vector is indistinguishable from equal-length zero
encryptions, jointly with its public key. This is an explicit additional assumption, not a
consequence of ordinary IND-CPA and not a security claim about a constructed output scheme. -/
def CircularSecure (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  ComputationallyIndistinguishable
    (fun n => (ProbComp.eval (circularPublicKey keyGen encrypt true n)).map encCircularPublicKey)
    (fun n => (ProbComp.eval (circularPublicKey keyGen encrypt false n)).map encCircularPublicKey)

end Cslib.Crypto.Encryption
