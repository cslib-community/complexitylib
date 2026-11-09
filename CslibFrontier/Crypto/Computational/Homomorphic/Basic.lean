/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Foundations.Data.BitString.List
public import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Languages.Probabilistic.Traverse

/-!
# Homomorphic encryption on bit strings

This module records the algorithms and perfect correctness of bit-encryption schemes with a
specified family of permitted Boolean circuits, following [Gentry2009, Definitions 1 and 5].
Algorithms are terminating probabilistic programs. Uniform efficiency and semantic security
are separate obligations; neither follows from this interface or its correctness property.

Homomorphic correctness is required on **pointwise supported fresh encryptions**. Inputs may
share randomness or repeat a ciphertext, as happens when the same encrypted secret key is used
twice in an augmented decryption circuit. No independence hypothesis is imposed on these inputs.

`Scheme.FixedWidth` describes a padded representation whose ciphertext width depends only on
the security parameter. It asserts a representation bound, not that the width is polynomial.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme`: encryption algorithms and permitted circuits.
* `Cslib.Crypto.Homomorphic.Scheme.FreshInputs`: matching plaintexts and fresh ciphertexts.
* `Cslib.Crypto.Homomorphic.Scheme.Correct`: perfect encryption and evaluation correctness.
* `Cslib.Crypto.Homomorphic.Scheme.FixedWidth`: fixed secret-key and ciphertext widths.
* `Cslib.Crypto.Homomorphic.Scheme.encryptBits`: encrypt each bit of a public word.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.mem_support_encryptBits_iff`: the exact support of bitwise
  encryption, including the empty word.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Circuits

/-- Algorithms of a bit-encryption scheme, with a unary security parameter. `evaluate` receives
an actual Boolean circuit and an ordered list of ciphertexts. Correctness, uniform efficiency,
and security are separate properties. -/
structure Scheme where
  /-- Sample a public and secret key, in that order. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Encrypt one bit under a public key. -/
  encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)
  /-- Decrypt a ciphertext under a secret key. -/
  decrypt : ℕ → List Bool → List Bool → Bool
  /-- Evaluate a circuit on encrypted inputs; malformed input lists are allowed but have no
  correctness guarantee. -/
  evaluate : ℕ → List Bool → (Σ m, Circuit Boolean.signature m 1) →
    List (List Bool) → ProbComp (List Bool)
  /-- Circuits for which homomorphic correctness is guaranteed at a security parameter. -/
  permitted : ℕ → (Σ m, Circuit Boolean.signature m 1) → Prop

namespace Scheme

variable (E : Scheme)

/-- Each ciphertext is a supported fresh encryption of the corresponding plaintext bit.
The relation implies equal list lengths, and permits repeated ciphertexts. -/
def FreshInputs (n : ℕ) (pk : List Bool) (bits : List Bool) (inputs : List (List Bool)) : Prop :=
  List.Forall₂ (fun b c => c ∈ (ProbComp.eval (E.encrypt n pk b)).support) bits inputs

/-- Perfect correctness of encryption and evaluation of permitted circuits on fresh inputs.
The evaluator need not accept its own outputs as inputs: bootstrapping will derive that closure.
-/
structure Correct : Prop where
  /-- Fresh ciphertexts decrypt to the encrypted bit under every supported key pair. -/
  decrypt_encrypt : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
    ∀ b c, c ∈ (ProbComp.eval (E.encrypt n keys.1 b)).support →
      E.decrypt n keys.2 c = b
  /-- Permitted circuits evaluate correctly on any pointwise supported fresh encryptions. -/
  decrypt_evaluate : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
    ∀ C, E.permitted n C → ∀ bits inputs, bits.length = C.1 →
      E.FreshInputs n keys.1 bits inputs →
      ∀ c, c ∈ (ProbComp.eval (E.evaluate n keys.1 C inputs)).support →
        E.decrypt n keys.2 c = C.2.eval Boolean.interpretation (BitString.ofList C.1 bits) 0

/-- A fixed-width representation for supported keys and ciphertexts. Both fresh encryption and
evaluation outputs have the same width, independent of circuit size and evaluation depth.
Polynomial bounds on these width functions are a separate efficiency obligation. -/
structure FixedWidth (secretWidth ciphertextWidth : ℕ → ℕ) : Prop where
  /-- Supported secret keys have the stated width. -/
  secret_length : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
    keys.2.length = secretWidth n
  /-- Supported fresh encryptions have the stated ciphertext width. -/
  encrypt_length : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
    ∀ b c, c ∈ (ProbComp.eval (E.encrypt n keys.1 b)).support →
      c.length = ciphertextWidth n
  /-- The base evaluator returns the same ciphertext width, even after a nontrivial circuit. -/
  evaluate_length : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
    ∀ C, E.permitted n C → ∀ bits inputs, bits.length = C.1 →
      E.FreshInputs n keys.1 bits inputs →
      ∀ c, c ∈ (ProbComp.eval (E.evaluate n keys.1 C inputs)).support →
        c.length = ciphertextWidth n

/-- Encrypt every bit of a public word using a fresh call to the base encryption algorithm. -/
def encryptBits (n : ℕ) (pk bits : List Bool) : ProbComp (List (List Bool)) :=
  bits.mapM (E.encrypt n pk)

/-- Bitwise encryption has exactly the pointwise fresh-encryption support. -/
theorem mem_support_encryptBits_iff (n : ℕ) (pk bits : List Bool) (inputs : List (List Bool)) :
    inputs ∈ (ProbComp.eval (E.encryptBits n pk bits)).support ↔
      E.FreshInputs n pk bits inputs :=
  ProbComp.mem_support_mapM_iff (E.encrypt n pk) bits inputs

end Scheme

end Cslib.Crypto.Homomorphic
