/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.FixedKey.Encoding
public import CslibFrontier.Crypto.Computational.Homomorphic.Evaluation

/-!
# Fixed-key homomorphic bootstrapping

Generate one base key and publish encryptions of its secret bits under the same public key.
Every compiled circuit layer reuses this artifact. The private key and ciphertext representation
remain those of the base scheme: no tag, depth budget or key transition is needed.

Evaluation accepts every finite De Morgan circuit, and all algorithms are total on their raw
inputs. Decryption executes the actual decryption circuit on padded or truncated input. The
correctness and native runtime theorems are separate; the self-encrypted secret requires an
explicit circular-security assumption in the security development.

## Main definitions

* `Cslib.Crypto.Homomorphic.FixedKey.keyGen`: sample one key and its self-encrypted secret.
* `Cslib.Crypto.Homomorphic.FixedKey.evaluateCircuit`: compile and evaluate under the same key.
* `Cslib.Crypto.Homomorphic.FixedKey.scheme`: the actual construction for every finite circuit.

## Main results

* `Cslib.Crypto.Homomorphic.FixedKey.mem_support_keyGen_iff`: exact supported key artifacts.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, the self-loop
  construction][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Circuits Circuits.Boolean

/-- Sample one supported key and encrypt every secret bit under its own public key. -/
def keyGen (E : Scheme) (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let keys ← E.keyGen n
  let encryptedKey ← E.encryptBits n keys.1 keys.2
  pure (encPublicKey (keys.1, encryptedKey), keys.2)

/-- Decode the public artifact and use ordinary base encryption, without adding a tag. -/
def encrypt (E : Scheme) (n : ℕ) (pk : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  E.encrypt n (publicKeyDecoder.decode pk).1 bit

/-- Every supported serialized artifact comes from one actual key sample and supported
pointwise encryptions of that same key's secret. -/
theorem mem_support_keyGen_iff (E : Scheme) (n : ℕ) (output : List Bool × List Bool) :
    output ∈ (ProbComp.eval (keyGen E n)).support ↔
      ∃ keys encryptedKey, keys ∈ (ProbComp.eval (E.keyGen n)).support ∧
        E.FreshInputs n keys.1 keys.2 encryptedKey ∧
        output = (encPublicKey (keys.1, encryptedKey), keys.2) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, E.mem_support_encryptBits_iff]
  aesop

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Execute the decryption circuit on every input word, padding or truncating as necessary. -/
def decrypt (n : ℕ) (sk ciphertext : List Bool) : Bool :=
  (D.circuit n).eval interpretation
    (BitString.ofList (secretWidth n + ciphertextWidth n) (sk ++ ciphertext)) 0

/-- Compile arbitrary raw code and reuse the same public key and encrypted secret at each
scheduled layer. The repetition count is computed from the actual code. -/
def evaluateCircuit (n : ℕ) (pk : List Bool) (encryptedKey inputs : List (List Bool))
    (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) : ProbComp (List (List Bool)) :=
  let count := 2 * depthCode inputCount code
  Scheme.evaluateCircuit D n (List.replicate count pk) (List.replicate count encryptedKey)
    inputs inputCount code

/-- Evaluate a finite single-output circuit under the one serialized public artifact. -/
def evaluate (n : ℕ) (pk : List Bool) (c : Σ m, Circuit signature m 1)
    (inputs : List (List Bool)) : ProbComp (List Bool) :=
  let artifact := publicKeyDecoder.decode pk
  (fun outputs => outputs.headD []) <$>
    evaluateCircuit D n artifact.1 artifact.2 inputs c.1 c.2.code

/-- Fixed-key bootstrapping permits every finite Boolean circuit. Correctness, uniform
efficiency and circular-security hypotheses are not bundled into the algorithms. -/
def scheme : Scheme where
  keyGen := keyGen E
  encrypt := encrypt E
  decrypt := decrypt D
  evaluate := evaluate D
  permitted _ _ := True

end Cslib.Crypto.Homomorphic.FixedKey
