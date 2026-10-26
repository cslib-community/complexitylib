/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Basic
import Mathlib.Data.List.GetD

/-!
# Correctness of fixed-key homomorphic evaluation

The same supported base key and self-encrypted secret can be reused at every compiled layer.
The proof requires pointwise supported secret-bit encryptions, not independent copies of their
randomness. Inputs need only have the base ciphertext width and the desired decryption; this
includes outputs of previous evaluations. Every finite circuit preserves the same key and exact
ciphertext width.

GHV is cited for the multi-hop notion (paraphrase: evaluation can be applied to its own outputs)
[GentryHaleviVaikuntanathan2010], which `evaluate_twoHop_spec` instantiates for the fixed-key
scheme evaluator itself.

## Main results

* `Cslib.Crypto.Homomorphic.FixedKey.encryptedWires_evaluateCircuit`: arbitrary circuit outputs
  retain their plaintexts and width under the same key.
* `Cslib.Crypto.Homomorphic.FixedKey.evaluate_spec`: the constructed evaluator accepts earlier
  evaluated ciphertexts with the correct width and decryption.
* `Cslib.Crypto.Homomorphic.FixedKey.encryptedWires_of_evaluate`: outputs of pointwise fixed-key
  evaluations again satisfy the wire invariant and can be fed into further evaluations.
* `Cslib.Crypto.Homomorphic.FixedKey.evaluate_twoHop_spec`: two-hop fixed-key evaluation produces
  a base-width ciphertext that decrypts to the composed circuit value.
* `Cslib.Crypto.Homomorphic.FixedKey.correct`: perfect correctness for every finite circuit.
* `Cslib.Crypto.Homomorphic.FixedKey.fixedWidth`: unchanged secret and ciphertext widths.
* `Cslib.Crypto.Homomorphic.FixedKey.decryptionCircuits`: reuse the actual decryption circuit.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, pp. 171--172,
  the self-loop construction][Gentry2009]
* [C. Gentry, S. Halevi, and V. Vaikuntanathan, *$i$-Hop Homomorphic Encryption and
  Rerandomizable Yao Circuits*][GentryHaleviVaikuntanathan2010]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Circuits Circuits.Boolean

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Executing the decryption circuit agrees with base decryption on every well-sized word. -/
theorem decrypt_eq (n : ℕ) (sk ciphertext : List Bool)
    (hsk : sk.length = secretWidth n) (hc : ciphertext.length = ciphertextWidth n) :
    decrypt D n sk ciphertext = E.decrypt n sk ciphertext :=
  D.correct n sk ciphertext hsk hc

/-- On the unchanged secret and ciphertext representation, both schemes have the same
well-sized encrypted-wire relation. No freshness hypothesis is needed. -/
theorem encryptedWires_iff (n : ℕ) (sk : List Bool) (hsk : sk.length = secretWidth n)
    (bits : List Bool) (inputs : List (List Bool)) :
    (scheme D).EncryptedWires ciphertextWidth n sk bits inputs ↔
      E.EncryptedWires ciphertextWidth n sk bits inputs := by
  constructor <;> intro h <;> apply h.imp <;> intro bit ciphertext hc
  · exact ⟨hc.1, (decrypt_eq D n sk ciphertext hsk hc.1).symm.trans hc.2⟩
  · exact ⟨hc.1, (decrypt_eq D n sk ciphertext hsk hc.1).trans hc.2⟩

/-- Repeating one supported key and its self-encrypted secret evaluates any finite circuit.
The starting wires may already have been evaluated; output selection also handles depth zero. -/
theorem encryptedWires_evaluateCircuit (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (encryptedKey : List (List Bool)) (hlink : E.FreshInputs n keys.1 keys.2 encryptedKey)
    {inputCount outputCount : ℕ} (c : Circuit signature inputCount outputCount)
    (x : Fin inputCount → Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n keys.2 (List.ofFn x) inputs)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateCircuit D n keys.1 encryptedKey inputs inputCount c.code)).support) :
    E.EncryptedWires ciphertextWidth n keys.2 (List.ofFn (c.eval interpretation x)) outputs := by
  have hlinks (count : ℕ) : E.ValidLinks n (List.replicate (count + 1) keys)
      (List.replicate count encryptedKey) := by
    induction count with
    | zero => simp [Scheme.ValidLinks]
    | succ count ih =>
      simp only [Scheme.ValidLinks, List.replicate_succ, List.tail_cons,
        List.zip_cons_cons] at ih ⊢
      exact .cons hlink ih
  simp only [evaluateCircuit, depthCode_code] at houtputs
  have h := Scheme.encryptedWires_evaluateCircuit D hE hwidth hD n
    (List.replicate (2 * c.depth + 1) keys) (List.replicate (2 * c.depth) encryptedKey) c
    (by simp) (by
      intro key hkey
      obtain rfl := List.eq_of_mem_replicate hkey
      exact hkeys) (hlinks _) x inputs
    (by simpa only [List.getD_replicate keys (Nat.zero_lt_succ _)] using hinputs)
    outputs (by
      simpa only [List.replicate_succ, List.tail_cons, List.map_replicate] using houtputs)
  simpa only [List.getD_replicate keys (Nat.lt_succ_self _)] using h

/-- Fresh fixed-key encryptions retain the exact base width and decrypt under the base secret. -/
theorem encrypt_spec (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D).keyGen n)).support)
    (bit : Bool) (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval ((scheme D).encrypt n keys.1 bit)).support) :
    ciphertext.length = ciphertextWidth n ∧ (scheme D).decrypt n keys.2 ciphertext = bit := by
  obtain ⟨base, encryptedKey, hbase, _, rfl⟩ := (mem_support_keyGen_iff E n keys).1 hkeys
  change ciphertext ∈ (ProbComp.eval (encrypt E n (encPublicKey _) bit)).support at hc
  simp only [encrypt, publicKeyDecoder_decode_enc] at hc
  have hlength := hwidth.encrypt_length n base hbase bit ciphertext hc
  refine ⟨hlength, ?_⟩
  change decrypt D n base.2 ciphertext = bit
  rw [decrypt_eq D n base.2 ciphertext (hwidth.secret_length n base hbase) hlength]
  exact hE.decrypt_encrypt n base hbase bit ciphertext hc

/-- Fresh inputs satisfy the constructed scheme's stronger wire invariant. -/
theorem freshInputs_encryptedWires (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) {n : ℕ}
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval ((scheme D).keyGen n)).support)
    {bits : List Bool} {inputs : List (List Bool)}
    (hinputs : (scheme D).FreshInputs n keys.1 bits inputs) :
    (scheme D).EncryptedWires ciphertextWidth n keys.2 bits inputs :=
  hinputs.imp fun bit ciphertext hc => encrypt_spec D hE hwidth n keys hkeys bit ciphertext hc

/-- Every supported evaluator result has the exact base width and correct decryption under
the same secret key. The inputs may be prior evaluation outputs; they need not be fresh. -/
theorem evaluate_spec (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D).keyGen n)).support)
    (c : Σ m, Circuit signature m 1) (bits : List Bool) (inputs : List (List Bool))
    (hbits : bits.length = c.1)
    (hinputs : (scheme D).EncryptedWires ciphertextWidth n keys.2 bits inputs)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval ((scheme D).evaluate n keys.1 c inputs)).support) :
    ciphertext.length = ciphertextWidth n ∧
      (scheme D).decrypt n keys.2 ciphertext =
        c.2.eval interpretation (BitString.ofList c.1 bits) 0 := by
  obtain ⟨base, encryptedKey, hbase, hlink, rfl⟩ := (mem_support_keyGen_iff E n keys).1 hkeys
  have hsk := hwidth.secret_length n base hbase
  have hin := (encryptedWires_iff D n base.2 hsk bits inputs).1 hinputs
  change ciphertext ∈ (ProbComp.eval (evaluate D n (encPublicKey _) c inputs)).support at hc
  rw [evaluate, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨row, hrow, rfl⟩ := hc
  simp only [publicKeyDecoder_decode_enc] at hrow
  have h := encryptedWires_evaluateCircuit D hE hwidth hD n base hbase encryptedKey hlink c.2
    (BitString.ofList c.1 bits) inputs
    (by simpa only [BitString.ofFn_ofList hbits] using hin) row hrow
  have hout := h.getD (i := 0) (by simp)
  have hlength : (row.headD []).length = ciphertextWidth n := by
    simpa only [List.headD_eq_getD] using hout.1
  refine ⟨hlength, ?_⟩
  change decrypt D n base.2 (row.headD []) = _
  rw [decrypt_eq D n base.2 (row.headD []) hsk hlength]
  rw [List.headD_eq_getD]
  simpa using hout.2

/-- Outputs of pointwise fixed-key evaluations again satisfy the wire invariant under the same
secret key, so they can be fed into subsequent homomorphic evaluations. -/
theorem encryptedWires_of_evaluate (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    {n : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval ((scheme D).keyGen n)).support)
    {midBits : List Bool} {mids : List (List Bool)}
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          bits.length = c.1 ∧
            (scheme D).EncryptedWires ciphertextWidth n keys.2 bits inputs ∧
            mid ∈ (ProbComp.eval ((scheme D).evaluate n keys.1 c inputs)).support ∧
            c.2.eval interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids) :
    (scheme D).EncryptedWires ciphertextWidth n keys.2 midBits mids :=
  hmids.imp fun _ _ ⟨c, bits, inputs, hbits, hinputs, hmid, heval⟩ => by
    have hspec := evaluate_spec D hE hwidth hD n keys hkeys c bits inputs hbits hinputs _ hmid
    exact ⟨hspec.1, hspec.2.trans heval⟩

/-- Two-hop fixed-key evaluation: feeding outputs of first-hop circuit evaluations into an outer
circuit evaluation retains the base ciphertext width and decrypts to the composed circuit value. -/
theorem evaluate_twoHop_spec (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D).keyGen n)).support)
    (outer : Σ m, Circuit signature m 1) (midBits : List Bool) (mids : List (List Bool))
    (hmidBits : midBits.length = outer.1)
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          bits.length = c.1 ∧
            (scheme D).EncryptedWires ciphertextWidth n keys.2 bits inputs ∧
            mid ∈ (ProbComp.eval ((scheme D).evaluate n keys.1 c inputs)).support ∧
            c.2.eval interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval ((scheme D).evaluate n keys.1 outer mids)).support) :
    ciphertext.length = ciphertextWidth n ∧
      (scheme D).decrypt n keys.2 ciphertext =
        outer.2.eval interpretation (BitString.ofList outer.1 midBits) 0 :=
  evaluate_spec D hE hwidth hD n keys hkeys outer midBits mids hmidBits
    (encryptedWires_of_evaluate D hE hwidth hD hkeys hmids) ciphertext hc

/-- Actual bootstrapping constructs a correct scheme permitting every finite Boolean circuit. -/
theorem correct (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) : (scheme D).Correct where
  decrypt_encrypt n keys hkeys bit ciphertext hc :=
    (encrypt_spec D hE hwidth n keys hkeys bit ciphertext hc).2
  decrypt_evaluate n keys hkeys c _ bits inputs hbits hinputs ciphertext hc :=
    (evaluate_spec D hE hwidth hD n keys hkeys c bits inputs hbits
      (freshInputs_encryptedWires D hE hwidth hkeys hinputs) ciphertext hc).2

/-- Secret keys and all valid ciphertexts retain exactly the base widths, independently of
the evaluated circuit and any previous sequence of evaluations. -/
theorem fixedWidth (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) : (scheme D).FixedWidth secretWidth ciphertextWidth where
  secret_length n keys hkeys := by
    obtain ⟨base, encryptedKey, hbase, _, rfl⟩ := (mem_support_keyGen_iff E n keys).1 hkeys
    exact hwidth.secret_length n base hbase
  encrypt_length n keys hkeys bit ciphertext hc :=
    (encrypt_spec D hE hwidth n keys hkeys bit ciphertext hc).1
  evaluate_length n keys hkeys c _ bits inputs hbits hinputs ciphertext hc :=
    (evaluate_spec D hE hwidth hD n keys hkeys c bits inputs hbits
      (freshInputs_encryptedWires D hE hwidth hkeys hinputs) ciphertext hc).1

/-- The constructed scheme executes the same decryption circuit, including on malformed data. -/
def decryptionCircuits : DecryptionCircuits (scheme D) secretWidth ciphertextWidth where
  circuit := D.circuit
  correct _ _ _ _ _ := rfl

end Cslib.Crypto.Homomorphic.FixedKey
