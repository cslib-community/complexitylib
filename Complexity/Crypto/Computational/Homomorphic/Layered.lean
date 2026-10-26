/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered
public import Complexity.Crypto.Computational.Homomorphic.Refresh
public import Complexity.Languages.Probabilistic.Traverse
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Homomorphic evaluation of consecutive layers

Constants are encrypted under the target public key, copies are refreshed, and NANDs use the
augmented decryption circuit. Every output is truncated to the base decryption circuit's arity.
On valid executions truncation changes nothing; on malformed inputs it still bounds the next layer's
wire volume. This unconditional bound is needed for strict polynomial-time evaluation.

Only public keys and encrypted key links are runtime inputs. Secret keys appear in correctness
predicates, never in the evaluator. `EncryptedWires` pairs every plaintext with a ciphertext of
the required width and decryption, without asserting that intermediate ciphertexts are fresh.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.EncryptedWires`: the invariant between adjacent layers.
* `Cslib.Crypto.Homomorphic.Scheme.evaluateNode`: evaluate and bound a single node.
* `Cslib.Crypto.Homomorphic.Scheme.evaluateLayer`: traverse a layer with independent calls.
* `Cslib.Crypto.Homomorphic.Scheme.evaluateLayers`: the public bounded loop over all layers.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateLayer`: correct evaluation from the
  preceding key to the target key, including constants, copies and repeated inputs.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits.Boolean

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Pair the plaintext wires with ciphertexts of the right width and decryption. This includes
equality of wire counts, and makes no fresh-encryption assumption. -/
def EncryptedWires (E : Scheme) (ciphertextWidth : ℕ → ℕ) (n : ℕ) (sk : List Bool)
    (bits : List Bool) (inputs : List (List Bool)) : Prop :=
  List.Forall₂ (fun bit ciphertext =>
    ciphertext.length = ciphertextWidth n ∧ E.decrypt n sk ciphertext = bit) bits inputs

/-- A valid wire lookup preserves both width and decryption. -/
theorem EncryptedWires.getD {n : ℕ} {sk bits : List Bool} {inputs : List (List Bool)}
    (h : E.EncryptedWires ciphertextWidth n sk bits inputs) {i : ℕ} (hi : i < bits.length) :
    (inputs.getD i []).length = ciphertextWidth n ∧
      E.decrypt n sk (inputs.getD i []) = bits.getD i false :=
  List.Forall₂.getD h hi false []

/-- Selecting valid ciphertext wires preserves their width and plaintexts, with no key change.
Output order and repetitions are exactly those of the index list. -/
theorem EncryptedWires.select {n : ℕ} {sk bits : List Bool} {inputs : List (List Bool)}
    (h : E.EncryptedWires ciphertextWidth n sk bits inputs) {outputs : List ℕ}
    (houtputs : ∀ i ∈ outputs, i < bits.length) :
    E.EncryptedWires ciphertextWidth n sk (Layered.select bits outputs)
      (outputs.map (inputs.getD · [])) := by
  simp only [EncryptedWires, Layered.select, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff, List.forall₂_same]
  exact fun i hi => h.getD (houtputs i hi)

/-- Fresh encryptions initialize the stronger invariant used after evaluation. -/
theorem FreshInputs.encryptedWires (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    {bits : List Bool} {inputs : List (List Bool)} (h : E.FreshInputs n keys.1 bits inputs) :
    E.EncryptedWires ciphertextWidth n keys.2 bits inputs :=
  h.imp fun bit ciphertext hc =>
    ⟨hwidth.encrypt_length n keys hkeys bit ciphertext hc,
      hE.decrypt_encrypt n keys hkeys bit ciphertext hc⟩

/-- Truncation at the decryption circuit's input arity leaves every valid ciphertext unchanged.
The arity can be read from the generated circuit without computing the width functions. -/
theorem take_decryptionArity_eq {n : ℕ} {ciphertext : List Bool}
    (h : ciphertext.length = ciphertextWidth n) :
    ciphertext.take (secretWidth n + ciphertextWidth n) = ciphertext :=
  List.take_of_length_le (by omega)

/-- Evaluate one node under the target public key, then bound its result on every input. -/
def evaluateNode (n : ℕ) (pk : List Bool) (encryptedKey inputs : List (List Bool))
    (node : Layered.Node) : ProbComp (List Bool) :=
  (List.take (secretWidth n + ciphertextWidth n)) <$>
    match node with
    | .const bit => E.encrypt n pk bit
    | .copy i => refresh D n pk encryptedKey (inputs.getD i [])
    | .nand i j => refreshNand D n pk encryptedKey (inputs.getD i []) (inputs.getD j [])

/-- Execute each node using the same preceding layer and encrypted secret key. -/
def evaluateLayer (n : ℕ) (pk : List Bool) (encryptedKey inputs : List (List Bool))
    (layer : List Layered.Node) : ProbComp (List (List Bool)) :=
  layer.mapM (evaluateNode D n pk encryptedKey inputs)

/-- One level of the public loop. The state stores the next level and its current wires.
The public-key list starts at the first target key, after the input-encryption key. -/
def evaluateLayerStep (n : ℕ) (publicKeys : List (List Bool))
    (encryptedKeys : List (List (List Bool))) (layers : List (List Layered.Node))
    (state : ℕ × List (List Bool)) : ProbComp (ℕ × List (List Bool)) :=
  (fun outputs => (state.1 + 1, outputs)) <$>
    evaluateLayer D n (publicKeys.getD state.1 []) (encryptedKeys.getD state.1 [])
      state.2 (layers.getD state.1 [])

/-- Evaluate all scheduled layers. Missing public data uses empty defaults; correctness requires
a valid chain, while the efficiency certificate covers these malformed inputs as well. -/
def evaluateLayers (n : ℕ) (publicKeys : List (List Bool))
    (encryptedKeys : List (List (List Bool))) (inputs : List (List Bool))
    (layers : List (List Layered.Node)) : ProbComp (List (List Bool)) :=
  Prod.snd <$> OracleComp.iterate layers.length
    (evaluateLayerStep D n publicKeys encryptedKeys layers) (0, inputs)

/-- A node's output is bounded even with invalid wires, keys, or encrypted key links. -/
theorem length_evaluateNode_le (n : ℕ) (pk : List Bool) (encryptedKey inputs : List (List Bool))
    (node : Layered.Node) (result : List Bool)
    (h : result ∈ (ProbComp.eval (evaluateNode D n pk encryptedKey inputs node)).support) :
    result.length ≤ secretWidth n + ciphertextWidth n := by
  rw [evaluateNode.eq_def, ProbComp.eval_map, PMF.mem_support_map_iff] at h
  obtain ⟨raw, _, rfl⟩ := h
  exact List.length_take_le _ _

/-- Every execution has the scheduled number of output wires, each bounded by the decryption
circuit's arity. No correctness, validity, or key-generation premise is used. -/
theorem evaluateLayer_bounds (n : ℕ) (pk : List Bool) (encryptedKey inputs : List (List Bool))
    (layer : List Layered.Node) (outputs : List (List Bool))
    (h : outputs ∈ (ProbComp.eval (evaluateLayer D n pk encryptedKey inputs layer)).support) :
    outputs.length = layer.length ∧
      ∀ ciphertext ∈ outputs, ciphertext.length ≤ secretWidth n + ciphertextWidth n := by
  rw [evaluateLayer, ProbComp.mem_support_mapM_iff] at h
  refine ⟨h.length_eq.symm, ?_⟩
  induction h with
  | nil => simp
  | @cons node output layer outputs hnode _ ih =>
    intro ciphertext hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact length_evaluateNode_le D n pk encryptedKey inputs node ciphertext hnode
    · exact ih ciphertext hc

/-- Valid nodes move the invariant to the target key. No intermediate freshness is needed. -/
theorem evaluateNode_correct (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk : List Bool) (hsk : sk.length = secretWidth n)
    (encryptedKey : List (List Bool)) (hek : E.FreshInputs n keys.1 sk encryptedKey)
    (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n sk bits inputs)
    (node : Layered.Node) (hnode : node.Valid bits.length) (result : List Bool)
    (hresult : result ∈
      (ProbComp.eval (evaluateNode D n keys.1 encryptedKey inputs node)).support) :
    result.length = ciphertextWidth n ∧ E.decrypt n keys.2 result = node.eval bits := by
  rw [evaluateNode.eq_def, ProbComp.eval_map, PMF.mem_support_map_iff] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  suffices hrawSpec : raw.length = ciphertextWidth n ∧
      E.decrypt n keys.2 raw = node.eval bits by
    simpa only [take_decryptionArity_eq hrawSpec.1] using hrawSpec
  cases node with
  | const bit =>
    exact ⟨hwidth.encrypt_length n keys hkeys bit raw hraw,
      hE.decrypt_encrypt n keys hkeys bit raw hraw⟩
  | copy i =>
    have hi := hinputs.getD hnode
    exact ⟨length_refresh D hwidth hD n keys hkeys sk _ hsk hi.1 encryptedKey hek raw hraw,
      (decrypt_refresh D hE hD n keys hkeys sk _ hsk hi.1 encryptedKey hek raw hraw).trans hi.2⟩
  | nand i j =>
    have hi := hinputs.getD hnode.1
    have hj := hinputs.getD hnode.2
    refine ⟨length_refreshNand D hwidth hD n keys hkeys sk _ _ hsk hi.1 hj.1
      encryptedKey hek raw hraw, ?_⟩
    simpa only [Layered.Node.eval, hi.2, hj.2] using
      decrypt_refreshNand D hE hD n keys hkeys sk _ _ hsk hi.1 hj.1
        encryptedKey hek raw hraw

/-- Evaluating a valid layer preserves the exact wire count, ciphertext width and plaintext
values under the next key. -/
theorem encryptedWires_evaluateLayer (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (E.keyGen n)).support)
    (sk : List Bool) (hsk : sk.length = secretWidth n)
    (encryptedKey : List (List Bool)) (hek : E.FreshInputs n keys.1 sk encryptedKey)
    (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n sk bits inputs)
    (layer : List Layered.Node) (hlayer : ∀ node ∈ layer, node.Valid bits.length)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateLayer D n keys.1 encryptedKey inputs layer)).support) :
    E.EncryptedWires ciphertextWidth n keys.2 (Layered.evalLayer bits layer) outputs := by
  rw [evaluateLayer, ProbComp.mem_support_mapM_iff] at houtputs
  rw [EncryptedWires, Layered.evalLayer, List.forall₂_map_left_iff]
  induction houtputs with
  | nil => exact .nil
  | @cons node output layer outputs hnode _ ih =>
    exact .cons (evaluateNode_correct D hE hwidth hD n keys hkeys sk hsk encryptedKey hek
      bits inputs hinputs node (hlayer node (by simp)) output hnode)
      (ih fun node hn => hlayer node (by simp [hn]))

end Cslib.Crypto.Homomorphic.Scheme
