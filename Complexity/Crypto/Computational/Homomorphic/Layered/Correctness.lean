/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Layered
public import Complexity.Crypto.Computational.Homomorphic.KeyChain
import Mathlib.Data.List.GetD

/-!
# Correct evaluation along a generated key chain

The bounded evaluator implements every well-formed program in the consecutive-layer model.
Its invariant tracks the current level, the exact plaintext wire list and ciphertext widths.
There is one key transition per scheduled layer, regardless of its number of nodes.

The runtime receives the public projection of the target keys and encrypted links. The full
key-pair list is only a witness in these theorems. The final plaintexts decrypt with the last
secret key; fresh inputs use the first key. `Homomorphic.Evaluation` composes this theorem with
the ordinary-circuit compiler and output selection. `Homomorphic.Leveled.Correctness` packages
the endpoint distinction in a depth-budgeted scheme; security remains a separate obligation.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateLayers`: the complete loop preserves
  the layer invariant along a valid chain.
* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateLayers_of_generatedChain`: correctness
  for every supported key-chain sample and pointwise fresh input encryptions.
* `Cslib.Crypto.Homomorphic.Scheme.encryptedWires_evaluateLayers_drop`: evaluating a layer
  schedule starting at an arbitrary offset in a generated key chain.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2,
  pp. 171--172][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Circuits.Boolean

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Evaluate all layers along an acyclic key chain. Correctness requires valid references;
the public algorithm itself is defined on every input. The initial wires may already be
evaluated ciphertexts, provided that their width and decryption are correct. -/
theorem encryptedWires_evaluateLayers (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) (layers : List (List Layered.Node))
    (hcount : layers.length + 1 ≤ keys.length)
    (hkeys : ∀ key ∈ keys, key ∈ (ProbComp.eval (E.keyGen n)).support)
    (hlinks : E.ValidLinks n keys links) (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n (keys.getD 0 ([], [])).2 bits inputs)
    (hvalid : Layered.WellFormed bits.length layers) (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateLayers D n (keys.tail.map Prod.fst) links inputs layers)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD layers.length ([], [])).2
      (Layered.eval bits layers) outputs := by
  have hkey (i : ℕ) (hi : i ≤ layers.length) :
      keys.getD i ([], []) ∈ (ProbComp.eval (E.keyGen n)).support := by
    have hi' : i < keys.length := by omega
    exact hkeys _ (by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _)
  have hlinkCount : layers.length ≤ links.length := by
    have := hlinks.length_eq
    omega
  have hpk (i : ℕ) :
      (keys.tail.map Prod.fst).getD i [] = (keys.getD (i + 1) ([], [])).1 := by
    change (keys.tail.map Prod.fst).getD i (Prod.fst (([], []) : List Bool × List Bool)) = _
    rw [List.getD_map]
    cases keys <;> rfl
  rw [evaluateLayers, ProbComp.eval_map, PMF.mem_support_map_iff] at houtputs
  obtain ⟨state, hstate, rfl⟩ := houtputs
  have hrun := ProbComp.iterate_invariant layers.length
    (evaluateLayerStep D n (keys.tail.map Prod.fst) links layers) (0, inputs)
    (fun i state => state.1 = i ∧
      E.EncryptedWires ciphertextWidth n (keys.getD i ([], [])).2
        (Layered.eval bits (layers.take i)) state.2)
    ⟨rfl, hinputs⟩
    (by
      intro i hi state hinvariant next hnext
      rw [evaluateLayerStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
      obtain ⟨newWires, hnewWires, rfl⟩ := hnext
      rw [hinvariant.1, hpk] at hnewWires
      refine ⟨congrArg (· + 1) hinvariant.1, ?_⟩
      rw [Layered.eval_take_succ bits layers hi]
      exact encryptedWires_evaluateLayer D hE hwidth hD n (keys.getD (i + 1) ([], []))
        (hkey _ (by omega)) (keys.getD i ([], [])).2
        (hwidth.secret_length n _ (hkey i hi.le)) (links.getD i [])
        (hlinks.getD (by omega)) (Layered.eval bits (layers.take i)) state.2 hinvariant.2
        (layers.getD i []) (hvalid.valid_getD hi) newWires hnewWires)
    state hstate
  simpa only [List.take_length] using hrun.2

/-- The actual sampler supplies all key and link premises. Each fresh input is under the
initial key, and each final output decrypts under the key after the last scheduled layer. -/
theorem encryptedWires_evaluateLayers_of_generatedChain (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) (layers : List (List Layered.Node))
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n layers.length)).support)
    (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.FreshInputs n (keys.getD 0 ([], [])).1 bits inputs)
    (hvalid : Layered.WellFormed bits.length layers) (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateLayers D n (keys.tail.map Prod.fst) links inputs layers)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD layers.length ([], [])).2
      (Layered.eval bits layers) outputs := by
  obtain ⟨hcount, hkeys, hlinks⟩ :=
    (E.mem_support_generateKeyChain_iff n layers.length keys links).1 hchain
  have hzero : 0 < keys.length := by omega
  have hfirst := hkeys (keys.getD 0 ([], []))
    (by rw [List.getD_eq_getElem _ _ hzero]; exact List.getElem_mem _)
  exact encryptedWires_evaluateLayers D hE hwidth hD n keys links layers hcount.ge hkeys hlinks
    bits inputs (hinputs.encryptedWires hE hwidth hfirst) hvalid outputs houtputs

/-- Evaluate a layer schedule starting at index `start` in a generated key chain of total depth
`total`, advancing the wire invariant from key `start` to key `start + layers.length`. -/
theorem encryptedWires_evaluateLayers_drop (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Bootstrappable D)
    (n total start : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) (layers : List (List Layered.Node))
    (htotal : start + layers.length ≤ total)
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n total)).support)
    (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n (keys.getD start ([], [])).2 bits inputs)
    (hvalid : Layered.WellFormed bits.length layers) (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateLayers D n ((keys.map Prod.fst).tail.drop start)
        (links.drop start) inputs layers)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (start + layers.length) ([], [])).2
      (Layered.eval bits layers) outputs := by
  obtain ⟨hcount, hkeys, hlinks⟩ :=
    (E.mem_support_generateKeyChain_iff n total keys links).1 hchain
  have hpk :
      (keys.map Prod.fst).tail.drop start = (keys.drop start).tail.map Prod.fst := by
    cases keys <;> simp [List.map_drop]
  have hget0 : (keys.drop start).getD 0 ([], []) = keys.getD start ([], []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hgetEnd :
      (keys.drop start).getD layers.length ([], []) =
        keys.getD (start + layers.length) ([], []) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [hpk] at houtputs
  rw [← hgetEnd]
  exact encryptedWires_evaluateLayers D hE hwidth hD n (keys.drop start)
    (links.drop start) layers (by rw [List.length_drop]; omega)
    (fun k hk => hkeys k (List.mem_of_mem_drop hk)) (hlinks.drop start) bits inputs
    (by rw [hget0]; exact hinputs) hvalid outputs houtputs

end Cslib.Crypto.Homomorphic.Scheme
