/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Layered.Correctness
import Complexity.Crypto.Computational.Homomorphic.Layered.PolyTime
import Complexity.Crypto.Computational.Homomorphic.KeyChain.PolyTime
import ComplexityTests.Crypto.HomomorphicExample

/-!
The tagged example rejects evaluated inputs, so these regressions exercise actual refresh at
every transition. The sampled keys may repeat: the chain below is `false → true → false`.
No security property is claimed for either test scheme.
-/

namespace ComplexityTests.HomomorphicLayered

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample Boolean.Layered

private def keys : List (List Bool × List Bool) :=
  [([false], [false]), ([true], [true]), ([false], [false])]

private def links : List (List (List Bool)) := [[[true, false]], [[true, false]]]

private def layers : List (List Node) :=
  [[.nand 0 0, .copy 0, .const true], [.nand 0 1, .copy 1, .nand 1 1]]

private theorem eval_augmentedXor (x : Fin 6 → Bool) :
    (augmentNand xorCircuit).eval Boolean.interpretation x 0 =
      !((x 1 ^^ x 0) && (x 4 ^^ x 3)) := by
  rw [augmentNand, Circuit.eval_comp, Boolean.eval_nandCircuit, Circuit.eval_parallel]
  change Bool.not ((xorCircuit.eval Boolean.interpretation (x ∘ Fin.castAdd 3) 0) &&
    (xorCircuit.eval Boolean.interpretation (x ∘ Fin.natAdd 3) 0)) = _
  rw [eval_xorCircuit, eval_xorCircuit]
  rfl

private theorem chain_supported :
    (keys, links) ∈ (ProbComp.eval (tagged.generateKeyChain 0 2)).support := by
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro key hk
    simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals exact (keys_supported 0 _).2 ⟨_, rfl⟩
  · simp [Scheme.ValidLinks, Scheme.FreshInputs, keys, links, tagged]

-- Two transitions, independently of the six scheduled nodes; one key value repeats.
example : keys.length = 3 ∧ links.length = 2 :=
  tagged.lengths_of_mem_support_generateKeyChain chain_supported

-- The invariant applies to every output of this actual supported key chain.
example (outputs : List (List Bool))
    (h : outputs ∈ (ProbComp.eval
      (Scheme.evaluateLayers decryptionCircuits 0 [[true], [false]] links
        [[true, false]] layers)).support) :
    tagged.EncryptedWires (fun _ => 2) 0 [false] [true, true, false] outputs := by
  have hchain : (keys, links) ∈
      (ProbComp.eval (tagged.generateKeyChain 0 layers.length)).support := chain_supported
  exact Scheme.encryptedWires_evaluateLayers_of_generatedChain decryptionCircuits
    tagged_correct tagged_width tagged_bootstrappable 0 keys links layers hchain
    [true] [[true, false]] (by simp [Scheme.FreshInputs, keys, tagged])
    (by simp [WellFormed, Node.Valid, layers]) outputs h

-- The first layer mixes refresh and fresh constants under the new public key. Tags expose
-- the distinction: copies and NANDs are evaluated outputs, while constants are fresh.
example : ProbComp.eval (Scheme.evaluateLayer decryptionCircuits 0 [true] [[true, false]]
    [[true, false]] [.nand 0 0, .copy 0, .const true]) =
    PMF.pure [[true, true], [false, true], [false, false]] := by
  simp [Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh, Scheme.refreshNand,
    Scheme.encryptBits, tagged, evaluatedBit, decryptionCircuits, eval_augmentedXor,
    eval_xorCircuit, decode, BitString.ofList]

-- The second transition must accept the previous evaluation tags. Shared/repeated indices
-- are read from the previous layer, and all final wires retain fixed width.
example : ProbComp.eval (Scheme.evaluateLayers decryptionCircuits 0 [[true], [false]] links
    [[true, false]] layers) = PMF.pure [[true, true], [true, true], [false, true]] := by
  simp [Scheme.evaluateLayers, Scheme.evaluateLayerStep, OracleComp.iterate,
    Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh, Scheme.refreshNand,
    Scheme.encryptBits, layers, links, tagged, evaluatedBit, decryptionCircuits,
    eval_augmentedXor, eval_xorCircuit, decode, BitString.ofList]

-- No layers perform no key transition and preserve the input ciphertexts exactly.
example (inputs : List (List Bool)) :
    Scheme.evaluateLayers decryptionCircuits 0 [] [] inputs [] = pure inputs := by
  simp [Scheme.evaluateLayers]

example : (([([true], [true])], [])) ∈
    (ProbComp.eval (tagged.generateKeyChain 0 0)).support := by
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, by simp [Scheme.ValidLinks]⟩
  intro key hk
  obtain rfl := List.mem_singleton.1 hk
  exact (keys_supported 0 _).2 ⟨true, rfl⟩

-- Zero inputs and an empty first layer still allow constants in a later layer.
example : ProbComp.eval (Scheme.evaluateLayers decryptionCircuits 0 [[true], [false]] links
    [] [[], [.const false, .const true]]) = PMF.pure [[false, false], [true, false]] := by
  simp [Scheme.evaluateLayers, Scheme.evaluateLayerStep, OracleComp.iterate,
    Scheme.evaluateLayer, Scheme.evaluateNode, tagged]

-- A malformed index is not a correctness case, but its output still has an unconditional cap.
example (result : List Bool)
    (h : result ∈ (ProbComp.eval
      (Scheme.evaluateNode decryptionCircuits 0 [] [] [] (.copy (2 ^ 100)))).support) :
    result.length ≤ 3 := Scheme.length_evaluateNode_le decryptionCircuits 0 [] [] [] _ result h

-- For this sampler-only fixture the ciphertext records its plaintext and target public key.
-- Unlike XOR, the representation makes reversing the link direction observably wrong.
private noncomputable def labelled : Scheme :=
  { tagged with encrypt := fun _ pk bit => pure (bit :: pk) }

private def labelledCircuits : DecryptionCircuits labelled (fun _ => 1) (fun _ => 2) where
  circuit := decryptionCircuits.circuit
  correct := decryptionCircuits.correct

example : ProbComp.eval (labelled.encryptKeyLinks 0
    [([false], [false]), ([true], [true])]) = PMF.pure [[[false, true]]] := by
  simp [Scheme.encryptKeyLinks, Scheme.encryptBits, labelled]

example : ProbComp.eval (labelled.encryptBits 0 [false] [true]) = PMF.pure [[true, false]] := by
  simp [Scheme.encryptBits, labelled]

-- This malformed public key produces an oversized raw encryption. Even the constant branch
-- must actually truncate it, without a correctness or fixed-width premise for labelled.
example : ProbComp.eval (Scheme.evaluateNode labelledCircuits 0 [true, false, true, true]
    [] [] (.const false)) = PMF.pure [false, true, false] := by
  simp [Scheme.evaluateNode, labelled]

-- The plaintext and ciphertext defaults disagree, so a validity premise is essential.
example : Node.eval [] (.copy 0) = false ∧ tagged.decrypt 0 [true] [] = true := ⟨rfl, rfl⟩

-- The actual sampler inhabits all of its native efficiency premises.
example : IsPPTOn (encPair encUnary encUnary)
    (encPair (encList (encPair encBits encBits)) (encList (encList encBits)))
    (fun p => tagged.generateKeyChain p.1 p.2) := by
  apply Scheme.isPPTOn_generateKeyChain keyGen_ppt encrypt_ppt
  all_goals fun_prop

-- The evaluator certificate covers every complete public input, including wrong chain lengths,
-- invalid wire indices, and initial ciphertexts whose widths are not those of the scheme.
example : IsPPTOn
    (encPair encUnary (encPair (encList encBits) (encPair (encList (encList encBits))
      (encPair (encList encBits) (encList (encList encNode)))))) (encList encBits)
    (fun p => Scheme.evaluateLayers decryptionCircuits p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2) := by
  apply Scheme.isPPTOn_evaluateLayers decryptionCircuits encrypt_ppt evaluate_ppt
    circuits_poly
  all_goals fun_prop

end ComplexityTests.HomomorphicLayered
