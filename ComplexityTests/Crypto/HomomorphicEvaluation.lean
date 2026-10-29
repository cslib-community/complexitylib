/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Evaluation
import Complexity.Crypto.Computational.Homomorphic.Evaluation.PolyTime
import ComplexityTests.Crypto.HomomorphicExample

/-!
Ordinary De Morgan circuits are compiled and evaluated using the tagged scheme, whose evaluator
rejects evaluated inputs. The tests therefore exercise actual refresh across the two microlevels.
Depth-zero wiring permutes and duplicates ciphertexts under the unchanged initial key.
The fixture is explicitly insecure; these are correctness and runtime tests only.
-/

namespace ComplexityTests.HomomorphicEvaluation

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample Boolean.Layered

private def orCircuit : Circuit Boolean.signature 2 1 := Circuit.oneGate .or id

private def keys : List (List Bool × List Bool) :=
  [([false], [false]), ([true], [true]), ([false], [false])]

private def links : List (List (List Bool)) := [[[true, false]], [[true, false]]]

private theorem chain_supported :
    (keys, links) ∈ (ProbComp.eval (tagged.generateKeyChain 0 (2 * orCircuit.depth))).support := by
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨by simp [keys, orCircuit], ?_, ?_⟩
  · intro key hk
    simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals exact (keys_supported 0 _).2 ⟨_, rfl⟩
  · simp [Scheme.ValidLinks, Scheme.FreshInputs, keys, links, tagged]

-- The source has one OR gate. Compilation creates both negated intermediates and finishes
-- their NAND in the second layer, preserving the two original inputs and the shared gate slot.
example : compile 2 orCircuit.code =
    ([[.copy 0, .copy 1, .const false, .nand 0 0, .nand 1 1],
      [.copy 0, .copy 1, .nand 3 4, .const false, .const false]], [2]) := rfl

-- Every supported execution of the generated chain computes OR for all four input pairs.
example (a b : Bool) (outputs : List (List Bool))
    (h : outputs ∈ (ProbComp.eval
      (Scheme.evaluateCircuit decryptionCircuits 0 [[true], [false]] links
        [[a, false], [b, false]] 2 orCircuit.code)).support) :
    tagged.EncryptedWires (fun _ => 2) 0 [false] [a || b] outputs := by
  have hcorrect := Scheme.encryptedWires_evaluateCircuit_of_generatedChain decryptionCircuits
    tagged_correct tagged_width tagged_bootstrappable 0 keys links orCircuit chain_supported
    ![a, b] [[a, false], [b, false]]
    (by simp [Scheme.FreshInputs, keys, tagged]) outputs h
  simpa [keys, orCircuit, Circuit.eval_oneGate, Boolean.interpretation] using hcorrect

private theorem eval_augmentedXor (x : Fin 6 → Bool) :
    (augmentNand xorCircuit).eval Boolean.interpretation x 0 =
      !((x 1 ^^ x 0) && (x 4 ^^ x 3)) := by
  rw [augmentNand, Circuit.eval_comp, Boolean.eval_nandCircuit, Circuit.eval_parallel]
  change Bool.not ((xorCircuit.eval Boolean.interpretation (x ∘ Fin.castAdd 3) 0) &&
    (xorCircuit.eval Boolean.interpretation (x ∘ Fin.natAdd 3) 0)) = _
  rw [eval_xorCircuit, eval_xorCircuit]
  rfl

-- The final tag is evaluated, and the message decrypts to true under the final false key.
-- Simply feeding first-layer evaluated ciphertexts to the base evaluator would return false.
example : ProbComp.eval (Scheme.evaluateCircuit decryptionCircuits 0 [[true], [false]] links
    [[false, false], [true, false]] 2 orCircuit.code) = PMF.pure [[true, true]] := by
  have hcompile : compile 2 orCircuit.code =
      ([[.copy 0, .copy 1, .const false, .nand 0 0, .nand 1 1],
        [.copy 0, .copy 1, .nand 3 4, .const false, .const false]], [2]) := rfl
  rw [Scheme.evaluateCircuit, hcompile]
  simp [Scheme.evaluateLayers, Scheme.evaluateLayerStep, OracleComp.iterate,
    Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh, Scheme.refreshNand,
    Scheme.encryptBits, links, tagged, evaluatedBit, decryptionCircuits, eval_augmentedXor,
    eval_xorCircuit, decode, BitString.ofList]

private def wiring : Circuit Boolean.signature 2 3 := Circuit.wiring _ ![1, 0, 1]

-- No refresh or key transition occurs: output selection preserves exact ciphertexts and tags.
example (first second : List Bool) :
    Scheme.evaluateCircuit decryptionCircuits 0 [] [] [first, second] 2 wiring.code =
      pure [second, first, second] := by
  have hcompile : compile 2 wiring.code = ([], [1, 0, 1]) := rfl
  rw [Scheme.evaluateCircuit, hcompile]
  simp [Scheme.evaluateLayers]

-- The one-key generated chain retains the initial true secret key, including repeated outputs.
example (outputs : List (List Bool))
    (h : outputs ∈ (ProbComp.eval (Scheme.evaluateCircuit decryptionCircuits 0 [] []
      [[false, false], [true, false]] 2 wiring.code)).support) :
    tagged.EncryptedWires (fun _ => 2) 0 [true] [false, true, false] outputs := by
  have hchain : ([([true], [true])], []) ∈
      (ProbComp.eval (tagged.generateKeyChain 0 (2 * wiring.depth))).support := by
    rw [Scheme.mem_support_generateKeyChain_iff]
    refine ⟨by simp [wiring], ?_, by simp [Scheme.ValidLinks]⟩
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact (keys_supported 0 _).2 ⟨true, rfl⟩
  have hcorrect := Scheme.encryptedWires_evaluateCircuit_of_generatedChain decryptionCircuits
    tagged_correct tagged_width tagged_bootstrappable 0 [([true], [true])] [] wiring hchain
    ![true, false] [[false, false], [true, false]]
    (by simp [Scheme.FreshInputs, tagged]) outputs h
  simpa [wiring, Circuit.eval_wiring] using hcorrect

-- The native certificate covers the complete public input, including arbitrary raw source
-- codes, mismatched key-list lengths, malformed references and ciphertexts of any width.
example : IsPPTOn
    (encPair encUnary (encPair (encList encBits) (encPair (encList (encList encBits))
      (encPair (encList encBits) (encPair encUnary Boolean.encCode))))) (encList encBits)
    (fun p => Scheme.evaluateCircuit decryptionCircuits p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  apply Scheme.isPPTOn_evaluateCircuit decryptionCircuits encrypt_ppt evaluate_ppt
    circuits_poly
  all_goals fun_prop

end ComplexityTests.HomomorphicEvaluation
