/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Leveled.Basic
import Complexity.Crypto.Computational.Homomorphic.Leveled.Correctness
import Complexity.Crypto.Computational.Homomorphic.Leveled.PolyTime
import ComplexityTests.Crypto.HomomorphicExample
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
End-to-end clients of the depth-budgeted scheme. The insecure tagged fixture rejects its own
evaluated inputs, and the initial and final masking bits differ. Thus exact ciphertexts test
both refresh through the full budget and the endpoint selected by the outer tag. These are
correctness and runtime tests, with no security claim.
-/

namespace ComplexityTests.HomomorphicLeveled

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample Boolean.Layered

private def keys : List (List Bool × List Bool) :=
  [([false], [false]), ([true], [true]), ([true], [true])]

private def links : List (List (List Bool)) := [[[true, false]], [[false, false]]]

private def artifact : List Bool × List Bool := Leveled.keyPair 2 keys links

private theorem chain_supported :
    (keys, links) ∈ (ProbComp.eval (tagged.generateKeyChain 0 2)).support := by
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro key hk
    simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    all_goals exact (keys_supported 0 _).2 ⟨_, rfl⟩
  · simp [Scheme.ValidLinks, Scheme.FreshInputs, keys, links, tagged]

private theorem artifact_supported :
    artifact ∈ (ProbComp.eval (Leveled.keyGen tagged 0 1)).support := by
  rw [Leveled.keyGen, ProbComp.eval_map, PMF.mem_support_map_iff]
  exact ⟨(keys, links), chain_supported, rfl⟩

private def wiring : Circuit Boolean.signature 1 1 := Circuit.wiring _ ![0]

private def disjunction : Circuit Boolean.signature 2 1 := Circuit.oneGate .or id

private def constant : Circuit Boolean.signature 0 1 := Circuit.oneGate (.const true) Fin.elim0

private def deadWiring : Circuit Boolean.signature 1 1 :=
  (Circuit.ofCode (σ := Boolean.signature) 1 1
    ([(.not, [0]), (.not, [1])], [0])).get (by decide)

private def doubleNegation : Circuit Boolean.signature 1 1 :=
  (Circuit.ofCode (σ := Boolean.signature) 1 1
    ([(.not, [0]), (.not, [1])], [2])).get (by decide)

private theorem eval_augmentedXor (x : Fin 6 → Bool) :
    (augmentNand xorCircuit).eval Boolean.interpretation x 0 =
      !((x 1 ^^ x 0) && (x 4 ^^ x 3)) := by
  rw [augmentNand, Circuit.eval_comp, Boolean.eval_nandCircuit, Circuit.eval_parallel]
  change Bool.not ((xorCircuit.eval Boolean.interpretation (x ∘ Fin.castAdd 3) 0) &&
    (xorCircuit.eval Boolean.interpretation (x ∘ Fin.natAdd 3) 0)) = _
  rw [eval_xorCircuit, eval_xorCircuit]
  rfl

-- The public projection and the two private endpoints come from an actual supported sampler.
example :
    artifact ∈
      (ProbComp.eval ((Leveled.scheme decryptionCircuits (fun _ => 1)).keyGen 0)).support :=
  artifact_supported
example : Leveled.publicKeyDecoder.decode artifact.1 = ([[false], [true], [true]], links) := by
  simp [artifact, Leveled.keyPair, keys]
example : Leveled.secretKeyDecoder.decode artifact.2 = ([false], [true]) := by
  simp [artifact, Leveled.keyPair, keys]

-- Fresh encryption uses the initial false mask and marks the initial endpoint.
example : ProbComp.eval (Leveled.encrypt tagged 0 artifact.1 true) =
    PMF.pure [false, true, false] := by
  simp [Leveled.encrypt, artifact, Leveled.keyPair, keys, tagged]

-- A depth-zero circuit still traverses the full budget. The final mask is true, and the
-- payload now has the base evaluator's tag as well as the wrapper's final-endpoint tag.
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 1 artifact.1
    ⟨1, wiring⟩ [[false, true, false]]) = PMF.pure [true, false, true] := by
  have hcompile : compile 1 wiring.code = ([], [0]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, artifact, Leveled.keyPair, keys,
    hcompile, padTo, identityLayer, Scheme.evaluateLayers, Scheme.evaluateLayerStep,
    OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh,
    Scheme.encryptBits, links, tagged, evaluatedBit, decryptionCircuits, eval_xorCircuit,
    decode, BitString.ofList]

-- The same serialized key also evaluates a depth-one OR, with both compiler microlevels.
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 1 artifact.1
    ⟨2, disjunction⟩ [[false, false, false], [false, true, false]]) =
    PMF.pure [true, false, true] := by
  have hcompile : compile 2 disjunction.code =
      ([[.copy 0, .copy 1, .const false, .nand 0 0, .nand 1 1],
        [.copy 0, .copy 1, .nand 3 4, .const false, .const false]], [2]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, artifact, Leveled.keyPair, keys,
    hcompile, padTo, Scheme.evaluateLayers, Scheme.evaluateLayerStep, OracleComp.iterate,
    Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh, Scheme.refreshNand,
    Scheme.encryptBits, links, tagged, evaluatedBit, decryptionCircuits, eval_augmentedXor,
    eval_xorCircuit, decode, BitString.ofList]

-- Decryption must choose different endpoint secrets for these two representations of true.
example : Leveled.decrypt decryptionCircuits 0 artifact.2 [false, true, false] = true ∧
    Leveled.decrypt decryptionCircuits 0 artifact.2 [true, false, true] = true := by
  simp [Leveled.decrypt, artifact, Leveled.keyPair, keys, decryptionCircuits,
    eval_xorCircuit, BitString.ofList]

-- A constant starts with no encrypted inputs and reaches the same final key.
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 1 artifact.1
    ⟨0, constant⟩ []) = PMF.pure [true, false, true] := by
  have hcompile : compile 0 constant.code =
      ([[.const false, .const true, .const false],
        [.copy 1, .const false, .const false]], [0]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, artifact, Leveled.keyPair, keys,
    hcompile, padTo, Scheme.evaluateLayers, Scheme.evaluateLayerStep, OracleComp.iterate,
    Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh, Scheme.encryptBits, links,
    tagged, evaluatedBit, decryptionCircuits, eval_xorCircuit, decode, BitString.ofList]

-- Dead depth-two gates do not change the circuit's designated-output depth or its budget use.
example : deadWiring.program.depth = 2 ∧ deadWiring.depth = 0 := by decide +kernel
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 1 artifact.1
    ⟨1, deadWiring⟩ [[false, true, false]]) = PMF.pure [true, false, true] := by
  have hcompile : compile 1 deadWiring.code = ([], [0]) := by decide +kernel
  simp [Leveled.evaluate, Leveled.evaluateCircuit, artifact, Leveled.keyPair, keys,
    hcompile, padTo, identityLayer, Scheme.evaluateLayers, Scheme.evaluateLayerStep,
    OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh,
    Scheme.encryptBits, links, tagged, evaluatedBit, decryptionCircuits, eval_xorCircuit,
    decode, BitString.ofList]

private def zeroArtifact : List Bool × List Bool :=
  Leveled.keyPair 0 [([true], [true])] []

private theorem zeroArtifact_supported :
    zeroArtifact ∈ (ProbComp.eval (Leveled.keyGen tagged 0 0)).support := by
  rw [Leveled.keyGen, ProbComp.eval_map, PMF.mem_support_map_iff]
  refine ⟨([([true], [true])], []), ?_, rfl⟩
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, by simp [Scheme.ValidLinks]⟩
  intro key hk
  obtain rfl := List.mem_singleton.mp hk
  exact (keys_supported 0 _).2 ⟨true, rfl⟩

-- At budget zero the endpoints coincide; evaluation changes only the outer tag.
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 0 zeroArtifact.1
    ⟨1, wiring⟩ [[false, false, false]]) = PMF.pure [true, false, false] := by
  have hcompile : compile 1 wiring.code = ([], [0]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, zeroArtifact, Leveled.keyPair,
    hcompile, padTo, Scheme.evaluateLayers]
example : Leveled.decrypt decryptionCircuits 0 zeroArtifact.2 [true, false, false] = true := by
  simp [Leveled.decrypt, zeroArtifact, Leveled.keyPair, decryptionCircuits,
    eval_xorCircuit, BitString.ofList]

private def keysTwo : List (List Bool × List Bool) :=
  [([false], [false]), ([true], [true]), ([false], [false]), ([false], [false]), ([true], [true])]

private def linksTwo : List (List (List Bool)) :=
  [[[true, false]], [[true, false]], [[false, false]], [[true, false]]]

private def artifactTwo : List Bool × List Bool := Leveled.keyPair 4 keysTwo linksTwo

private theorem artifactTwo_supported :
    artifactTwo ∈ (ProbComp.eval (Leveled.keyGen tagged 0 2)).support := by
  rw [Leveled.keyGen, ProbComp.eval_map, PMF.mem_support_map_iff]
  refine ⟨(keysTwo, linksTwo), ?_, rfl⟩
  rw [Scheme.mem_support_generateKeyChain_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro key hk
    simp only [keysTwo, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    all_goals exact (keys_supported 0 _).2 ⟨_, rfl⟩
  · simp [Scheme.ValidLinks, Scheme.FreshInputs, keysTwo, linksTwo, tagged]

-- The budget-two endpoint differs from the keys after two and three transitions, so stopping
-- early at either point would give the wrong payload under the final key.
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 2 artifactTwo.1
    ⟨1, wiring⟩ [[false, true, false]]) = PMF.pure [true, false, true] := by
  have hcompile : compile 1 wiring.code = ([], [0]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, artifactTwo, Leveled.keyPair, keysTwo,
    hcompile, padTo, identityLayer, Scheme.evaluateLayers, Scheme.evaluateLayerStep,
    OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh,
    Scheme.encryptBits, linksTwo, tagged, evaluatedBit, decryptionCircuits, eval_xorCircuit,
    decode, BitString.ofList]

example : wiring.depth = 0 ∧ disjunction.depth = 1 ∧ doubleNegation.depth = 2 := by
  decide +kernel

-- The permission boundary uses designated-output depth and rejects deeper circuits.
example : (Leveled.scheme decryptionCircuits (fun _ => 1)).permitted 0 ⟨1, deadWiring⟩ ∧
    (Leveled.scheme decryptionCircuits (fun _ => 1)).permitted 0 ⟨2, disjunction⟩ ∧
    ¬(Leveled.scheme decryptionCircuits (fun _ => 1)).permitted 0 ⟨1, doubleNegation⟩ := by
  change deadWiring.depth ≤ 1 ∧ disjunction.depth ≤ 1 ∧ ¬doubleNegation.depth ≤ 1
  decide +kernel
example : ¬(Leveled.scheme decryptionCircuits (fun _ => 0)).permitted 0 ⟨0, constant⟩ := by
  change ¬constant.depth ≤ 0
  decide +kernel

-- All inputs and supported evaluation outputs are covered for every circuit through depth two,
-- including the three depths above. Fresh inputs use the initial false mask of this real key.
example {arity : ℕ} (c : Circuit Boolean.signature arity 1) (hdepth : c.depth ≤ 2)
    (bits : List Bool) (hbits : bits.length = arity) (output : List Bool)
    (houtput : output ∈ (ProbComp.eval (Leveled.evaluate decryptionCircuits 0 2 artifactTwo.1
      ⟨arity, c⟩ (bits.map (fun bit => [false, bit, false])))).support) :
    output.length = 3 ∧ Leveled.decrypt decryptionCircuits 0 artifactTwo.2 output =
      c.eval Boolean.interpretation (BitString.ofList arity bits) 0 := by
  apply Leveled.evaluate_spec decryptionCircuits tagged_correct tagged_width
    tagged_bootstrappable (fun _ => 2) 0 artifactTwo artifactTwo_supported
    ⟨arity, c⟩ hdepth bits (bits.map (fun bit => [false, bit, false])) hbits ?_ output houtput
  simp [Scheme.FreshInputs, List.forall₂_map_right_iff, List.forall₂_same, Leveled.scheme,
    Leveled.encrypt, artifactTwo, Leveled.keyPair, keysTwo, tagged]

-- Two-hop evaluation across budget 2 (step₁ = 1, step₂ = 1): hop 1 advances from key 0 ([false])
-- to key 2 ([false]), and hop 2 advances from key 2 ([false]) to the final key 4 ([true]).
example : ProbComp.eval (do
    let mid ← Leveled.evaluateHop decryptionCircuits 0 0 1 artifactTwo.1
      ⟨2, disjunction⟩ [[false, false, false], [false, true, false]]
    Leveled.evaluateHop decryptionCircuits 0 1 1 artifactTwo.1
      ⟨1, wiring⟩ [mid]) = PMF.pure [true, false, true] := by
  have hcompileOr : compile 2 disjunction.code =
      ([[.copy 0, .copy 1, .const false, .nand 0 0, .nand 1 1],
        [.copy 0, .copy 1, .nand 3 4, .const false, .const false]], [2]) := rfl
  have hcompileWire : compile 1 wiring.code = ([], [0]) := rfl
  simp [Leveled.evaluateHop, Leveled.evaluateCircuit, artifactTwo, Leveled.keyPair, keysTwo,
    hcompileOr, hcompileWire, padTo, identityLayer, Scheme.evaluateLayers,
    Scheme.evaluateLayerStep, OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode,
    Scheme.refresh, Scheme.refreshNand, Scheme.encryptBits, linksTwo, tagged, evaluatedBit,
    decryptionCircuits, eval_augmentedXor, eval_xorCircuit, decode, BitString.ofList]

example (outer : Σ m, Circuit Boolean.signature m 1) (houter : outer.2.depth ≤ 1)
    (midBits : List Bool) (mids : List (List Bool)) (hmidBits : midBits.length = outer.1)
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit Boolean.signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          c.2.depth ≤ 1 ∧
            bits.length = c.1 ∧
            (Leveled.scheme decryptionCircuits (fun _ => 2)).FreshInputs 0
              artifactTwo.1 bits inputs ∧
            mid ∈ (ProbComp.eval
              (Leveled.evaluateHop decryptionCircuits 0 0 1 artifactTwo.1 c inputs)).support ∧
            c.2.eval Boolean.interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids)
    (output : List Bool)
    (houtput : output ∈ (ProbComp.eval
      (Leveled.evaluateHop decryptionCircuits 0 1 1 artifactTwo.1 outer mids)).support) :
    output.length = 3 ∧ Leveled.decrypt decryptionCircuits 0 artifactTwo.2 output =
      outer.2.eval Boolean.interpretation (BitString.ofList outer.1 midBits) 0 :=
  Leveled.evaluateHop_twoHop_spec decryptionCircuits tagged_correct tagged_width
    tagged_bootstrappable (fun _ => 2) 0 1 1 artifactTwo artifactTwo_supported rfl
    outer houter midBits mids hmidBits hmids output houtput

-- The concrete base scheme inhabits the scheme and fixed-width interfaces at a growing budget.
example : (Leveled.scheme decryptionCircuits (fun n => n + 1)).Correct :=
  Leveled.correct decryptionCircuits tagged_correct tagged_width tagged_bootstrappable
    (fun n => n + 1)
example :
    (Leveled.scheme decryptionCircuits (fun n => n + 1)).FixedWidth (fun _ => 4) (fun _ => 3) :=
  Leveled.fixedWidth decryptionCircuits tagged_correct tagged_width tagged_bootstrappable
    (fun n => n + 1)

-- Total decoding and circuit-based decryption cover malformed keys and truncated ciphertexts.
example : Leveled.decrypt decryptionCircuits 0 [] [] = false := by decide +kernel
example : Leveled.decrypt decryptionCircuits 0 artifact.2 [true] = true := by
  simp [Leveled.decrypt, artifact, Leveled.keyPair, keys, decryptionCircuits,
    eval_xorCircuit, BitString.ofList]
example : ProbComp.eval (Leveled.evaluate decryptionCircuits 0 0 [] ⟨1, wiring⟩ []) =
    PMF.pure [true] := by
  have hcompile : compile 1 wiring.code = ([], [0]) := rfl
  simp [Leveled.evaluate, Leveled.evaluateCircuit, hcompile, padTo, Scheme.evaluateLayers]

-- All four native algorithm certificates accept their full inputs, including arbitrary key
-- serializations, malformed ciphertexts and circuits outside the budget. No validity is assumed.
example : IsPPTOn (encPair encUnary encUnary) (encPair encBits encBits)
    (fun p => Leveled.keyGen tagged p.1 p.2) := by
  apply Leveled.isPPTOn_keyGen keyGen_ppt encrypt_ppt <;> fun_prop

example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => Leveled.encrypt tagged p.1 p.2.1 p.2.2) := by
  apply Leveled.isPPTOn_encrypt encrypt_ppt <;> fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool => Leveled.decrypt decryptionCircuits p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) encBool := by
  apply Leveled.computableInPolyTime_decrypt decryptionCircuits circuits_poly <;>
    fun_prop

example : IsPPTOn
    (encPair encUnary (encPair encUnary
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))) encBits
    (fun p => Leveled.evaluate decryptionCircuits p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  apply Leveled.isPPTOn_evaluate encrypt_ppt decryptionCircuits circuits_poly
    evaluate_ppt
  all_goals fun_prop

example : IsPPTOn
    (encPair encUnary (encPair encUnary (encPair encUnary
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits)))))) encBits
    (fun p => Leveled.evaluateHop decryptionCircuits p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  apply Leveled.isPPTOn_evaluateHop encrypt_ppt decryptionCircuits evaluate_ppt
    circuits_poly
  all_goals fun_prop

-- A nonconstant budget family instantiates the actual Scheme fields with one uniform clock.
example : IsPPTOn encUnary (encPair encBits encBits)
    (Leveled.scheme decryptionCircuits (fun n => n + 1)).keyGen :=
  Leveled.isPPTOn_scheme_keyGen keyGen_ppt encrypt_ppt decryptionCircuits
    (fun n => n + 1) (by fun_prop)

example : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits)))) encBits
    (fun p => (Leveled.scheme decryptionCircuits (fun n => n + 1)).evaluate
      p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Leveled.isPPTOn_scheme_evaluate encrypt_ppt decryptionCircuits circuits_poly
    evaluate_ppt
    (fun n => n + 1) (by fun_prop)

-- The same generated decryption circuits supply the compact widths' polynomial bounds.
example : PolynomiallyBounded (fun _ : ℕ => 4) ∧ PolynomiallyBounded (fun _ : ℕ => 3) :=
  Leveled.polynomiallyBounded_widths decryptionCircuits circuits_poly

end ComplexityTests.HomomorphicLeveled
