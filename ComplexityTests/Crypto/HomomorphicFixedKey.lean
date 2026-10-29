/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.FixedKey.Correctness
import Complexity.Crypto.Computational.Homomorphic.FixedKey.PolyTime
import ComplexityTests.Crypto.HomomorphicExample

/-!
The insecure tagged fixture rejects evaluated ciphertexts in its base evaluator. Fixed-key
bootstrapping instead reuses one public artifact and one secret through successive evaluations,
without changing ciphertext width or imposing a depth budget. Exact distribution tests exercise
the compiled computation; generic clients check the stronger encrypted-wire invariant and native
runtime certificates. No encryption-security claim is made for this fixture.
-/

namespace ComplexityTests.HomomorphicFixedKey

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM
open ComplexityTests.HomomorphicExample Boolean.Layered

private def encryptedKey : List (List Bool) := [[false, false]]

private def artifact : List Bool × List Bool :=
  (FixedKey.encPublicKey ([true], encryptedKey), [true])

private theorem artifact_supported (n : ℕ) :
    artifact ∈ (ProbComp.eval (FixedKey.keyGen tagged n)).support := by
  rw [FixedKey.mem_support_keyGen_iff]
  refine ⟨([true], [true]), encryptedKey, (keys_supported n _).2 ⟨true, rfl⟩, ?_, rfl⟩
  simp [Scheme.FreshInputs, encryptedKey, tagged]

private def disjunction : Circuit Boolean.signature 2 1 := Circuit.oneGate .or id

private def constant : Circuit Boolean.signature 0 1 := Circuit.oneGate (.const true) Fin.elim0

private def wiring : Circuit Boolean.signature 2 3 := Circuit.wiring _ ![1, 0, 1]

private def deadWiring : Circuit Boolean.signature 1 1 :=
  (Circuit.ofCode (σ := Boolean.signature) 1 1
    ([(.not, [0]), (.not, [1])], [0])).get (by decide)

private theorem eval_augmentedXor (x : Fin 6 → Bool) :
    (augmentNand xorCircuit).eval Boolean.interpretation x 0 =
      !((x 1 ^^ x 0) && (x 4 ^^ x 3)) := by
  rw [augmentNand, Circuit.eval_comp, Boolean.eval_nandCircuit, Circuit.eval_parallel]
  change Bool.not ((xorCircuit.eval Boolean.interpretation (x ∘ Fin.castAdd 3) 0) &&
    (xorCircuit.eval Boolean.interpretation (x ∘ Fin.natAdd 3) 0)) = _
  rw [eval_xorCircuit, eval_xorCircuit]
  rfl

-- The same artifact is supported at parameter 0 and contains exactly one self-encrypted key.
example : artifact ∈ (ProbComp.eval (FixedKey.keyGen tagged 0)).support :=
  artifact_supported 0
example : FixedKey.publicKeyDecoder.decode artifact.1 = ([true], encryptedKey) := by
  simp [artifact]
example : ProbComp.eval (FixedKey.encrypt tagged 0 artifact.1 true) =
    PMF.pure [false, false] := by
  simp [FixedKey.encrypt, artifact, tagged]

-- Both input tags are arbitrary: refresh reads the old ciphertext as data, then feeds fresh
-- encryptions of its bits to the base evaluator. The second input represents true.
private theorem evaluate_or (firstTag secondTag : Bool) :
    ProbComp.eval (FixedKey.evaluate decryptionCircuits 0 artifact.1
      ⟨2, disjunction⟩ [[true, firstTag], [false, secondTag]]) =
      PMF.pure [false, true] := by
  have hcompile : compile 2 disjunction.code =
      ([[.copy 0, .copy 1, .const false, .nand 0 0, .nand 1 1],
        [.copy 0, .copy 1, .nand 3 4, .const false, .const false]], [2]) := rfl
  have hdepth : Boolean.depthCode 2 disjunction.code = 1 := by decide +kernel
  simp [FixedKey.evaluate, FixedKey.evaluateCircuit, artifact, hdepth,
    Scheme.evaluateCircuit, hcompile, Scheme.evaluateLayers, Scheme.evaluateLayerStep,
    OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh,
    Scheme.refreshNand, Scheme.encryptBits, encryptedKey, tagged, evaluatedBit,
    decryptionCircuits, eval_augmentedXor, eval_xorCircuit, decode, BitString.ofList]

-- A real evaluation output is fed back to another evaluation with exactly the same public key.
example : ProbComp.eval (do
    let ciphertext ← FixedKey.evaluate decryptionCircuits 0 artifact.1
      ⟨2, disjunction⟩ [[true, false], [false, false]]
    FixedKey.evaluate decryptionCircuits 0 artifact.1
      ⟨2, disjunction⟩ [[true, false], ciphertext]) = PMF.pure [false, true] := by
  rw [ProbComp.eval_bind, evaluate_or, PMF.pure_bind]
  exact evaluate_or false true

-- The base evaluator returns false on those same evaluated inputs, and the evaluated
-- ciphertext is outside every fresh-encryption support.
example : ProbComp.eval (tagged.evaluate 0 [true] ⟨2, disjunction⟩
    [[true, false], [false, true]]) = PMF.pure [true, true] := by
  simp [tagged, evaluatedBit]
example (pk : List Bool) (bit : Bool) :
    [false, true] ∉ (ProbComp.eval (tagged.encrypt 0 pk bit)).support := by
  simp [tagged]

-- It nevertheless satisfies the stronger same-secret invariant used by fixed-key evaluation.
example : (FixedKey.scheme decryptionCircuits).EncryptedWires (fun _ => 2) 0 artifact.2
    [false, true] [[true, false], [false, true]] := by
  simp [Scheme.EncryptedWires, FixedKey.scheme, FixedKey.decrypt, artifact,
    decryptionCircuits, eval_xorCircuit, BitString.ofList]
example : FixedKey.decrypt decryptionCircuits 0 artifact.2 [false, false] = true ∧
    FixedKey.decrypt decryptionCircuits 0 artifact.2 [false, true] = true := by
  simp [FixedKey.decrypt, artifact, decryptionCircuits, eval_xorCircuit, BitString.ofList]

-- Zero-depth wiring preserves exact ciphertexts, including evaluated tags and repeated outputs.
example (first second : List Bool) :
    FixedKey.evaluateCircuit decryptionCircuits 0 [true] encryptedKey
      [first, second] 2 wiring.code = pure [second, first, second] := by
  have hcompile : compile 2 wiring.code = ([], [1, 0, 1]) := rfl
  simp [FixedKey.evaluateCircuit, Scheme.evaluateCircuit, hcompile, Scheme.evaluateLayers]

-- Nullary constants need no input ciphertexts and still return the unchanged base width.
example : ProbComp.eval (FixedKey.evaluate decryptionCircuits 0 artifact.1
    ⟨0, constant⟩ []) = PMF.pure [false, true] := by
  have hcompile : compile 0 constant.code =
      ([[.const false, .const true, .const false],
        [.copy 1, .const false, .const false]], [0]) := rfl
  have hdepth : Boolean.depthCode 0 constant.code = 1 := by decide +kernel
  simp [FixedKey.evaluate, FixedKey.evaluateCircuit, artifact, hdepth,
    Scheme.evaluateCircuit, hcompile, Scheme.evaluateLayers, Scheme.evaluateLayerStep,
    OracleComp.iterate, Scheme.evaluateLayer, Scheme.evaluateNode, Scheme.refresh,
    Scheme.encryptBits, encryptedKey, tagged, evaluatedBit, decryptionCircuits,
    eval_xorCircuit, decode, BitString.ofList]

-- Unused gates do not force a refresh: only the designated output depths determine the schedule.
example : deadWiring.program.depth = 2 ∧ deadWiring.depth = 0 := by decide +kernel
example (ciphertext : List Bool) : FixedKey.evaluate decryptionCircuits 0 artifact.1
    ⟨1, deadWiring⟩ [ciphertext] = pure ciphertext := by
  have hcompile : compile 1 deadWiring.code = ([], [0]) := by decide +kernel
  simp [FixedKey.evaluate, FixedKey.evaluateCircuit, Scheme.evaluateCircuit,
    hcompile, Scheme.evaluateLayers]

-- Every finite circuit is permitted; there is no hidden depth bound in this client.
example :
    (FixedKey.scheme decryptionCircuits).permitted 0 ⟨2, disjunction⟩ := trivial

-- All supported outputs are covered for arbitrary well-sized decrypting inputs, including
-- previous evaluator results. No fresh-encryption or depth premise appears here.
example (n : ℕ) (c : Σ m, Circuit Boolean.signature m 1)
    (bits : List Bool) (inputs : List (List Bool)) (hbits : bits.length = c.1)
    (hinputs : (FixedKey.scheme decryptionCircuits).EncryptedWires (fun _ => 2) n
      artifact.2 bits inputs) (output : List Bool)
    (houtput : output ∈ (ProbComp.eval
      (FixedKey.evaluate decryptionCircuits n artifact.1 c inputs)).support) :
    output.length = 2 ∧ FixedKey.decrypt decryptionCircuits n artifact.2 output =
      c.2.eval Boolean.interpretation (BitString.ofList c.1 bits) 0 :=
  FixedKey.evaluate_spec decryptionCircuits tagged_correct tagged_width tagged_bootstrappable
    n artifact (artifact_supported n) c bits inputs hbits hinputs output houtput

-- Two-hop fixed-key evaluation composes pointwise first-hop evaluations with an outer circuit.
example (n : ℕ) (outer : Σ m, Circuit Boolean.signature m 1)
    (midBits : List Bool) (mids : List (List Bool)) (hmidBits : midBits.length = outer.1)
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit Boolean.signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          bits.length = c.1 ∧
            (FixedKey.scheme decryptionCircuits).EncryptedWires (fun _ => 2) n
              artifact.2 bits inputs ∧
            mid ∈ (ProbComp.eval
              ((FixedKey.scheme decryptionCircuits).evaluate n artifact.1 c inputs)).support ∧
            c.2.eval Boolean.interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids)
    (output : List Bool)
    (houtput : output ∈ (ProbComp.eval
      ((FixedKey.scheme decryptionCircuits).evaluate n artifact.1 outer mids)).support) :
    output.length = 2 ∧ FixedKey.decrypt decryptionCircuits n artifact.2 output =
      outer.2.eval Boolean.interpretation (BitString.ofList outer.1 midBits) 0 :=
  FixedKey.evaluate_twoHop_spec decryptionCircuits tagged_correct tagged_width
    tagged_bootstrappable n artifact (artifact_supported n) outer midBits mids hmidBits
    hmids output houtput

example : (FixedKey.scheme decryptionCircuits).Correct :=
  FixedKey.correct decryptionCircuits tagged_correct tagged_width tagged_bootstrappable
example : (FixedKey.scheme decryptionCircuits).FixedWidth (fun _ => 1) (fun _ => 2) :=
  FixedKey.fixedWidth decryptionCircuits tagged_correct tagged_width tagged_bootstrappable

-- Decryption uses the same circuit and representation, even for its total malformed-input path.
example : (FixedKey.decryptionCircuits decryptionCircuits).circuit 0 = xorCircuit := rfl
example : FixedKey.decrypt decryptionCircuits 0 [] [] = false := by decide +kernel
example : FixedKey.decrypt decryptionCircuits 0 [true] [] = true := by decide +kernel

-- These are certificates for the actual Scheme fields, uniformly over complete encoded inputs.
example : IsPPTOn encUnary (encPair encBits encBits) (FixedKey.scheme decryptionCircuits).keyGen :=
  FixedKey.isPPTOn_scheme_keyGen keyGen_ppt encrypt_ppt decryptionCircuits

example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => (FixedKey.scheme decryptionCircuits).encrypt p.1 p.2.1 p.2.2) :=
  FixedKey.isPPTOn_scheme_encrypt encrypt_ppt decryptionCircuits

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool =>
      (FixedKey.scheme decryptionCircuits).decrypt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) encBool :=
  FixedKey.computableInPolyTime_scheme_decrypt decryptionCircuits circuits_poly

example : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits)))) encBits
    (fun p => (FixedKey.scheme decryptionCircuits).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  FixedKey.isPPTOn_scheme_evaluate encrypt_ppt decryptionCircuits circuits_poly
    evaluate_ppt

-- The same evaluator certificate also applies to an empty, malformed public artifact.
example : IsPPTOn (encPair encUnary (encPair (Boolean.encCircuit 1) (encList encBits))) encBits
    (fun p => FixedKey.evaluate decryptionCircuits p.1 [] p.2.1 p.2.2) := by
  apply FixedKey.isPPTOn_evaluate encrypt_ppt decryptionCircuits circuits_poly
    evaluate_ppt
  all_goals fun_prop

-- Raw evaluation charges arbitrary code and binary references, not just well-typed circuits.
example : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (encList encBits)
      (encPair (encList encBits) (encPair encUnary Boolean.encCode))))) (encList encBits)
    (fun p => FixedKey.evaluateCircuit decryptionCircuits p.1 p.2.1 p.2.2.1
      p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  apply FixedKey.isPPTOn_evaluateCircuit encrypt_ppt decryptionCircuits circuits_poly
    evaluate_ppt
  all_goals fun_prop

example : PolynomiallyBounded (fun _ : ℕ => 1) ∧ PolynomiallyBounded (fun _ : ℕ => 2) :=
  FixedKey.polynomiallyBounded_widths decryptionCircuits circuits_poly
example : PolynomiallyBounded (fun n => (decryptionCircuits.circuit n).size) :=
  FixedKey.polynomiallyBounded_decryptionSize decryptionCircuits circuits_poly
example : ComputableInPolyTime
    (fun n => (⟨_, (FixedKey.decryptionCircuits decryptionCircuits).circuit n⟩ :
      Σ m, Circuit Boolean.signature m 1)) encUnary (Boolean.encCircuit 1) := circuits_poly

end ComplexityTests.HomomorphicFixedKey
