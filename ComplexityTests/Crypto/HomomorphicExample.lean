/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Efficiency
import Complexity.Computability.Circuit.Boolean.EvaluationTime

/-!
An explicitly insecure bit-encryption example checks the refresh construction. A ciphertext has
a masked message bit and a tag. Fresh encryption always sets the tag to `false`, while evaluation
always sets it to `true` and deliberately returns a wrong answer on evaluated inputs.
Thus evaluation outputs lie outside every fresh-encryption support.
The public key reveals the masking bit; no security claim is made for this test scheme.
-/

namespace ComplexityTests.HomomorphicExample

open Cslib Cslib.Circuits Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM

def decode (key ciphertext : List Bool) : Bool :=
  ciphertext.getD 0 false ^^ key.getD 0 false

def evaluatedBit (pk : List Bool) (C : Σ n, Circuit Boolean.signature n 1)
    (inputs : List (List Bool)) : Bool :=
  if inputs.any (fun c => c.getD 1 false) then false
  else C.2.eval Boolean.interpretation (BitString.ofList C.1 (inputs.map (decode pk))) 0

noncomputable def tagged : Scheme where
  keyGen _ := (fun b : Bool => ([b], [b])) <$> ProbComp.uniform Bool
  encrypt _ pk b := pure [b ^^ pk.getD 0 false, false]
  decrypt _ := decode
  evaluate _ pk C inputs := pure
    [evaluatedBit pk C inputs ^^ pk.getD 0 false, true]
  permitted _ _ := True

theorem decode_encrypt (pk : List Bool) (b tag : Bool) :
    decode pk [b ^^ pk.getD 0 false, tag] = b := by
  change ((b ^^ pk.getD 0 false) ^^ pk.getD 0 false) = b
  cases b <;> cases pk.getD 0 false <;> rfl

theorem decode_fresh {n : ℕ} {pk bits : List Bool} {inputs : List (List Bool)}
    (h : tagged.FreshInputs n pk bits inputs) : inputs.map (decode pk) = bits := by
  induction h with
  | nil => rfl
  | @cons b c bits inputs hc _ ih =>
    have heq : c = [b ^^ pk.getD 0 false, false] := by simpa [tagged] using hc
    subst c
    simp only [List.map_cons, decode_encrypt, ih]

theorem tags_fresh {n : ℕ} {pk bits : List Bool} {inputs : List (List Bool)}
    (h : tagged.FreshInputs n pk bits inputs) :
    inputs.any (fun c => c.getD 1 false) = false := by
  induction h with
  | nil => rfl
  | @cons b c bits inputs hc _ ih =>
    have heq : c = [b ^^ pk.getD 0 false, false] := by simpa [tagged] using hc
    subst c
    change inputs.any (fun c => c.getD 1 false) = false
    exact ih

theorem keys_supported (n : ℕ) (keys : List Bool × List Bool) :
    keys ∈ (ProbComp.eval (tagged.keyGen n)).support ↔
      ∃ b : Bool, keys = ([b], [b]) := by
  have h : (0 : ENNReal) ≠ 2⁻¹ := (ENNReal.inv_ne_zero.mpr (by norm_num)).symm
  simp [tagged, eq_comm, h]

theorem tagged_correct : tagged.Correct where
  decrypt_encrypt n keys hkeys b c hc := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    have hc' : c = [b ^^ k, false] := by simpa [tagged] using hc
    subst c
    exact decode_encrypt [k] b false
  decrypt_evaluate n keys hkeys C _ bits inputs _ hfresh c hc := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    have hc' : c = [evaluatedBit [k] C inputs ^^ k, true] := by
      simpa [tagged] using hc
    subst c
    change decode [k] [evaluatedBit [k] C inputs ^^ k, true] = _
    exact (decode_encrypt [k] (evaluatedBit [k] C inputs) true).trans (by
      simp only [evaluatedBit, tags_fresh hfresh, Bool.false_eq_true, ite_false,
        decode_fresh hfresh])

theorem tagged_width : tagged.FixedWidth (fun _ => 1) (fun _ => 2) where
  secret_length n keys hkeys := by
    obtain ⟨k, rfl⟩ := (keys_supported n keys).1 hkeys
    rfl
  encrypt_length n keys _ b c hc := by
    have hc' : c = [b ^^ keys.1.getD 0 false, false] := by simpa [tagged] using hc
    simp [hc']
  evaluate_length n keys _ C _ bits inputs _ _ c hc := by
    have hc' : c = [evaluatedBit keys.1 C inputs ^^ keys.1.getD 0 false, true] := by
      simpa [tagged] using hc
    simp [hc']

def xorCircuit : Circuit Boolean.signature 3 1 :=
  (Circuit.oneGate (σ := Boolean.signature) .and id).comp
    ((Circuit.oneGate (σ := Boolean.signature) .or ![0, 1]).append
      ((Circuit.oneGate (σ := Boolean.signature) .not (fun _ => 0)).comp
        (Circuit.oneGate (σ := Boolean.signature) .and ![0, 1])))

theorem eval_xorCircuit (x : Fin 3 → Bool) :
    xorCircuit.eval Boolean.interpretation x 0 = (x 1 ^^ x 0) := by
  change ((x 0 || x 1) && !(x 0 && x 1)) = (x 1 ^^ x 0)
  cases x 0 <;> cases x 1 <;> rfl

def decryptionCircuits : DecryptionCircuits tagged (fun _ => 1) (fun _ => 2) where
  circuit _ := xorCircuit
  correct n sk c hsk hc := by
    rw [eval_xorCircuit]
    rcases sk with _ | ⟨s, sk⟩
    · simp at hsk
    rcases sk with _ | ⟨s', sk⟩
    · cases c with
      | nil => simp at hc
      | cons b rest => rfl
    · simp at hsk

theorem tagged_bootstrappable : Scheme.Bootstrappable decryptionCircuits where
  decrypt_mem _ := trivial
  nand_mem _ := trivial

theorem decode_poly : ComputableInPolyTime
    (fun p : List Bool × List Bool => decode p.1 p.2) (encPair encBits encBits) encBool := by
  unfold decode
  fun_prop

theorem evaluatedBit_poly : ComputableInPolyTime
    (fun p : List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
      evaluatedBit p.1 p.2.1 p.2.2)
    (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBool := by
  have hdecoded : ComputableInPolyTime
      (fun p : List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
        p.2.2.map (decode p.1))
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBits := by
    apply ComputableInPolyTime.mapToBitsWithInput
    · fun_prop
    · exact decode_poly.comp (show ComputableInPolyTime
        (fun p : (List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool)) ×
          List Bool => (p.1.1, p.2))
        (encPair (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBits)
        (encPair encBits encBits) by fun_prop)
  have heval : ComputableInPolyTime
      (fun p : List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
        p.2.1.2.eval Boolean.interpretation (BitString.ofList p.2.1.1 (p.2.2.map (decode p.1))) 0)
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))) encBool :=
    Boolean.computableInPolyTime_evalCircuit (by fun_prop) hdecoded
  unfold evaluatedBit
  fun_prop

theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => tagged.encrypt p.1 p.2.1 p.2.2) := by
  apply ComputableInPolyTime.isPPTOn
  change ComputableInPolyTime
    (fun p : ℕ × List Bool × Bool => [p.2.2 ^^ p.2.1.getD 0 false, false]) _ _
  fun_prop

theorem evaluate_ppt : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => tagged.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply ComputableInPolyTime.isPPTOn
  change ComputableInPolyTime
    (fun p : ℕ × List Bool × (Σ n, Circuit Boolean.signature n 1) × List (List Bool) =>
      [evaluatedBit p.2.1 p.2.2.1 p.2.2.2 ^^ p.2.1.getD 0 false, true]) _ _
  have heval := evaluatedBit_poly.comp
    (ComputableInPolyTime.snd encUnary
      (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
  fun_prop

theorem circuits_poly : ComputableInPolyTime
    (fun n => (⟨_, decryptionCircuits.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1) :=
  ComputableInPolyTime.const
    (⟨3, xorCircuit⟩ : Σ n, Circuit Boolean.signature n 1)

-- The key sampler is one fair bit followed by finite deterministic processing.
theorem keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) tagged.keyGen :=
  (isPPTOn_uniform_bool encUnary).map (ComputableInPolyTime.of_finite _)

end ComplexityTests.HomomorphicExample
