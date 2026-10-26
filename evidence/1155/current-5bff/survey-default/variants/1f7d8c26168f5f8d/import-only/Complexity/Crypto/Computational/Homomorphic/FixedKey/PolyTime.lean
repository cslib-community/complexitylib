/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Basic
public import Complexity.Crypto.Computational.Homomorphic.Evaluation.PolyTime
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Boolean.DepthTime.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.PPT.Capture


import Diag1155.Measure
/-!
# Uniform native certificates for fixed-key bootstrapping

The actual sampler encrypts one secret key under its own public key. Evaluation repeats that
public artifact across the compiled circuit layers; the key sampler takes no circuit or depth
parameter. The certificates charge the complete keys, encrypted secret, circuit code, ciphertext
inputs and outputs. Total decoding and evaluation also cover malformed artifacts and raw codes.

The only runtime premises concern the base algorithms and a uniform generator for the actual
decryption circuits. Correctness, bootstrappability, circular security and valid input widths
are not used to supply a runtime bound. Both unchanged widths and the decryption-circuit size
are polynomially bounded as a consequence of the generator certificate.

## Main results

* `Cslib.Crypto.Homomorphic.FixedKey.isPPTOn_keyGen`: generate the fixed public artifact.
* `Cslib.Crypto.Homomorphic.FixedKey.isPPTOn_encrypt`: encrypt after total artifact decoding.
* `Cslib.Crypto.Homomorphic.FixedKey.computableInPolyTime_decrypt`: execute decryption.
* `Cslib.Crypto.Homomorphic.FixedKey.isPPTOn_evaluate`: evaluate the complete circuit uniformly.
* `Cslib.Crypto.Homomorphic.FixedKey.polynomiallyBounded_widths`: bound both unchanged widths.
* `Cslib.Crypto.Homomorphic.FixedKey.polynomiallyBounded_decryptionSize`: bound circuit size.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, the self-loop
  construction][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.FixedKey

open Circuits Probability Turing.MultiTapeTM

variable {α : Type} {input : α ↪ List Bool} {E : Scheme}
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {n : α → ℕ} {pk sk ciphertext : α → List Bool}

include hkeyGen hencrypt in
/-- Generate one base key, encrypt its entire secret under that key, and serialize the artifact.
The key generator has no circuit-size or depth parameter. -/
@[fun_prop]
theorem isPPTOn_keyGen
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input (encPair encBits encBits) (fun a => keyGen E (n a)) := by
  have hn := hn.tidy
  apply (hkeyGen.preprocess (.of_tidy hn)).bind_with
  have hbits := Scheme.isPPTOn_encryptBits hencrypt
    (.of_tidy (show ComputableTidilyInPolyTime
      (fun p : α × (List Bool × List Bool) => n p.1)
      (encPair input (encPair encBits encBits)) encUnary by fun_prop))
    (.of_tidy (ComputableTidilyInPolyTime.snd _ _).fst')
    (.of_tidy (ComputableTidilyInPolyTime.snd _ _).snd')
  simpa only [bind_pure_comp] using hbits.map_with
    (.of_tidy (show ComputableTidilyInPolyTime
      (fun p : (α × (List Bool × List Bool)) × List (List Bool) =>
        (encPublicKey (p.1.2.1, p.2), p.1.2.2))
      (encPair (encPair input (encPair encBits encBits)) (encList encBits))
      (encPair encBits encBits) from
      (((ComputableTidilyInPolyTime.fst _ _).snd'.fst'.prod
        (ComputableTidilyInPolyTime.snd _ _)).encoded).prod
          (ComputableTidilyInPolyTime.fst _ _).snd'.snd'))

include hencrypt in
/-- Decode any public word and encrypt under the decoded base public key. -/
@[fun_prop]
theorem isPPTOn_encrypt {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBits (fun a => encrypt E (n a) (pk a) (bit a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hpk
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hbit
  have hpublic := publicKeyDecoder.computableInPolyTime.tidy.comp hpk
  exact hencrypt.preprocess (.of_tidy (hn.prod (hpublic.fst'.prod hbit)))

variable {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hD : ComputableInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))

include hD in
/-- Execute the generated decryption circuit on every encoded secret and ciphertext, with
the circuit evaluator's total padding and truncation conventions. -/
@[fun_prop]
theorem computableInPolyTime_decrypt
    (hn : ComputableInPolyTime n input encUnary)
    (hsk : ComputableInPolyTime sk input encBits)
    (hc : ComputableInPolyTime ciphertext input encBits) :
    ComputableInPolyTime (fun a => decrypt D (n a) (sk a) (ciphertext a))
      input encBool := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hsk
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hc
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  exact (Boolean.computableInPolyTime_evalCircuit (.of_tidy (hD.tidy.comp hn)) (.of_tidy
    (hsk.bitsAppend
    hc))).tidy

variable (hevaluate : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))

include hencrypt hevaluate hD in
/-- Compute the actual output depth, repeat the public artifact, and run the compiler and
encrypted evaluator. Both binary indices and all copied artifact data are charged. -/
@[fun_prop]
theorem isPPTOn_evaluateCircuit {inputCount : α → ℕ}
    {encryptedKey inputs : α → List (List Bool)}
    {code : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hek : ComputableInPolyTime encryptedKey input (encList encBits))
    (hinputs : ComputableInPolyTime inputs input (encList encBits))
    (hcount : ComputableInPolyTime inputCount input encUnary)
    (hcode : ComputableInPolyTime code input Boolean.encCode) :
    IsPPTOn input (encList encBits)
      (fun a => evaluateCircuit D (n a) (pk a) (encryptedKey a) (inputs a)
        (inputCount a) (code a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hpk
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hek
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hinputs
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcount
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcode
  have hdepth := (Boolean.computableInPolyTime_depthCode (.of_tidy hcount) (.of_tidy hcode)).tidy
  have hrepeats : ComputableTidilyInPolyTime
      (fun a => 2 * Boolean.depthCode (inputCount a) (code a)) input encUnary := by fun_prop
  exact Scheme.isPPTOn_evaluateCircuit D hencrypt hevaluate hD (.of_tidy hn)
    (.of_tidy (ComputableTidilyInPolyTime.replicate hrepeats hpk))
    (.of_tidy (ComputableTidilyInPolyTime.replicate hrepeats hek))
    (.of_tidy hinputs) (.of_tidy hcount) (.of_tidy hcode)

include hencrypt hevaluate hD in
/-- One uniform native certificate evaluates all finite circuits under the same public artifact.
It charges the complete encoded circuit and inputs without any correctness or width premise. -/
@[fun_prop]
theorem isPPTOn_evaluate {c : α → Σ m, Circuit Boolean.signature m 1}
    {inputs : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hc : ComputableInPolyTime c input (Boolean.encCircuit 1))
    (hinputs : ComputableInPolyTime inputs input (encList encBits)) :
    IsPPTOn input encBits (fun a => evaluate D (n a) (pk a) (c a) (inputs a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hpk
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hc
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hinputs
  have hpublic := publicKeyDecoder.computableInPolyTime.tidy.comp hpk
  have hview : ComputableTidilyInPolyTime
      (fun C : Σ m, Circuit Boolean.signature m 1 => (C.1, C.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have hparts := hview.comp hc
  exact (isPPTOn_evaluateCircuit hencrypt D hD hevaluate (.of_tidy hn)
    (.of_tidy hpublic.fst') (.of_tidy hpublic.snd') (.of_tidy hinputs)
    (.of_tidy hparts.fst') (.of_tidy hparts.snd')).map (ComputableInPolyTime.headD [])

include hD in
/-- Unary input arity in the emitted decryption circuit bounds both unchanged widths
polynomially in the security parameter. No separate width-computability premise is needed. -/
theorem polynomiallyBounded_widths :
    PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth := by
  have hview : ComputableTidilyInPolyTime
      (fun c : Σ m, Circuit Boolean.signature m 1 => (c.1, c.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have htotal : PolynomiallyBounded (fun n => secretWidth n + ciphertextWidth n) :=
    (hview.fst'.comp hD.tidy).polynomiallyBounded
  exact ⟨htotal.mono_of_le (fun n => Nat.le_add_right (secretWidth n) (ciphertextWidth n)),
    htotal.mono_of_le (fun n => Nat.le_add_left (ciphertextWidth n) (secretWidth n))⟩

include hD in
/-- A uniform native circuit generator also bounds the number of decryption gates. -/
theorem polynomiallyBounded_decryptionSize :
    PolynomiallyBounded (fun n => (D.circuit n).size) := by
  have hview : ComputableTidilyInPolyTime
      (fun c : Σ m, Circuit Boolean.signature m 1 => (c.1, c.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have hlength : PolynomiallyBounded (fun n => (D.circuit n).code.1.length) :=
    ((ComputableTidilyInPolyTime.length_list Boolean.encGate).comp
      (hview.snd'.fst'.comp hD.tidy)).polynomiallyBounded
  exact hlength.mono_of_le (fun n => (Circuit.length_code_fst (D.circuit n)).ge)

include hkeyGen hencrypt in
/-- The constructed scheme's actual key generator is strict PPT. -/
@[fun_prop]
theorem isPPTOn_scheme_keyGen :
    IsPPTOn encUnary (encPair encBits encBits) (scheme D).keyGen :=
  isPPTOn_keyGen hkeyGen hencrypt (.of_tidy (by fun_prop))

include hencrypt in
/-- The constructed scheme's actual encryption algorithm is strict PPT. -/
@[fun_prop]
theorem isPPTOn_scheme_encrypt :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => (scheme D).encrypt p.1 p.2.1 p.2.2) := by
  apply isPPTOn_encrypt hencrypt <;> fun_prop

include hD in
/-- The constructed scheme's actual decryption algorithm is total polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_scheme_decrypt :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (scheme D).decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  apply computableInPolyTime_decrypt D hD <;> fun_prop

include hencrypt hevaluate hD in
/-- The constructed scheme's actual evaluator is strict PPT uniformly in the full circuit. -/
@[fun_prop]
theorem isPPTOn_scheme_evaluate :
    IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
      encBits (fun p => (scheme D).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply isPPTOn_evaluate hencrypt D hD hevaluate <;> fun_prop

end Cslib.Crypto.Homomorphic.FixedKey
