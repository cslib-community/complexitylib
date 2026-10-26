/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Basic
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.PolyTime
public import Complexity.Crypto.Computational.Homomorphic.Evaluation.PolyTime
public import Complexity.Computability.Circuit.Boolean.Layered.Padding.PolyTime
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


import Diag1155.Measure
/-!
# Uniform native certificates for the depth-budgeted scheme

These certificates compose the actual sampler, serializers, total decoders, circuit compiler,
identity padding, encrypted evaluator and tags. Both the security parameter and depth budget
use unary encodings. The same polynomial bound therefore applies as the budget varies; the
proofs do not fix a different hidden clock for each budget. Efficient unary budget families can
then be substituted for the second parameter.

The bounds charge the complete key artifacts, circuit code and input ciphertext lists. They
also cover malformed keys, wrong-width ciphertexts, and circuits exceeding the budget. No
correctness or valid-input premise supplies a runtime bound. Total decryption executes the
generated circuit, so no separate runtime assumption on the base decryption function is needed.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_keyGen`: uniform generation in the parameter and budget.
* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_encrypt`: fresh tagged encryption.
* `Cslib.Crypto.Homomorphic.Leveled.computableInPolyTime_decrypt`: total tagged decryption.
* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_evaluate`: uniform evaluation of the complete circuit.
* `Cslib.Crypto.Homomorphic.Leveled.polynomiallyBounded_widths`: polynomial secret-key and
  ciphertext widths follow from the native decryption-circuit generator.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Probability Turing.MultiTapeTM

variable {α : Type} {input : α ↪ List Bool}

/-- Serialize public projections and two secret endpoints, including the complete output words. -/
@[fun_prop]
theorem computableInPolyTime_keyPair {depth : α → ℕ}
    {keys : α → List (List Bool × List Bool)} {links : α → List (List (List Bool))}
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList (encPair encBits encBits)))
    (hlinks : ComputableInPolyTime links input (encList (encList encBits))) :
    ComputableInPolyTime (fun a => keyPair (depth a) (keys a) (links a))
      input (encPair encBits encBits) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hdepth
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hkeys
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hlinks
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  have hpublic := ((ComputableTidilyInPolyTime.fst encBits encBits).map.comp hkeys).prod hlinks
  have hfirst := (ComputableTidilyInPolyTime.listGetD
    (encA := encPair encBits encBits) ([], [])).comp
      (hkeys.prod (ComputableTidilyInPolyTime.const 0))
  have hlast := (ComputableTidilyInPolyTime.listGetD
    (encA := encPair encBits encBits) ([], [])).comp (hkeys.prod hdepth)
  exact hpublic.encoded.prod (hfirst.snd'.prod hlast.snd').encoded

variable {E : Scheme}
  (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
  (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => E.encrypt p.1 p.2.1 p.2.2))
  {n budget : α → ℕ} {pk sk ciphertext : α → List Bool}

include hkeyGen hencrypt in
/-- The key sampler has one native clock uniform in both unary parameters. -/
@[fun_prop]
theorem isPPTOn_keyGen
    (hn : ComputableInPolyTime n input encUnary)
    (hbudget : ComputableInPolyTime budget input encUnary) :
    IsPPTOn input (encPair encBits encBits) (fun a => keyGen E (n a) (budget a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hbudget
  apply (Scheme.isPPTOn_generateKeyChain hkeyGen hencrypt (.of_tidy hn)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => 2 * budget a) input encUnary by
      fun_prop))).map_with
  apply computableInPolyTime_keyPair <;> exact .of_tidy (by fun_prop)

include hencrypt in
/-- Decode every public word, encrypt under its initial key, and add the fresh tag. -/
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
  have hfirst := (ComputableTidilyInPolyTime.listGetD (encA := encBits) []).comp
    (hpublic.fst'.prod (ComputableTidilyInPolyTime.const 0))
  exact (hencrypt.preprocess (.of_tidy (hn.prod (hfirst.prod hbit)))).map (by fun_prop)

variable {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)
  (hD : ComputableInPolyTime
    (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
    encUnary (Boolean.encCircuit 1))

include hD in
/-- Decryption is polynomial time on every encoded input and contains no budget parameter. -/
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
  have hendpoints := secretKeyDecoder.computableInPolyTime.tidy.comp hsk
  have hhead := (ComputableTidilyInPolyTime.headD (encA := encBool) false).comp hc
  have hsecret := hhead.cond hendpoints.snd' hendpoints.fst'
  exact (Boolean.computableInPolyTime_evalCircuit (.of_tidy (hD.tidy.comp hn))
    (.of_tidy (hsecret.bitsAppend (ComputableTidilyInPolyTime.bitsTail.comp hc)))).tidy

variable (hevaluate : IsPPTOn
    (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
    encBits (fun p => E.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))

include hencrypt hevaluate hD in
/-- Compile, pad, evaluate and select outputs uniformly in the full raw code and unary budget. -/
@[fun_prop]
theorem isPPTOn_evaluateCircuit {inputCount : α → ℕ}
    {publicKeys inputs : α → List (List Bool)} {links : α → List (List (List Bool))}
    {code : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hbudget : ComputableInPolyTime budget input encUnary)
    (hpks : ComputableInPolyTime publicKeys input (encList encBits))
    (hlinks : ComputableInPolyTime links input (encList (encList encBits)))
    (hinputs : ComputableInPolyTime inputs input (encList encBits))
    (hcount : ComputableInPolyTime inputCount input encUnary)
    (hcode : ComputableInPolyTime code input Boolean.encCode) :
    IsPPTOn input (encList encBits)
      (fun a => evaluateCircuit D (n a) (budget a) (publicKeys a) (links a) (inputs a)
        (inputCount a) (code a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hbudget
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hpks
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hlinks
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hinputs
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcount
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcode
  have hcompiled := (Boolean.Layered.computableInPolyTime_compile (.of_tidy hcount) (.of_tidy
    hcode)).tidy
  have hpadded := (Boolean.Layered.computableInPolyTime_padTo (.of_tidy hcount)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => 2 * budget a) input encUnary by fun_prop))
    (.of_tidy hcompiled.fst')).tidy
  apply (Scheme.isPPTOn_evaluateLayers D hencrypt hevaluate hD (.of_tidy hn)
    (.of_tidy hpks) (.of_tidy hlinks) (.of_tidy hinputs) (.of_tidy hpadded)).map_with
  apply Turing.MultiTapeTM.ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.mapWithInput
    (hcompiled.snd'.comp (ComputableTidilyInPolyTime.fst _ _))
  exact ComputableTidilyInPolyTime.listGetD_binary [] (by fun_prop) (by fun_prop)

include hencrypt hevaluate hD in
/-- The actual scheme evaluator is strict PPT, including on malformed artifacts and on circuits
outside the chosen depth budget. The native certificate charges the complete circuit input. -/
@[fun_prop]
theorem isPPTOn_evaluate {c : α → Σ m, Circuit Boolean.signature m 1}
    {inputs : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary)
    (hbudget : ComputableInPolyTime budget input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hc : ComputableInPolyTime c input (Boolean.encCircuit 1))
    (hinputs : ComputableInPolyTime inputs input (encList encBits)) :
    IsPPTOn input encBits
      (fun a => evaluate D (n a) (budget a) (pk a) (c a) (inputs a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hn
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hbudget
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hpk
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hc
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hinputs
  have hpublic := publicKeyDecoder.computableInPolyTime.tidy.comp hpk
  have hview : ComputableTidilyInPolyTime
      (fun C : Σ m, Circuit Boolean.signature m 1 => (C.1, C.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have hparts := hview.comp hc
  apply (isPPTOn_evaluateCircuit hencrypt D hD hevaluate (.of_tidy hn) (.of_tidy hbudget)
    (.of_tidy ((ComputableTidilyInPolyTime.listTail encBits).comp hpublic.fst'))
    (.of_tidy hpublic.snd') (.of_tidy (ComputableTidilyInPolyTime.bitsTail.map.comp hinputs))
    (.of_tidy hparts.fst') (.of_tidy hparts.snd')).map
  exact ComputableInPolyTime.bitsCons (by fun_prop)
    (ComputableInPolyTime.headD [])

include hD in
/-- The circuit generator emits its input arity in unary. Its native runtime certificate
therefore bounds both base widths and the two derived widths polynomially in `n`, independently
of the depth budget. No separate polynomial-width assumption is needed. -/
theorem polynomiallyBounded_widths :
    PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) := by
  have hview : ComputableTidilyInPolyTime
      (fun c : Σ m, Circuit Boolean.signature m 1 => (c.1, c.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have htotal : PolynomiallyBounded (fun n => secretWidth n + ciphertextWidth n) :=
    (hview.fst'.comp hD.tidy).polynomiallyBounded
  have hsecret : PolynomiallyBounded secretWidth :=
    htotal.mono_of_le (fun n => Nat.le_add_right (secretWidth n) (ciphertextWidth n))
  have hciphertext : PolynomiallyBounded ciphertextWidth :=
    htotal.mono_of_le (fun n => Nat.le_add_left (ciphertextWidth n) (secretWidth n))
  constructor <;> fun_prop

include hkeyGen hencrypt in
/-- Substitute an efficiently computed unary depth budget into the constructed key generator. -/
@[fun_prop]
theorem isPPTOn_scheme_keyGen (budget : ℕ → ℕ)
    (hbudget : ComputableInPolyTime budget encUnary encUnary) :
    IsPPTOn encUnary (encPair encBits encBits) (scheme D budget).keyGen := by
  have hbudget := hbudget.tidy
  exact isPPTOn_keyGen hkeyGen hencrypt (by fun_prop) (.of_tidy hbudget)

include hencrypt in
/-- The constructed scheme's encryption certificate does not depend on computing its budget. -/
@[fun_prop]
theorem isPPTOn_scheme_encrypt (budget : ℕ → ℕ) :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => (scheme D budget).encrypt p.1 p.2.1 p.2.2) := by
  apply isPPTOn_encrypt hencrypt <;> fun_prop

include hD in
/-- The constructed decryption algorithm and its polynomial clock are independent of the budget. -/
@[fun_prop]
theorem computableInPolyTime_scheme_decrypt (budget : ℕ → ℕ) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (scheme D budget).decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  apply computableInPolyTime_decrypt D hD <;> fun_prop

include hencrypt hevaluate hD in
/-- An efficient unary budget yields one uniform certificate for the constructed evaluator. -/
@[fun_prop]
theorem isPPTOn_scheme_evaluate (budget : ℕ → ℕ)
    (hbudget : ComputableInPolyTime budget encUnary encUnary) :
    IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Boolean.encCircuit 1) (encList encBits))))
      encBits (fun p => (scheme D budget).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hbudget
  apply isPPTOn_evaluate hencrypt D hD hevaluate <;> fun_prop

end Cslib.Crypto.Homomorphic.Leveled
