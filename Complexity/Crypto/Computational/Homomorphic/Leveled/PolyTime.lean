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
* `Cslib.Crypto.Homomorphic.Leveled.isPPTOn_evaluateHop`: uniform evaluation of one depth-bounded
  hop.
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
  have hpublic := ((ComputableInPolyTime.fst encBits encBits).map.comp hkeys).prod hlinks
  have hfirst := (ComputableInPolyTime.listGetD
    (encA := encPair encBits encBits) ([], [])).comp
      (hkeys.prod (ComputableInPolyTime.const 0))
  have hlast := (ComputableInPolyTime.listGetD
    (encA := encPair encBits encBits) ([], [])).comp (hkeys.prod hdepth)
  exact (hpublic.of_enc_eq fun _ => rfl).prod
    ((hfirst.snd'.prod hlast.snd').of_enc_eq fun _ => rfl)

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
  apply (Scheme.isPPTOn_generateKeyChain hkeyGen hencrypt hn
    (show ComputableInPolyTime (fun a => 2 * budget a) input encUnary by
      fun_prop)).map_with
  apply computableInPolyTime_keyPair <;> fun_prop

include hencrypt in
/-- Decode every public word, encrypt under its initial key, and add the fresh tag. -/
@[fun_prop]
theorem isPPTOn_encrypt {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBits (fun a => encrypt E (n a) (pk a) (bit a)) := by
  have hpublic := publicKeyDecoder.computableInPolyTime.comp hpk
  have hfirst := (ComputableInPolyTime.listGetD (encA := encBits) []).comp
    (hpublic.fst'.prod (ComputableInPolyTime.const 0))
  exact (hencrypt.preprocess (hn.prod (hfirst.prod hbit))).map (by fun_prop)

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
  have hendpoints := secretKeyDecoder.computableInPolyTime.comp hsk
  have hhead := (ComputableInPolyTime.headD (encA := encBool) false).comp hc
  have hsecret := hhead.ite hendpoints.snd' hendpoints.fst'
  exact Boolean.computableInPolyTime_evalCircuit (hD.comp hn)
    (hsecret.bitsAppend (ComputableInPolyTime.bitsTail.comp hc))

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
  have hcompiled := Boolean.Layered.computableInPolyTime_compile hcount hcode
  have hpadded := Boolean.Layered.computableInPolyTime_padTo hcount
    (show ComputableInPolyTime (fun a => 2 * budget a) input encUnary by fun_prop)
    hcompiled.fst'
  apply (Scheme.isPPTOn_evaluateLayers D hencrypt hevaluate hD hn
    hpks hlinks hinputs hpadded).map_with
  apply ComputableInPolyTime.mapWithInput
    (hcompiled.snd'.comp (ComputableInPolyTime.fst _ _))
  exact ComputableInPolyTime.listGetD_binary [] (by fun_prop) (by fun_prop)

include hencrypt hevaluate in
/-- Hop evaluation is strict PPT uniformly in the security parameter, depth offset, step budget,
public key, circuit, and input ciphertexts. -/
@[fun_prop]
theorem isPPTOn_evaluateHop
    (hcircuits : ComputableInPolyTime
      (fun n => (⟨_, D.circuit n⟩ : Σ m, Circuit Boolean.signature m 1))
      encUnary (Boolean.encCircuit 1))
    {offset step : α → ℕ}
    {c : α → Σ m, Circuit Boolean.signature m 1}
    {inputs : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary)
    (hoffset : ComputableInPolyTime offset input encUnary)
    (hstep : ComputableInPolyTime step input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hc : ComputableInPolyTime c input (Boolean.encCircuit 1))
    (hinputs : ComputableInPolyTime inputs input (encList encBits)) :
    IsPPTOn input encBits
      (fun a => evaluateHop D (n a) (offset a) (step a) (pk a) (c a) (inputs a)) := by
  have hpublic := publicKeyDecoder.computableInPolyTime.comp hpk
  have hview : ComputableInPolyTime
      (fun C : Σ m, Circuit Boolean.signature m 1 => (C.1, C.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have hparts := hview.comp hc
  have hdrop : ComputableInPolyTime (fun a => 2 * offset a) input encUnary := by
    fun_prop
  have htail : ComputableInPolyTime (List.tail (α := List Bool))
      (encList encBits) (encList encBits) := by
    simpa only [Function.comp_def, List.drop_one] using
      (ComputableInPolyTime.dropUnary (encA := encBits) (encL := encList encBits)).comp
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1))
  have hpks := (ComputableInPolyTime.dropUnary (encA := encBits) (encL := encList encBits)).comp
    ((htail.comp hpublic.fst').prod hdrop)
  have hlinks := (ComputableInPolyTime.dropUnary (encA := encList encBits)
    (encL := encList (encList encBits))).comp (hpublic.snd'.prod hdrop)
  apply (isPPTOn_evaluateCircuit hencrypt D hcircuits hevaluate hn hstep hpks hlinks
    (ComputableInPolyTime.bitsTail.map.comp hinputs) hparts.fst' hparts.snd').map
  exact ComputableInPolyTime.bitsCons (by fun_prop)
    (ComputableInPolyTime.headD [])

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
  have hpublic := publicKeyDecoder.computableInPolyTime.comp hpk
  have hview : ComputableInPolyTime
      (fun C : Σ m, Circuit Boolean.signature m 1 => (C.1, C.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have hparts := hview.comp hc
  have htail : ComputableInPolyTime (List.tail (α := List Bool))
      (encList encBits) (encList encBits) := by fun_prop
  apply (isPPTOn_evaluateCircuit hencrypt D hD hevaluate hn hbudget
    (htail.comp hpublic.fst')
    hpublic.snd' (ComputableInPolyTime.bitsTail.map.comp hinputs)
    hparts.fst' hparts.snd').map
  exact ComputableInPolyTime.bitsCons (by fun_prop)
    (ComputableInPolyTime.headD [])

include hD in
/-- The circuit generator emits its input arity in unary. Its native runtime certificate
therefore bounds both base widths and the two derived widths polynomially in `n`, independently
of the depth budget. No separate polynomial-width assumption is needed. -/
theorem polynomiallyBounded_widths :
    PolynomiallyBounded (fun n => 3 * secretWidth n + 1) ∧
      PolynomiallyBounded (fun n => ciphertextWidth n + 1) := by
  have hview : ComputableInPolyTime
      (fun c : Σ m, Circuit Boolean.signature m 1 => (c.1, c.2.code))
      (Boolean.encCircuit 1) (encPair encUnary Boolean.encCode) := .of_eq fun _ => rfl
  have htotal : PolynomiallyBounded (fun n => secretWidth n + ciphertextWidth n) :=
    (hview.fst'.comp hD).polynomiallyBounded
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
  exact isPPTOn_keyGen hkeyGen hencrypt (by fun_prop) hbudget

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
  apply isPPTOn_evaluate hencrypt D hD hevaluate <;> fun_prop

end Cslib.Crypto.Homomorphic.Leveled
