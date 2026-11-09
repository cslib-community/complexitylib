/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Native
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Tactic.PPT

/-!
# Strict PPT realization of the native VOLE simulator

The scalar ring and its encoding are fixed before the input. The public-input encoding is supplied
and charged in every callback, along with polynomial-time layout extraction and first-message
preprocessing. Extracted wire counts use unary encoding; gate lists use binary wire indices, with
bounded list lookups even on malformed inputs. Lists, callback state and the full raw view are
charged explicitly. Four fixed callback invocations compose polynomially without a separate
iterative storage-growth assumption.

## Main definitions

* `Native.encInput`, `Native.encShare`, `Native.encView`: full data encodings.

## Main results

* `Native.computableInPolyTime_checkValue`: total polynomial-time list arithmetic.
* `Native.isPPTOn_simulate`: one uniform strict-PPT simulator for all runtime inputs.

The exact-uniform sampler law is used by `Native.receiverView_eq_eval_simulate`; runtime alone
does not imply that law. Conversely, finite uniformity alone does not certify a strict fair-coin
sampler. The tests instantiate both contracts over the two-element field represented by `Bool`.

This is an original runtime realization of the bounded ideal program, not a certificate for
arbitrary higher-order receivers or for a growing family of extension fields.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.Native

open Probability Turing.MultiTapeTM

/-- Gate indices are binary; the wire count is unary and every listed gate is charged. -/
def encInput : Input ↪ List Bool :=
  encPair encUnary (encList (encPair encNat (encPair encNat encNat)))

/-- The key and every receiver tag are explicitly encoded. -/
def encShare {F : Type} (eF : F ↪ List Bool) : Share F ↪ List Bool :=
  encPair eF (encList eF)

/-- The complete receiver output, including every correction and transmitted weight. -/
def encView {F Result : Type} (eF : F ↪ List Bool) (eResult : Result ↪ List Bool) :
    View F Result ↪ List Bool :=
  encPair (encShare eF) (encPair (encList eF)
    (encPair (encList eF) (encPair (encPair eF eF) eResult)))

variable {F α : Type} [CommRing F] [Finite F]
  {eF : F ↪ List Bool} {input : α ↪ List Bool}

omit [Finite F] in
/-- Weight normalization runs in polynomial time in the unary count and actual list length. -/
theorem computableInPolyTime_weights {count : α → ℕ} {r : α → List F}
    (hcount : ComputableInPolyTime count input encUnary)
    (hr : ComputableInPolyTime r input (encList eF)) :
    ComputableInPolyTime (fun a => weights (count a) (r a)) input (encList eF) := by
  unfold weights
  apply ComputableInPolyTime.mapWithInput
    ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range).comp hcount)
  exact (ComputableInPolyTime.listGetD (encA := eF) 0).comp
    ((hr.comp (.fst _ _)).prod (.snd _ _))

/-- List summation has fixed-size scalar accumulators. -/
private theorem polyTime_sum
    (hadd : ComputableInPolyTime (fun p : F × F => p.1 + p.2) (encPair eF eF) eF) :
    ComputableInPolyTime (List.sum : List F → F) (encList eF) eF := by
  let _ := Fintype.ofFinite F
  have h := ComputableInPolyTime.foldl' (encA := eF) (encL := encList eF)
    (encB := eF) (.id') (.const 0) hadd
    (B := fun _ => Finset.univ.sup (fun x : F => (eF x).length)) (.const _)
    (fun _ _ _ => Finset.le_sup (f := fun x : F => (eF x).length) (Finset.mem_univ _))
  change ComputableInPolyTime (fun xs : List F => xs.sum) (encList eF) eF
  simpa only [List.sum_eq_foldl] using h

/-- All lookups are polynomial in their binary index's encoded length, including indices beyond
the actual lists. Only the semantic bridge imposes valid gate indices. -/
theorem computableInPolyTime_checkValue
    (hadd : ComputableInPolyTime (fun p : F × F => p.1 + p.2) (encPair eF eF) eF)
    (hsub : ComputableInPolyTime (fun p : F × F => p.1 - p.2) (encPair eF eF) eF)
    (hmul : ComputableInPolyTime (fun p : F × F => p.1 * p.2) (encPair eF eF) eF) :
    ComputableInPolyTime (fun p : Input × Share F × List F × List F =>
      checkValue p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encInput (encPair (encShare eF) (encPair (encList eF) (encList eF)))) eF := by
  let e := encPair encInput (encPair (encShare eF) (encPair (encList eF) (encList eF)))
  let gateEnc := encPair encNat (encPair encNat encNat)
  have hg : ComputableInPolyTime (fun p : Input × Share F × List F × List F => p.1.2)
      e (encList gateEnc) := by unfold e encInput; fun_prop
  have hr : ComputableInPolyTime (fun p : Input × Share F × List F × List F =>
      weights p.1.2.length p.2.2.2) e (encList eF) :=
    computableInPolyTime_weights ((ComputableInPolyTime.length_list gateEnc).comp hg)
      (by unfold e; fun_prop)
  have hz := (ComputableInPolyTime.zip gateEnc eF).comp (hg.prod hr)
  have hterm : ComputableInPolyTime
      (fun p : (Input × Share F × List F × List F) × ((ℕ × ℕ × ℕ) × F) =>
        let adjusted := fun i => p.1.2.1.2.getD i 0 + p.1.2.2.1.getD i 0 * p.1.2.1.1
        p.2.2 * (adjusted p.2.1.1 * adjusted p.2.1.2.1 -
          adjusted p.2.1.2.2 * p.1.2.1.1))
      (encPair e (encPair gateEnc eF)) eF := by
    have hlookup (index : ((Input × Share F × List F × List F) × ((ℕ × ℕ × ℕ) × F)) → ℕ)
        (hi : ComputableInPolyTime index (encPair e (encPair gateEnc eF)) encNat) :
        ComputableInPolyTime (fun p => p.1.2.1.2.getD (index p) 0 +
          p.1.2.2.1.getD (index p) 0 * p.1.2.1.1)
          (encPair e (encPair gateEnc eF)) eF := by
      have hq : ComputableInPolyTime (fun p => p.1.2.1.2.getD (index p) 0)
          (encPair e (encPair gateEnc eF)) eF :=
        .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0
          (by unfold e encShare; fun_prop) hi.tidy)
      have hd : ComputableInPolyTime (fun p => p.1.2.2.1.getD (index p) 0)
          (encPair e (encPair gateEnc eF)) eF :=
        .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0
          (by unfold e; fun_prop) hi.tidy)
      unfold e encShare at *
      polytime
    have hl := hlookup (fun p => p.2.1.1) (by unfold gateEnc; fun_prop)
    have hr := hlookup (fun p => p.2.1.2.1) (by unfold gateEnc; fun_prop)
    have ho := hlookup (fun p => p.2.1.2.2) (by unfold gateEnc; fun_prop)
    dsimp only
    unfold e encShare gateEnc at *
    polytime
  have hsum := (polyTime_sum hadd).comp (ComputableInPolyTime.mapWithInput (f := fun p g =>
      g.2 * ((p.2.1.2.getD g.1.1 0 + p.2.2.1.getD g.1.1 0 * p.2.1.1) *
        (p.2.1.2.getD g.1.2.1 0 + p.2.2.1.getD g.1.2.1 0 * p.2.1.1) -
        (p.2.1.2.getD g.1.2.2 0 + p.2.2.1.getD g.1.2.2 0 * p.2.1.1) * p.2.1.1)) hz hterm)
  have hlast : ComputableInPolyTime
      (fun p : Input × Share F × List F × List F => p.2.1.2.getD p.1.1 0) e eF :=
    (ComputableInPolyTime.listGetD (encA := eF) 0).comp
      ((show ComputableInPolyTime (fun p => p.2.1.2) e (encList eF) by
        unfold e encShare; fun_prop).prod (by unfold e encInput; fun_prop))
  change ComputableInPolyTime _ e eF
  unfold checkValue
  polytime

variable {I First State Result : Type}

/-- A fixed ring's certified sampler and four certified callbacks give one strict fair-coin
machine over the complete encoded input. Layout extraction and first-message preprocessing are
charged, including their output growth; a runtime circuit cannot be hidden in a fixed callback
when invoking this theorem for a varying circuit input. The certificate is total even on malformed
layouts. It assumes no efficient realization of arbitrary strategy trees. -/
theorem isPPTOn_simulate (sample : ProbComp F) (receiver : Receiver F I First State Result)
    (layout : I → Input) (first : I → Share F → List F → First)
    (eInput : I ↪ List Bool) (eFirst : First ↪ List Bool)
    (eState : State ↪ List Bool) (eResult : Result ↪ List Bool)
    (hsample : IsPPTOn encUnit eF (fun _ : Unit => sample))
    (hadd : ComputableInPolyTime (fun p : F × F => p.1 + p.2) (encPair eF eF) eF)
    (hsub : ComputableInPolyTime (fun p : F × F => p.1 - p.2) (encPair eF eF) eF)
    (hmul : ComputableInPolyTime (fun p : F × F => p.1 * p.2) (encPair eF eF) eF)
    (hlayout : ComputableInPolyTime layout eInput encInput)
    (hfirst : ComputableInPolyTime (fun p : I × Share F × List F => first p.1 p.2.1 p.2.2)
      (encPair eInput (encPair (encShare eF) (encList eF))) eFirst)
    (hinit : IsPPTOn (encPair eInput (encShare eF)) eState
      (fun p : I × Share F => receiver.init p.1 p.2))
    (hchallenge : IsPPTOn
      (encPair eInput (encPair (encShare eF) (encPair eState eFirst)))
      (encPair (encList eF) eState)
      (fun p : I × Share F × State × First =>
        receiver.challenge p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hreceive : IsPPTOn
      (encPair eInput (encPair (encShare eF) (encPair eState (encPair eF eF)))) eState
      (fun p : I × Share F × State × (F × F) =>
        receiver.receive p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hterminal : IsPPTOn (encPair eInput (encPair (encShare eF) eState)) eResult
      (fun p : I × Share F × State => receiver.terminal p.1 p.2.1 p.2.2)) :
    IsPPTOn eInput (encView eF eResult) (simulate sample receiver layout first) := by
  have hsamples : IsPPTOn encUnary (encList eF)
      (fun n => OracleComp.replicate n sample) :=
    (hsample.preprocess (ComputableInPolyTime.const ())).replicate .id'
  have hc := computableInPolyTime_checkValue hadd hsub hmul
  have hfinish : IsPPTOn
      (encPair eInput (encPair (encShare eF) (encPair (encList eF)
        (encPair (encList eF) (encPair eState (encPair eF eF))))))
      (encView eF eResult)
      (fun p : I × Share F × List F × List F × State × (F × F) => do
        let state ← receiver.receive p.1 p.2.1 p.2.2.2.2.1 p.2.2.2.2.2
        let result ← receiver.terminal p.1 p.2.1 state
        return (p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.2, result)) := by
    apply IsPPTOn.bind_with (left := eState)
    · apply hreceive.preprocess
        (prepare := fun p : I × Share F × List F × List F × State × (F × F) =>
          (p.1, p.2.1, p.2.2.2.2.1, p.2.2.2.2.2))
      fun_prop
    simp only [bind_pure_comp]
    apply IsPPTOn.map_with
    · apply hterminal.preprocess (prepare := fun p :
          (I × Share F × List F × List F × State × (F × F)) × State =>
        (p.1.1, p.1.2.1, p.2))
      fun_prop
    · unfold encView
      fun_prop
  unfold simulate encView encShare encInput at *
  apply IsPPTOn.bind_with (left := eF)
  · exact hsample.preprocess (ComputableInPolyTime.const ())
  apply IsPPTOn.bind_with (left := encList eF)
  · ppt
  apply IsPPTOn.bind_with (left := eState)
  · ppt
  apply IsPPTOn.bind_with (left := encList eF)
  · ppt
  apply IsPPTOn.bind_with (left := encPair (encList eF) eState)
  · ppt
  apply IsPPTOn.bind_with (left := eF)
  · exact hsample.preprocess (ComputableInPolyTime.const ())
  apply hfinish.preprocess (prepare := fun p :
      (((((I × F) × List F) × State) × List F) × (List F × State)) × F =>
    (p.1.1.1.1.1.1, (p.1.1.1.1.1.2, p.1.1.1.1.2), p.1.1.2,
      weights (layout p.1.1.1.1.1.1).2.length p.1.2.1, p.1.2.2,
      (p.2, checkValue (layout p.1.1.1.1.1.1) (p.1.1.1.1.1.2, p.1.1.1.1.2) p.1.1.2
        (weights (layout p.1.1.1.1.1.1).2.length p.1.2.1) - p.2 * p.1.1.1.1.1.2)))
  let e1 := encPair eInput eF
  let e2 := encPair e1 (encList eF)
  let e3 := encPair e2 eState
  let e4 := encPair e3 (encList eF)
  let e5 := encPair e4 (encPair (encList eF) eState)
  have hp := ComputableInPolyTime.fst e5 eF
  have ha := ComputableInPolyTime.snd e5 eF
  have hinput := hp.fst'.fst'.fst'.fst'.fst'
  have hdelta := hp.fst'.fst'.fst'.fst'.snd'
  have hq := hp.fst'.fst'.fst'.snd'
  have hd := hp.fst'.snd'
  have hraw := hp.snd'.fst'
  have hstate := hp.snd'.snd'
  have hshare := hdelta.prod hq
  have hshape := hlayout.comp hinput
  have hlen := (ComputableInPolyTime.length_list
    (encPair encNat (encPair encNat encNat))).comp hshape.snd'
  have hr := computableInPolyTime_weights hlen hraw
  have hvalue := hc.comp (hshape.prod (hshare.prod (hd.prod hr)))
  have hreply := ha.prod (hsub.comp (hvalue.prod (hmul.comp (ha.prod hdelta))))
  exact hinput.prod (hshare.prod (hd.prod (hr.prod (hstate.prod hreply))))

end Cslib.Crypto.Protocols.VOLE.Native
