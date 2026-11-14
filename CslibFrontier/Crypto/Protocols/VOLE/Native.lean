/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.AdaptiveMulCheck
public import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.Product

/-!
# List programs for masked VOLE receiver simulation

The ring is fixed. A layout map extracts the wire count and gate list from the full runtime input.
Receiver callbacks retain that input and explicit state through initialization, challenge selection,
reply processing and termination. Their first-message carrier is supplied independently.
`Receiver.strategy` adapts them to the existing strategy type, reading the same cached receiver
share in each phase. This is a first-order subclass of receivers, not a representation of arbitrary
higher-order strategy trees. The simulator samples one fresh affine mask per execution.

`Receiver.mapFirst` can preprocess corrections using public input and the receiver's own share.
The exact law retains the raw correction-based `View` and concerns the resulting receiver adapter.
It does not assert that an arbitrary transformed message is sender-realizable. A protocol that
sends a richer first message needs its own reconstruction law before expanding this raw view.

## Main definitions

* `Native.Gate`, `Native.Input`, `Native.Share`, `Native.View`: native circuit, share, and
  receiver view records.
* `Native.Receiver`: the four stateful probabilistic callbacks.
* `Native.Receiver.strategy`: their role-local interactive realization.
* `Native.Receiver.mapFirst`: preprocessing the first-message callback without changing state flow.
* `Native.simulate`: the witness-free list program.
* `Native.checkValue`: total list implementation of the receiver's weighted equation.

## Main results

* `Native.checkValue_ofFn`: agreement with the finite-vector algebraic check.
* `Native.eval_simulate`: exact realization of the existing typed simulator.
* `Native.receiverView_eq_eval_simulate`: exact native simulation of the actual receiver view.

The realization results here are original; the ideal algebra and source mapping are in
`VOLE.AdaptiveMulCheck` and `VOLE.MaskedMulCheck`.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.Native

open Probability Interactive Interactive.Spec
open scoped BigOperators

/-- One multiplication gate of a native circuit, with left, right, and output wire indices. -/
@[ext]
structure Gate where
  /-- Left input wire index. -/
  left : ℕ
  /-- Right input wire index. -/
  right : ℕ
  /-- Output product wire index. -/
  output : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Runtime wire count and ordered multiplication gates. -/
@[ext]
structure Input where
  /-- Number of witness wires before the fresh mask wire. -/
  wires : ℕ
  /-- Ordered multiplication gates. -/
  gates : List Gate
  deriving DecidableEq, Repr, Inhabited

/-- Receiver key and tags, including the final fresh-mask tag. -/
@[ext]
structure Share (F : Type) where
  /-- Global VOLE key held by the receiver. -/
  key : F
  /-- Receiver tags for each witness wire and the trailing fresh mask. -/
  tags : List F
  deriving DecidableEq, Repr, Inhabited

/-- Receiver share, raw corrections, normalized weights, affine reply and terminal private
result. -/
@[ext]
structure View (F Result : Type) where
  /-- Receiver's sampled VOLE key and tags. -/
  share : Share F
  /-- Raw commitment corrections for each witness wire. -/
  corrections : List F
  /-- Normalized challenge weight per gate. -/
  weights : List F
  /-- Blinded affine reply `(a, b)`. -/
  reply : F × F
  /-- Terminal private output of the receiver callback. -/
  result : Result
  deriving DecidableEq, Repr, Inhabited

variable {F I First State Result : Type}

/-- Explicit-state receiver callbacks. Each phase receives the public input and its own private
setup share. Private randomness may be saved in `State` for subsequent phases. -/
structure Receiver (F I First State Result : Type) where
  /-- Initialization before receiving the corrections. -/
  init : I → Share F → ProbComp State
  /-- Adaptive public weights and retained state after the supplied first message. -/
  challenge : I → Share F → State → First → ProbComp (List F × State)
  /-- Process the affine reply. -/
  receive : I → Share F → State → F × F → ProbComp State
  /-- Return the receiver's private result. -/
  terminal : I → Share F → State → ProbComp Result

/-- Preprocess only the receiver's first-message callback. The map may use the receiver's own
share; this operation alone makes no claim that a sender can produce the transformed message. -/
def Receiver.mapFirst {Message : Type} (receiver : Receiver F I First State Result)
    (first : I → Share F → Message → First) : Receiver F I Message State Result where
  init := receiver.init
  challenge input share state message :=
    receiver.challenge input share state (first input share message)
  receive := receiver.receive
  terminal := receiver.terminal

/-- Identity preprocessing leaves every callback and its captured state unchanged. -/
@[simp] theorem Receiver.mapFirst_id (receiver : Receiver F I First State Result) :
    receiver.mapFirst (fun _ _ message => message) = receiver := by
  cases receiver
  rfl

variable [CommRing F]

/-- Exactly `count` weights: missing entries are zero and excess entries are discarded. -/
def weights (count : ℕ) (r : List F) : List F :=
  (List.range count).map (fun i => r.getD i 0)

/-- Total list evaluation. Gate indices are looked up in the existing lists; their numeric values
never determine an allocation or loop bound. The wire count selects the fresh mask's tag. -/
def checkValue (input : Input) (share : Share F) (d r : List F) : F :=
  let adjusted := fun i => share.tags.getD i 0 + d.getD i 0 * share.key
  ((input.gates.zip (weights input.gates.length r)).map fun (gate, weight) =>
    weight * (adjusted gate.left * adjusted gate.right - adjusted gate.output * share.key)).sum +
      share.tags.getD input.wires 0

/-- The supplied sampler is called independently for the key, each tag/correction, and the final
affine coefficient. Exactness and efficient realization are separate sampler hypotheses. The first
message map preprocesses only the receiver callback; the returned view retains raw corrections. -/
def simulate (sample : ProbComp F) (receiver : Receiver F I First State Result)
    (layout : I → Input) (first : I → Share F → List F → First) (input : I) :
    ProbComp (View F Result) := do
  let shape := layout input
  let delta ← sample
  let q ← OracleComp.replicate (shape.wires + 1) sample
  let share : Share F := ⟨delta, q⟩
  let s ← receiver.init input share
  let d ← OracleComp.replicate shape.wires sample
  let (r, s) ← receiver.challenge input share s (first input share d)
  let r := weights shape.gates.length r
  let a ← sample
  let reply := (a, checkValue shape share d r - a * delta)
  let s ← receiver.receive input share s reply
  let result ← receiver.terminal input share s
  return ⟨share, d, r, reply, result⟩

/-- The adapter reads the actual cached share at every phase, rather than passing setup state
through the prover interface. The returned strategies retain the sampled callback state. The
first-message encoder and weight-index map specify the typed message carriers; this semantic
adapter alone carries no runtime certificate for those maps. -/
def Receiver.strategy {Message Index : Type} (receiver : Receiver F I First State Result)
    (n : ℕ) (encodeFirst : Message → First) (index : Index → ℕ) (input : I) :
    ProbOracleComp (voleReceiverSpec F (n + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (n + 1)))
        (threeMoveSpec Message (Index → F) (F × F)) Result) := do
  let share ← ProbOracleComp.query ()
  let state ← ProbOracleComp.sample (receiver.init input ⟨share.1, List.ofFn share.2⟩)
  return fun message => do
    let share ← ProbOracleComp.query ()
    let (r, state) ← ProbOracleComp.sample
      (receiver.challenge input ⟨share.1, List.ofFn share.2⟩ state (encodeFirst message))
    return (show ProbOracleComp (voleReceiverSpec F (n + 1))
      ((Index → F) × ((F × F) → ProbOracleComp (voleReceiverSpec F (n + 1))
        (ProbOracleComp (voleReceiverSpec F (n + 1)) Result))) from
      pure ((fun i => r.getD (index i) 0), fun reply => do
      let share ← ProbOracleComp.query ()
      let state ← ProbOracleComp.sample
        (receiver.receive input ⟨share.1, List.ofFn share.2⟩ state reply)
      return (do
        let share ← ProbOracleComp.query ()
        ProbOracleComp.sample (receiver.terminal input ⟨share.1, List.ofFn share.2⟩ state))))

/-- Public input representing finite wire maps; binary indices retain repeated wires. -/
def inputOfMaps {n m : ℕ} (left right output : Fin m → Fin n) : Input :=
  ⟨n, List.ofFn (fun i => ⟨(left i).val, (right i).val, (output i).val⟩)⟩

/-- List representation of the full typed receiver view, including its private share. -/
def viewToLists {n m : ℕ} :
    ((F × (Fin (n + 1) → F)) × Transcript (maskedMulCheckSpec F (Fin m) n) × Result) →
      View F Result :=
  fun (share, (d, r, reply, ()), result) =>
    ⟨⟨share.1, List.ofFn share.2⟩, List.ofFn d, List.ofFn r, reply, result⟩

/-- The transmitted list is precisely the adapter's finite weight vector. -/
theorem weights_eq_ofFn (count : ℕ) (r : List F) :
    weights count r = List.ofFn (fun i : Fin count => r.getD i.val 0) := by
  apply List.ext_getElem (by simp [weights])
  intro i hi hi'
  simp [weights]

/-- Normalization leaves an already correctly sized vector unchanged. -/
theorem weights_ofFn {m : ℕ} (r : Fin m → F) : weights m (List.ofFn r) = List.ofFn r := by
  rw [weights_eq_ofFn]
  congr 1 with i : 1
  simp

/-- The total list algorithm agrees with the existing algebraic check on valid wire maps. -/
theorem checkValue_ofFn {n m : ℕ} (left right output : Fin m → Fin n)
    (delta : F) (q : Fin (n + 1) → F) (d : Fin n → F) (r : Fin m → F) :
    checkValue (inputOfMaps left right output) ⟨delta, List.ofFn q⟩
      (List.ofFn d) (List.ofFn r) = maskedMulCheckValue left right output delta q d r := by
  simp only [checkValue, inputOfMaps, List.length_ofFn, weights_ofFn]
  have hzip :
      (List.ofFn (fun i => (⟨(left i).val, (right i).val, (output i).val⟩ : Gate))).zip
        (List.ofFn r) = List.ofFn (fun i =>
          ((⟨(left i).val, (right i).val, (output i).val⟩ : Gate), r i)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  rw [hzip, List.map_ofFn, List.sum_ofFn]
  simp only [maskedMulCheckValue, voleAdjustReceiver, Fin.init]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_def, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      (left i).isLt, (right i).isLt, (output i).isLt,
      Nat.lt_succ_of_lt (left i).isLt, Nat.lt_succ_of_lt (right i).isLt,
      Nat.lt_succ_of_lt (output i).isLt, ↓reduceDIte, Option.getD_some]
    rfl
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Nat.lt_succ_self, ↓reduceDIte, Option.getD_some]
    rfl

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
private theorem eval_replicate_sample (sample : ProbComp F)
    (hsample : ProbComp.eval sample = PMF.uniformOfFintype F) (count : ℕ) :
    ProbComp.eval (OracleComp.replicate count sample) =
      (PMF.uniformOfFintype (Fin count → F)).map List.ofFn := by
  apply ProbComp.eval_replicate_of_uniform count sample id
  simpa only [PMF.map_id] using hsample

omit [DecidableEq F] in
/-- The native program realizes the existing typed simulator, including all private callback
state effects. The public input and vector dimensions are tied by the explicit layout equality. -/
theorem eval_simulate {n m : ℕ} (left right output : Fin m → Fin n)
    (sample : ProbComp F) (hsample : ProbComp.eval sample = PMF.uniformOfFintype F)
    (receiver : Receiver F I First State Result) (layout : I → Input)
    (first : I → Share F → List F → First) (input : I)
    (hlayout : layout input = inputOfMaps left right output) :
    ProbComp.eval (simulate sample receiver layout first input) =
      (ProbComp.eval (maskedMulCheckReceiverSimulate left right output
        ((receiver.mapFirst first).strategy n List.ofFn (Fin.val (n := m))) input)).map
          viewToLists := by
  simp only [simulate, hlayout, maskedMulCheckReceiverSimulate, Receiver.strategy,
    Receiver.mapFirst, OracleComp.interpret_bind, OracleComp.interpret_pure, ProbOracleComp.query,
    OracleComp.interpret_query, OracleComp.sumHandler, ProbOracleComp.interpret_sample,
    OracleComp.interpret_query_eq_self, pure_bind, bind_assoc, ProbComp.eval_bind,
    ProbComp.eval_pure,
    ProbComp.eval_uniform, hsample, eval_replicate_sample sample hsample,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, inputOfMaps, List.length_ofFn]
  simp only [Function.comp_def, weights_eq_ofFn, viewToLists]
  have hv (delta : F) (q : Fin (n + 1) → F) (d : Fin n → F) (r : Fin m → F) :=
    checkValue_ofFn left right output delta q d r
  simp only [inputOfMaps] at hv
  simp only [hv]

/-- Exact native full-view simulation for satisfying witnesses and supplied receiver callbacks.
The actual cached World runs the receiver with first-message preprocessing. The returned view
retains the raw corrections; a sender-realizable transformed transcript needs a separate law. -/
theorem receiverView_eq_eval_simulate {n m : ℕ} (left right output : Fin m → Fin n)
    (sample : ProbComp F) (hsample : ProbComp.eval sample = PMF.uniformOfFintype F)
    (receiver : Receiver F I First State Result) (layout : I → Input)
    (first : I → Share F → List F → First) (input : I)
    (hlayout : layout input = inputOfMaps left right output) (w : Fin n → F)
    (hw : ∀ i, w (left i) * w (right i) = w (output i)) :
    (maskedMulCheckReceiverView left right output
      ((receiver.mapFirst first).strategy n List.ofFn (Fin.val (n := m))) w input).map viewToLists =
        ProbComp.eval (simulate sample receiver layout first input) := by
  rw [maskedMulCheckReceiverView_eq_simulate left right output _ w _ hw,
    eval_simulate left right output sample hsample receiver layout first input hlayout]

end Cslib.Crypto.Protocols.VOLE.Native
