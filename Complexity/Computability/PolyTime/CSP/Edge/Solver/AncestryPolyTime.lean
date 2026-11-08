/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Ancestry
import Complexity.Computability.PolyTime.CSP.Edge.Solver.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Native chronological ancestry compiler certificates

The backwards scan stores one actual parent pair and one unary copy timestamp per selected
expansion. A native-computable envelope of all possible parent records bounds full framed
storage on every raw log, including huge binary positions and names. This bookkeeping is
original and assumes no forest invariant or externally supplied resource certificate.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode encWalkCode)
open EdgeForest (ExpansionCode encExpansionCode MeetingCode encMeetingCode)

attribute [local fun_prop] NativeWalk.computableInPolyTime_portWith
  NativeWalk.computableInPolyTime_start NativeWalk.computableInPolyTime_steps
  NativeWalk.computableInPolyTime_mk

private theorem poly_start : ComputableInPolyTime TraceCode.start encTraceCode encNat :=
  encTraceCode_start_deg.computableInPolyTime
private theorem poly_steps : ComputableInPolyTime TraceCode.steps encTraceCode
    (encList (encPair encNat encNat)) := encTraceCode_steps_deg.computableInPolyTime
private theorem poly_times : ComputableInPolyTime TraceCode.times encTraceCode
    (encList encUnary) := encTraceCode_times_deg.computableInPolyTime
private theorem poly_traceMk : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × ℕ) × List ℕ => TraceCode.mk p.1 p.2.1 p.2.2)
    encTraceCodeFields encTraceCode := encTraceCode_mk_deg.computableInPolyTime
private theorem poly_expInput : ComputableInPolyTime ExpansionCode.input encExpansionCode encNat :=
  EdgeForest.encExpansionCode_input_deg.computableInPolyTime
private theorem poly_expOutputs : ComputableInPolyTime ExpansionCode.outputs encExpansionCode
    (encList encNat) := EdgeForest.encExpansionCode_outputs_deg.computableInPolyTime

attribute [local fun_prop] poly_start poly_steps poly_times poly_traceMk poly_expInput
  poly_expOutputs

/-- Body and log are framed, followed by an arbitrary initial backwards-scan suffix. -/
abbrev encTraceArgs := encPair (encCSP encTable encNat)
  (encPair (encList encExpansionCode) encTraceCode)

private abbrev TimedExpansion := ExpansionCode × ℕ
/-- Binary expansion positions, framed, followed by its unary actual timestamp. -/
private abbrev encTimedExpansion := encPair encExpansionCode encUnary

private def timed (es : List ExpansionCode) : List TimedExpansion :=
  es.zip (List.range es.length).reverse

private def atom (F : CSP Table ℕ) (e : TimedExpansion) (o : ℕ) : TraceCode :=
  ⟨(EdgeAugmenting.recordAt F e.1.input).2.2, [(e.1.input, o)], [e.2]⟩

private def atoms (F : CSP Table ℕ) (es : List ExpansionCode) : List TraceCode :=
  (timed es).flatMap fun e => e.1.outputs.map (atom F e)

private theorem poly_timed : ComputableInPolyTime timed (encList encExpansionCode)
    (encList encTimedExpansion) := by
  unfold timed
  fun_prop

private theorem poly_timedWith {α : Type} {e : α ↪ List Bool} {es : α → List ExpansionCode}
    (h : ComputableInPolyTime es e (encList encExpansionCode)) :
    ComputableInPolyTime (fun a => timed (es a)) e (encList encTimedExpansion) :=
  poly_timed.comp h

attribute [local fun_prop] poly_timedWith

private theorem poly_atoms : ComputableInPolyTime
    (fun p : CSP Table ℕ × List ExpansionCode × TraceCode => atoms p.1 p.2.1)
    encTraceArgs (encList encTraceCode) := by
  unfold atoms atom
  fun_prop

private theorem poly_traceStep : ComputableInPolyTime
    (fun p : ((CSP Table ℕ × List ExpansionCode × TraceCode) × TraceCode) × TimedExpansion =>
      traceStep p.1.1.1 p.1.2 p.2)
    (encPair (encPair encTraceArgs encTraceCode) encTimedExpansion) encTraceCode := by
  unfold traceStep
  fun_prop

private theorem traceStep_growth (F : CSP Table ℕ) (es : List ExpansionCode)
    (s : TraceCode) (e : TimedExpansion) (he : e ∈ timed es) :
    (encTraceCode (traceStep F s e)).length ≤ (encTraceCode s).length +
      (encList encTraceCode (atoms F es)).length := by
  unfold traceStep
  cases ho : e.1.outputs.find? (fun o => (EdgeAugmenting.recordAt F o).2.2 == s.start) with
  | none => simp
  | some o =>
    have hm : atom F e o ∈ atoms F es :=
      List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨o, List.mem_of_find?_eq_some ho, rfl⟩⟩
    have hb := length_le_encList_of_mem encTraceCode hm
    simp only [Option.elim_some]
    simp only [atom, encTraceCode_apply, encTraceCodeFields, length_encPair, encList_cons,
      encList_nil, List.length_append, length_frame, List.length_nil] at hb ⊢
    omega

/-- A backwards chronological scan is native polynomial-time on all raw logs and suffixes.
Every intermediate code is bounded by the full encoded parent-record envelope. -/
theorem computableInPolyTime_trace : ComputableInPolyTime
    (fun p : CSP Table ℕ × List ExpansionCode × TraceCode => trace p.1 p.2.1 p.2.2)
    encTraceArgs encTraceCode := by
  unfold trace
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encTimedExpansion) (encL := encList encTimedExpansion)
    (growth := fun p => (encList encTraceCode (atoms p.1 p.2.1)).length)
    (show ComputableInPolyTime (fun p : CSP Table ℕ × List ExpansionCode × TraceCode => p.2.2)
      encTraceArgs encTraceCode from by fun_prop).tidy
  · refine ⟨?_, poly_traceStep.tidy, inferInstance, inferInstance⟩
    exact (poly_timedWith (show ComputableInPolyTime
      (fun p : CSP Table ℕ × List ExpansionCode × TraceCode => p.2.1)
      encTraceArgs (encList encExpansionCode) from by fun_prop)).tidy
  · exact ⟨poly_atoms.polyBounded_length, fun p s e he => traceStep_growth p.1 p.2.1 s e he⟩

/-- Body and expansion log are framed, followed by the queried binary original name. -/
abbrev encAncestryArgs := encPair (encCSP encTable encNat)
  (encPair (encList encExpansionCode) encNat)

/-- Native root-path reconstruction on every raw expansion log. -/
theorem computableInPolyTime_ancestry : ComputableInPolyTime
    (fun p : CSP Table ℕ × List ExpansionCode × ℕ => ancestry p.1 p.2.1 p.2.2)
    encAncestryArgs encTraceCode := by
  unfold ancestry
  simpa only [Function.comp_def] using computableInPolyTime_trace.comp (show ComputableInPolyTime
    (fun p : CSP Table ℕ × List ExpansionCode × ℕ => (p.1, p.2.1, TraceCode.mk p.2.2 [] []))
    encAncestryArgs encTraceArgs from by fun_prop)

private theorem poly_ancestryWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {es : α → List ExpansionCode} {v : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (he : ComputableInPolyTime es e (encList encExpansionCode))
    (hv : ComputableInPolyTime v e encNat) :
    ComputableInPolyTime (fun a => ancestry (F a) (es a) (v a)) e encTraceCode := by
  simpa only [Function.comp_def] using computableInPolyTime_ancestry.comp (hF.prod (he.prod hv))

private theorem poly_nodes : ComputableInPolyTime
    (fun p : CSP Table ℕ × TraceCode => nodes p.1 p.2)
    (encPair (encCSP encTable encNat) encTraceCode) (encList encNodeCode) := by
  unfold nodes
  fun_prop

private theorem poly_nodesWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {p : α → TraceCode}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hp : ComputableInPolyTime p e encTraceCode) :
    ComputableInPolyTime (fun a => nodes (F a) (p a)) e (encList encNodeCode) := by
  simpa only [Function.comp_def] using poly_nodes.comp (hF.prod hp)

private theorem poly_takeWhileWith {α β : Type} {e : α ↪ List Bool}
    {eb : β ↪ List Bool} {xs : α → List β} {pred : α → β → Bool}
    (hx : ComputableInPolyTime xs e (encList eb))
    (hp : ComputableInPolyTime (fun p : α × β => pred p.1 p.2) (encPair e eb) encBool) :
    ComputableInPolyTime (fun a => (xs a).takeWhile (pred a)) e (encList eb) := by
  have hn := NativeWalk.computableInPolyTime_findIdxWith (pred := fun a b => !(pred a b)) hx
    (show ComputableInPolyTime (fun p : α × β => !(pred p.1 p.2))
      (encPair e eb) encBool from by fun_prop)
  simpa only [List.takeWhile_eq_take_findIdx_not] using
    (show ComputableInPolyTime
      (fun a => (xs a).take ((xs a).findIdx (fun b => !(pred a b)))) e (encList eb)
      from by fun_prop)

attribute [local fun_prop] poly_ancestryWith poly_nodesWith poly_takeWhileWith

/-- Body and left ancestry are framed, followed by the right ancestry with unary timestamps. -/
private abbrev encCommonArgs := encPair (encCSP encTable encNat)
  (encPair encTraceCode encTraceCode)

private theorem poly_common : ComputableInPolyTime
    (fun p : CSP Table ℕ × TraceCode × TraceCode => common p.1 p.2.1 p.2.2)
    encCommonArgs (encList encNodeCode) := by
  unfold common
  fun_prop

private theorem poly_commonWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {left right : α → TraceCode}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hl : ComputableInPolyTime left e encTraceCode)
    (hr : ComputableInPolyTime right e encTraceCode) :
    ComputableInPolyTime (fun a => common (F a) (left a) (right a)) e
      (encList encNodeCode) := by
  simpa only [Function.comp_def] using poly_common.comp (hF.prod (hl.prod hr))

private theorem poly_walk : ComputableInPolyTime walk encTraceCode encWalkCode := by
  unfold walk
  fun_prop

private theorem poly_appendWith {α : Type} {e : α ↪ List Bool} {p q : α → WalkCode}
    (hp : ComputableInPolyTime p e encWalkCode)
    (hq : ComputableInPolyTime q e encWalkCode) :
    ComputableInPolyTime (fun a => append (p a) (q a)) e encWalkCode := by
  unfold append
  fun_prop

attribute [local fun_prop] poly_commonWith poly_walk poly_appendWith
  NativeWalk.computableInPolyTime_takeWith NativeWalk.computableInPolyTime_reverseWith
  NativeWalk.computableInPolyTime_snocWith

private theorem poly_older : ComputableInPolyTime MeetingCode.older encMeetingCode
    (encList encExpansionCode) := EdgeForest.encMeetingCode_older_deg.computableInPolyTime
private theorem poly_current : ComputableInPolyTime MeetingCode.current encMeetingCode
    encExpansionCode := EdgeForest.encMeetingCode_current_deg.computableInPolyTime
private theorem poly_output : ComputableInPolyTime MeetingCode.output encMeetingCode encNat :=
  EdgeForest.encMeetingCode_output_deg.computableInPolyTime
attribute [local fun_prop] poly_older poly_current poly_output

/-- The original body is framed, followed by the complete binary-position meeting code. -/
abbrev encMeetingArgs := encPair (encCSP encTable encNat) encMeetingCode

/-- Candidate augmentation compilation is native polynomial-time on all raw meetings. -/
theorem computableInPolyTime_meetingWalk : ComputableInPolyTime
    (fun p : CSP Table ℕ × MeetingCode => meetingWalk p.1 p.2) encMeetingArgs encWalkCode := by
  unfold meetingWalk
  fun_prop

/-- Both timestamped LCA cases are native polynomial-time on every raw meeting. In particular,
copy times are not original constraint names and binary labels never fund a unary traversal. -/
theorem computableInPolyTime_blossom : ComputableInPolyTime
    (fun p : CSP Table ℕ × MeetingCode => blossom p.1 p.2)
    encMeetingArgs (encOption encBlossomCode) := by
  let left (p : CSP Table ℕ × MeetingCode) :=
    ancestry p.1 p.2.older (EdgeAugmenting.recordAt p.1 p.2.current.input).2.2
  let right (p : CSP Table ℕ × MeetingCode) :=
    ancestry p.1 p.2.older (EdgeAugmenting.recordAt p.1 p.2.output).2.2
  let shared (p : CSP Table ℕ × MeetingCode) := common p.1 (left p) (right p)
  let k (p : CSP Table ℕ × MeetingCode) := ((shared p).length - 1) / 2
  have hl : ComputableInPolyTime left encMeetingArgs encTraceCode := by dsimp only [left]; fun_prop
  have hr : ComputableInPolyTime right encMeetingArgs encTraceCode := by
    dsimp only [right]; fun_prop
  have hs : ComputableInPolyTime shared encMeetingArgs (encList encNodeCode) := by
    dsimp only [shared]; fun_prop
  have hk : ComputableInPolyTime k encMeetingArgs encUnary := by
    dsimp only [k]
    exact ComputableInPolyTime.unary_div_const 2 |>.comp (by fun_prop)
  have hh : ComputableInPolyTime (fun p => (shared p).reverse.head?) encMeetingArgs
      (encOption encNodeCode) := by fun_prop
  have hm := encBlossomCode_mk_deg.computableInPolyTime
  let lb (p : CSP Table ℕ × MeetingCode) (base : ℕ) : Option BlossomCode :=
    let a : WalkCode := ⟨base, (left p).steps.drop (k p)⟩
    let b : WalkCode := ⟨base, (right p).steps.drop (k p)⟩
    some ⟨NativeWalk.take (walk (left p)) (k p),
      append (NativeWalk.snoc a p.2.current.input p.2.output) (NativeWalk.reverse p.1 b)⟩
  let rb (p : CSP Table ℕ × MeetingCode) (_ : ℕ × ℕ) : Option BlossomCode :=
    ((left p).steps[k p]?).elim none fun pair =>
      ((right p).steps[k p]?).map fun other =>
        let a : WalkCode :=
          ⟨(EdgeAugmenting.recordAt p.1 pair.2).2.2, (left p).steps.drop (k p + 1)⟩
        let b : WalkCode :=
          ⟨(EdgeAugmenting.recordAt p.1 other.2).2.2, (right p).steps.drop (k p + 1)⟩
        ⟨NativeWalk.take (walk (left p)) (k p + 1),
          NativeWalk.snoc
            (append (NativeWalk.snoc a p.2.current.input p.2.output)
              (NativeWalk.reverse p.1 b)) other.2 pair.2⟩
  have hlb : ComputableInPolyTime (fun p : (CSP Table ℕ × MeetingCode) × ℕ => lb p.1 p.2)
      (encPair encMeetingArgs encNat) (encOption encBlossomCode) := by
    dsimp only [lb]
    fun_prop
  have hgetL : ComputableInPolyTime (fun p => (left p).steps[k p]?) encMeetingArgs
      (encOption (encPair encNat encNat)) := by
    exact .of_tidy (ComputableTidilyInPolyTime.getElem? (poly_steps.comp hl).tidy hk.tidy)
  have hgetR : ComputableInPolyTime (fun p => (right p).steps[k p]?) encMeetingArgs
      (encOption (encPair encNat encNat)) := by
    exact .of_tidy (ComputableTidilyInPolyTime.getElem? (poly_steps.comp hr).tidy hk.tidy)
  have hrb : ComputableInPolyTime (fun p : (CSP Table ℕ × MeetingCode) × (ℕ × ℕ) => rb p.1 p.2)
      (encPair encMeetingArgs (encPair encUnary encUnary)) (encOption encBlossomCode) := by
    dsimp only [rb]
    apply ComputableInPolyTime.optionElimWithInput
      (hgetL.comp (ComputableInPolyTime.fst encMeetingArgs (encPair encUnary encUnary)))
      (ComputableInPolyTime.const none)
    apply ComputableInPolyTime.optionMapWithInput
      (hgetR.comp ((ComputableInPolyTime.fst
        (encPair encMeetingArgs (encPair encUnary encUnary)) (encPair encNat encNat)).fst'))
    fun_prop
  have hcase := NativeCases.sumElimSnd (left := lb) (right := rb) none hlb hrb
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun p a => a.elim (lb p) (rb p)) hh (ComputableInPolyTime.const none) hcase
  apply h.of_enc_eq
  intro p
  dsimp only [blossom, left, right, shared, k]
  cases he : (common p.1
      (ancestry p.1 p.2.older (EdgeAugmenting.recordAt p.1 p.2.current.input).2.2)
      (ancestry p.1 p.2.older (EdgeAugmenting.recordAt p.1 p.2.output).2.2)).reverse.head? with
  | none => rfl
  | some a => cases a <;> rfl

end Cslib.Complexity.CSP.EdgeSolver.NativeForest
