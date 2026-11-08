/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Walk
public import Complexity.Algorithms.Lean.EdgeCSP.Forest.BlossomData
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Finite chronological ancestry and blossom compilation

A single backwards scan reconstructs actual root paths. Timestamps are paid for by the older
log's length and retain copied-constraint identity. Original names and public occurrence
positions remain binary. The representation bookkeeping is original; the two LCA cases are
those of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, Section 5.3, printed pp. 11–12.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode encWalkCode)
open EdgeForest (ExpansionCode encExpansionCode MeetingCode encMeetingCode)

/-- Backwards-scan state: queried binary variable and the already reconstructed suffix. -/
structure TraceCode where
  /-- Current ancestor's binary original name. -/
  start : ℕ
  /-- Actual binary global port pairs in root-to-leaf order. -/
  steps : List (ℕ × ℕ)
  /-- Actual copy timestamps, in the same order and encoded unary. -/
  times : List ℕ

/-- Framed binary start and framed binary position pairs, followed by framed unary times. -/
enc_structure encTraceCode : TraceCode where
  start : encNat, steps : (encList (encPair encNat encNat)), times : (encList encUnary)

/-- Follow one actual parent through a strictly older expansion. -/
@[expose] def traceStep (F : CSP Table ℕ) (s : TraceCode) (e : ExpansionCode × ℕ) : TraceCode :=
  let (expansion, time) := e
  (expansion.outputs.find? fun o =>
    let (_constraint, _argument, variableName) := EdgeAugmenting.recordAt F o
    variableName == s.start).elim s fun output =>
    let (_constraint, _argument, parent) := EdgeAugmenting.recordAt F expansion.input
    ⟨parent, (expansion.input, output) :: s.steps, time :: s.times⟩

/-- Scan newest-first expansions with the actual decreasing copy timestamps. -/
@[expose] def trace (F : CSP Table ℕ) (es : List ExpansionCode) (s : TraceCode) : TraceCode :=
  (es.zip (List.range es.length).reverse).foldl (traceStep F) s

/-- Root-to-variable ancestry with exact ordered step positions and actual copy times. -/
@[expose] def ancestry (F : CSP Table ℕ) (es : List ExpansionCode) (v : ℕ) : TraceCode :=
  trace F es ⟨v, [], []⟩

/-- Forget only the copy timestamps of an actual ancestry code. -/
@[expose] def walk (p : TraceCode) : WalkCode := ⟨p.start, p.steps⟩

/-- Actual variable/copy node codes; copied nodes keep original constraint and time. -/
abbrev NodeCode := ℕ ⊕ (ℕ × ℕ)

/-- A variable/copy tag precedes binary original names or unary constraint/time coordinates. -/
abbrev encNodeCode := encSum encNat (encPair encUnary encUnary)

/-- Original variables alternate with actual timestamped copied constraints. -/
@[expose] def nodes (F : CSP Table ℕ) (p : TraceCode) : List NodeCode :=
  .inl p.start :: (p.steps.zip p.times).flatMap fun ((a, b), t) =>
    let (constraint, _inputArgument, _inputVariable) := EdgeAugmenting.recordAt F a
    let (_outputConstraint, _outputArgument, variableName) := EdgeAugmenting.recordAt F b
    [.inr (constraint, t), .inl variableName]

/-- The full common root-path prefix, retaining both coordinates of a copied constraint. -/
@[expose] def common (F : CSP Table ℕ) (left right : TraceCode) : List NodeCode :=
  ((nodes F left).zip (nodes F right)).takeWhile (fun (a, b) => a == b) |>.map Prod.fst

/-- The preparatory root path and actual closed cycle; metadata remain in the source layer. -/
structure BlossomCode where
  /-- Root-to-base path whose flip prepares the blossom. -/
  prepare : WalkCode
  /-- Actual cycle in original global port order. -/
  cycle : WalkCode

/-- The preparation walk is framed, followed by the cycle walk. -/
enc_structure encBlossomCode : BlossomCode where
  prepare : encWalkCode, cycle : encWalkCode

/-- Append two actual walks, preserving the first one's original start. -/
@[expose] def append (p q : WalkCode) : WalkCode := ⟨p.start, p.steps ++ q.steps⟩

/-- Candidate augmentation: the left ancestry, meeting pair, and reversed right ancestry. -/
@[expose] def meetingWalk (F : CSP Table ℕ) (m : MeetingCode) : WalkCode :=
  let (_inputConstraint, _inputArgument, inputVariable) := EdgeAugmenting.recordAt F m.current.input
  let (_outputConstraint, _outputArgument, outputVariable) := EdgeAugmenting.recordAt F m.output
  let left := walk (ancestry F m.older inputVariable)
  let right := walk (ancestry F m.older outputVariable)
  append (NativeWalk.snoc left m.current.input m.output) (NativeWalk.reverse F right)

/-- Both actual LCA cases, including the final child-to-child pair for a copied-constraint LCA.
Every scope lookup and prefix length is bounded by an actual list. -/
@[expose] def blossom (F : CSP Table ℕ) (m : MeetingCode) : Option BlossomCode :=
  let (_inputConstraint, _inputArgument, inputVariable) := EdgeAugmenting.recordAt F m.current.input
  let (_outputConstraint, _outputArgument, outputVariable) := EdgeAugmenting.recordAt F m.output
  let left := ancestry F m.older inputVariable
  let right := ancestry F m.older outputVariable
  let shared := common F left right
  let k := (shared.length - 1) / 2
  shared.reverse.head?.elim none fun ancestor =>
    match ancestor with
    | .inl base =>
      let a : WalkCode := ⟨base, left.steps.drop k⟩
      let b : WalkCode := ⟨base, right.steps.drop k⟩
      some ⟨NativeWalk.take (walk left) k,
        append (NativeWalk.snoc a m.current.input m.output) (NativeWalk.reverse F b)⟩
    | .inr _ =>
      (left.steps[k]?).elim none fun (_, lport) =>
        (right.steps[k]?).map fun (_, rport) =>
          let (_leftConstraint, _leftArgument, leftVariable) := EdgeAugmenting.recordAt F lport
          let (_rightConstraint, _rightArgument, rightVariable) := EdgeAugmenting.recordAt F rport
          let a : WalkCode := ⟨leftVariable, left.steps.drop (k + 1)⟩
          let b : WalkCode := ⟨rightVariable, right.steps.drop (k + 1)⟩
          ⟨NativeWalk.take (walk left) (k + 1),
            NativeWalk.snoc
              (append (NativeWalk.snoc a m.current.input m.output) (NativeWalk.reverse F b))
              rport lport⟩

private theorem trace_cons (F : CSP Table ℕ) (e : ExpansionCode)
    (es : List ExpansionCode) (s : TraceCode) :
    trace F (e :: es) s = trace F es (traceStep F s (e, es.length)) := by
  simp [trace, List.range_succ, List.reverse_append]

private theorem find_output_code {F : CSP Table ℕ} (e : Forest.Expansion F) (v : ℕ) :
    ((EdgeForest.codeExpansion e).outputs.find?
      (fun o => (EdgeAugmenting.recordAt F o).2.2 == v)) =
      (e.outputs.find? fun o => o.var == v).map EdgeAugmenting.occurrenceIndex := by
  simp [EdgeForest.codeExpansion, List.find?_map,
    EdgeAugmenting.recordAt_index, Occurrence.record]

private theorem trace_code {F : CSP Table ℕ} (es : Forest.Log F) (s : TraceCode) :
    trace F (es.map EdgeForest.codeExpansion) s =
      let p := es.ancestry s.start
      ⟨p.walk.start, (EdgeAugmenting.code p.walk).steps ++ s.steps, p.times ++ s.times⟩ := by
  induction es generalizing s with
  | nil => simp [trace, Forest.Log.ancestry, EdgeAugmenting.code]
  | cons e es ih =>
    rw [List.map_cons, trace_cons]
    simp only [traceStep, find_output_code, List.length_map]
    cases he : e.outputs.find? (fun o => o.var == s.start) with
    | none => simpa only [Option.map_none, Option.elim_none, Forest.Log.ancestry, he] using ih s
    | some o =>
      simp only [Option.map_some, Option.elim_some, EdgeForest.codeExpansion,
        EdgeAugmenting.recordAt_index, Occurrence.record]
      rw [ih]
      simp [Forest.Log.ancestry, he, EdgeAugmenting.code, Walk.snoc, List.map_append,
        List.append_assoc]

/-- A single native backwards scan has exactly the source's chronological ancestry.
No forest invariant, validity, width or edge-instance premise is needed for this bridge. -/
theorem ancestry_code {F : CSP Table ℕ} (es : Forest.Log F) (v : ℕ) :
    ancestry F (es.map EdgeForest.codeExpansion) v =
      ⟨(es.ancestry v).walk.start, (EdgeAugmenting.code (es.ancestry v).walk).steps,
        (es.ancestry v).times⟩ := by
  simpa only [ancestry, List.append_nil] using trace_code es ⟨v, [], []⟩

private def nodeCode {F : CSP Table ℕ} : DAG.Node F → NodeCode
  | .inl v => .inl v
  | .inr (c, t) => .inr (c.val, t)

private theorem nodeCode_injective {F : CSP Table ℕ} :
    Function.Injective (nodeCode (F := F)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [nodeCode, Prod.ext_iff, Fin.ext_iff]

private theorem nodes_code {F : CSP Table ℕ} (p : Forest.Ancestry F) :
    nodes F ⟨p.walk.start, (EdgeAugmenting.code p.walk).steps, p.times⟩ =
      p.nodes.map nodeCode := by
  simp [nodes, Forest.Ancestry.nodes, EdgeAugmenting.code, List.zip_map_left,
    List.flatMap_map, List.map_flatMap, nodeCode,
    EdgeAugmenting.recordAt_index, Occurrence.record]

private theorem common_code {F : CSP Table ℕ} (m : Forest.Meeting F) :
    common F
      ⟨m.left.walk.start, (EdgeAugmenting.code m.left.walk).steps, m.left.times⟩
      ⟨m.right.walk.start, (EdgeAugmenting.code m.right.walk).steps, m.right.times⟩ =
      m.commonNodes.map nodeCode := by
  simp only [common, nodes_code, List.zip_map, List.takeWhile_map, List.map_map]
  have he : (fun p : DAG.Node F × DAG.Node F => nodeCode p.1 == nodeCode p.2) =
      (fun p => p.1 == p.2) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, nodeCode_injective.eq_iff]
  simp only [Prod.map_fst, Prod.map_snd, he, Forest.Meeting.commonNodes,
    List.map_map, Function.comp_def]

/-- The native ancestry compiler constructs the exact original augmenting walk. -/
theorem meetingWalk_code {F : CSP Table ℕ} (m : Forest.Meeting F) :
    meetingWalk F (EdgeForest.codeMeeting m) = EdgeAugmenting.code m.walk := by
  simp [meetingWalk, EdgeForest.codeMeeting, EdgeForest.codeExpansion,
    EdgeAugmenting.recordAt_index, Occurrence.record, ancestry_code, walk,
    NativeWalk.snoc, append, NativeWalk.reverse, Walk.reverse, List.map_reverse,
    List.map_map, Function.comp_def, Forest.Meeting.walk,
    Forest.Meeting.left, Forest.Meeting.right, EdgeAugmenting.code, Walk.snoc, Walk.append]

/-- The native compiler retains the exact preparation and cycle of both source LCA cases.
The metadata and mathematical invariant remain the existing `Meeting.blossomData` API. -/
theorem blossom_code {F : CSP Table ℕ} (m : Forest.Meeting F) :
    blossom F (EdgeForest.codeMeeting m) =
      m.blossomData.map (fun b => BlossomCode.mk
        (EdgeAugmenting.code b.prepare) (EdgeAugmenting.code b.cycle)) := by
  simp only [blossom, EdgeForest.codeMeeting, EdgeForest.codeExpansion,
    EdgeAugmenting.recordAt_index, Occurrence.record, ancestry_code]
  have hcommon := common_code m
  simp only [Forest.Meeting.left, Forest.Meeting.right] at hcommon
  rw [hcommon]
  simp only [List.head?_reverse, List.length_map, List.getLast?_map]
  cases ha : m.ancestor? with
  | none =>
    have hn : m.commonNodes.getLast? = none := ha
    simp [Forest.Meeting.blossomData, Forest.Meeting.ancestor?, hn]
  | some ancestor =>
    have hlast : m.commonNodes.getLast? = some ancestor := ha
    simp only [hlast, Option.map_some, Option.elim_some]
    cases ancestor with
    | inl base =>
      simp [Forest.Meeting.blossomData, ha, nodeCode, walk, append, NativeWalk.take,
        NativeWalk.snoc, NativeWalk.reverse, EdgeAugmenting.code,
        Walk.take, Walk.snoc, Walk.append, Walk.reverse, List.map_drop, List.map_reverse,
        List.map_map, Function.comp_def, Forest.Meeting.left, Forest.Meeting.right]
    | inr copy =>
      cases hl : m.left.walk.steps[(m.commonNodes.length - 1) / 2]? <;>
        cases hr : m.right.walk.steps[(m.commonNodes.length - 1) / 2]? <;>
        simp only [Forest.Meeting.left, Forest.Meeting.right] at hl hr <;>
        simp [Forest.Meeting.blossomData, ha, nodeCode, walk, append, NativeWalk.take,
          NativeWalk.snoc, NativeWalk.reverse, EdgeAugmenting.code,
          Walk.take, Walk.snoc, Walk.append, Walk.reverse, List.map_drop, List.map_reverse,
          List.map_map, Function.comp_def, EdgeAugmenting.recordAt_index, Occurrence.record,
          Forest.Meeting.left, Forest.Meeting.right, hl, hr]

end Cslib.Complexity.CSP.EdgeSolver.NativeForest
