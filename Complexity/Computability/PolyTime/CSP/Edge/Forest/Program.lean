/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Forest.Code
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Finite chronological forest-search program

The work representation uses the existing positional occurrence records: unary constraint and
port positions, binary original names. Only final result positions are converted to binary
global indices. Every loop traverses an actual list or its length. The stopped event occupies a
separate small field: the completed log stays in the same encoding throughout the iteration.
-/

public section

namespace Cslib.Complexity.CSP.EdgeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (Record encRecord)

/-- One work expansion: its positional input record and ordered positional output records. -/
abbrev WorkExpansion := Record × List Record

/-- A unary-position input record is framed; its framed output list follows. Names stay binary. -/
abbrev encWorkExpansion := encPair encRecord (encList encRecord)

/-- Completed work expansions, newest first. -/
abbrev WorkLog := List WorkExpansion

/-- A framed list of the documented work expansions. -/
abbrev encWorkLog := encList encWorkExpansion

/-- Work scan state: ordered children and the optional first meeting port. -/
abbrev ScanState := List Record × Option Record

/-- The child list is framed, followed by an option tag and a positional meeting record. -/
abbrev encScanState := encPair (encList encRecord) (encOption encRecord)

/-- Small terminal data: current input, current children, and meeting output. -/
abbrev Event := Record × List Record × Record

/-- Input and children are framed in order, followed by the meeting record. -/
abbrev encEvent := encPair encRecord (encPair (encList encRecord) encRecord)

/-- Log and remaining ports, followed by running / exhausted / meeting status. -/
abbrev State := WorkLog × List Record × Option (Option Event)

/-- Log and remaining list stay in fixed framed fields. The two option tags distinguish running,
exhausted and meeting; event data never duplicate or reframe the completed log. -/
abbrev encState := encPair encWorkLog
  (encPair (encList encRecord) (encOption (encOption encEvent)))

/-- Original roots, retaining first positional occurrence order. -/
@[expose] def roots (input : Input) : List ℕ :=
  (((CSP.occurrences input.body).filter fun (_, _, vertex) =>
    EdgeAugmenting.inconsistent input.body input.labels vertex).map
      fun (_, _, vertex) => vertex).eraseDups

/-- Used positional records in the source log's order. -/
@[expose] def used (es : WorkLog) : List Record := es.flatMap fun e => e.1 :: e.2

/-- Discovered variables in the source log's order. -/
@[expose] def children (es : WorkLog) : List ℕ :=
  es.flatMap fun (_, outputs) => outputs.map fun (_, _, vertex) => vertex

/-- Root/discovery membership, including children already inserted at the current copy. -/
@[expose] def visited (rs : List ℕ) (es : WorkLog) (v : ℕ) : Bool :=
  decide (v ∈ rs ∨ v ∈ children es)

/-- First actual parent output's original constraint position; timestamps are irrelevant here. -/
@[expose] def parentConstraint (es : WorkLog) (v : ℕ) : Option ℕ :=
  ((es.flatMap Prod.snd).find? fun (_, _, vertex) => vertex == v).map Prod.fst

/-- Follow parents through older records, computing just the root of the actual ancestry walk. -/
@[expose] def root (es : WorkLog) (v : ℕ) : ℕ :=
  es.foldl (fun current ((_, _, parentVariable), outputs) =>
    if (outputs.find? (fun (_, _, vertex) => vertex == current)).isSome
      then parentVariable else current) v

/-- Feasible same-constraint, distinct-variable partners in actual incidence order. The validity
check is global, including on invalid inputs and malformed explicit relation tables. -/
@[expose] def partners (input : Input) (a : Record) : List Record :=
  let (constraint, _, vertex) := a
  (CSP.occurrences input.body).filter fun b =>
    let (otherConstraint, _, otherVariable) := b
    decide (constraint = otherConstraint) && decide (vertex ≠ otherVariable) &&
      EdgeAugmenting.valid input.body (EdgeAugmenting.flip input.labels
        [(CSP.occurrences input.body).idxOf a, (CSP.occurrences input.body).idxOf b])

/-- One scan step. A meeting freezes both ordered children and the first meeting output. -/
@[expose] def scanStep (rs : List ℕ) (es : WorkLog) (a : Record)
    (s : ScanState) (b : Record) : ScanState :=
  let (outputs, meeting) := s
  let (constraint, _, _) := a
  let (_, _, vertex) := b
  if meeting.isSome then s else
    let current := (a, outputs) :: es
    if !visited rs current vertex then (outputs ++ [b], none)
    else if parentConstraint current vertex = some constraint then s
    else (outputs, some b)

/-- Scan actual partners using a finite left fold. -/
@[expose] def scan (rs : List ℕ) (es : WorkLog) (a : Record)
    (outputs bs : List Record) : ScanState :=
  bs.foldl (scanStep rs es a) (outputs, none)

/-- One outer step. Noncanonical external states whose chosen port is not an actual occurrence
stop immediately; this guard gives uniform growth on every state, without scanning its index. -/
@[expose] def step (input : Input) (s : State) : State :=
  let (log, remaining, event) := s
  if event.isSome then s else
    ((remaining.find? fun (_, _, vertex) => visited (roots input) log vertex)).elim
      (log, remaining, some none) fun a =>
        if a ∈ CSP.occurrences input.body then
          let (outputs, meeting) := scan (roots input) log a [] (partners input a)
          meeting.elim
            (let next := (a, outputs) :: log
             (next, remaining.filter (fun b => decide (b ∉ used next)), none))
            (fun b => (log, remaining, some (some (a, outputs, b))))
        else (log, remaining, some none)

/-- Convert a work expansion's positional records into binary global occurrence positions. -/
@[expose] def finishExpansion (F : CSP Table ℕ) (e : WorkExpansion) : ExpansionCode :=
  let (input, outputs) := e
  ⟨(CSP.occurrences F).idxOf input, outputs.map (CSP.occurrences F).idxOf⟩

/-- Finalize once, after the loop. Classification uses roots of the actual older ancestries. -/
@[expose] def finish (input : Input) (s : State) : Option ResultCode :=
  let (log, _, status) := s
  status.elim none fun event =>
    event.elim (some (.inl (log.map (finishExpansion input.body)))) fun (a, outputs, b) =>
      let (_, _, leftVariable) := a
      let (_, _, rightVariable) := b
      let m : MeetingCode := ⟨roots input, log.map (finishExpansion input.body),
        finishExpansion input.body (a, outputs), (CSP.occurrences input.body).idxOf b⟩
      some (if root log leftVariable = root log rightVariable
        then .inr (.inr m) else .inr (.inl m))

/-- Total native forest search. Exactly the actual occurrence width is accepted. The outer
clock is one more than the actual occurrence count, so the final exhaustion check is paid for. -/
@[expose] def run (input : Input) : Option ResultCode :=
  if input.labels.length = (CSP.occurrences input.body).length then
    finish input ((step input)^[(CSP.occurrences input.body).length + 1]
      ([], CSP.occurrences input.body, none))
  else none

/-- Reject either short or long occurrence buffers. -/
theorem run_eq_none_of_length (input : Input)
    (h : input.labels.length ≠ (incidenceList input.body).length) : run input = none := by
  simp [run, occurrences_eq_map_incidenceList, h]

end Cslib.Complexity.CSP.EdgeForest
