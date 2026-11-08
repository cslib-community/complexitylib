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
  (((CSP.occurrences input.body).filter fun o =>
    EdgeAugmenting.inconsistent input.body input.labels o.2.2).map (·.2.2)).eraseDups

/-- Used positional records in the source log's order. -/
@[expose] def used (es : WorkLog) : List Record := es.flatMap fun e => e.1 :: e.2

/-- Discovered variables in the source log's order. -/
@[expose] def children (es : WorkLog) : List ℕ :=
  es.flatMap fun e => e.2.map (·.2.2)

/-- Root/discovery membership, including children already inserted at the current copy. -/
@[expose] def visited (rs : List ℕ) (es : WorkLog) (v : ℕ) : Bool :=
  decide (v ∈ rs ∨ v ∈ children es)

/-- First actual parent output's original constraint position; timestamps are irrelevant here. -/
@[expose] def parentConstraint (es : WorkLog) (v : ℕ) : Option ℕ :=
  ((es.flatMap Prod.snd).find? fun o => o.2.2 == v).map Prod.fst

/-- Follow parents through older records, computing just the root of the actual ancestry walk. -/
@[expose] def root (es : WorkLog) (v : ℕ) : ℕ :=
  es.foldl (fun current e => if (e.2.find? (fun o => o.2.2 == current)).isSome
    then e.1.2.2 else current) v

/-- Feasible same-constraint, distinct-variable partners in actual incidence order. The validity
check is global, including on invalid inputs and malformed explicit relation tables. -/
@[expose] def partners (input : Input) (a : Record) : List Record :=
  (CSP.occurrences input.body).filter fun b =>
    decide (a.1 = b.1) && decide (a.2.2 ≠ b.2.2) &&
      EdgeAugmenting.valid input.body
        (EdgeAugmenting.flip input.labels
          [(CSP.occurrences input.body).idxOf a, (CSP.occurrences input.body).idxOf b])

/-- One scan step. A meeting freezes both ordered children and the first meeting output. -/
@[expose] def scanStep (rs : List ℕ) (es : WorkLog) (a : Record)
    (s : ScanState) (b : Record) : ScanState :=
  if s.2.isSome then s else
    let current := (a, s.1) :: es
    if !visited rs current b.2.2 then (s.1 ++ [b], none)
    else if parentConstraint current b.2.2 = some a.1 then s
    else (s.1, some b)

/-- Scan actual partners using a finite left fold. -/
@[expose] def scan (rs : List ℕ) (es : WorkLog) (a : Record)
    (outputs bs : List Record) : ScanState :=
  bs.foldl (scanStep rs es a) (outputs, none)

/-- One outer step. Noncanonical external states whose chosen port is not an actual occurrence
stop immediately; this guard gives uniform growth on every state, without scanning its index. -/
@[expose] def step (input : Input) (s : State) : State :=
  if s.2.2.isSome then s else
    ((s.2.1.find? fun a => visited (roots input) s.1 a.2.2)).elim
      (s.1, s.2.1, some none) fun a =>
        if a ∈ CSP.occurrences input.body then
          let out := scan (roots input) s.1 a [] (partners input a)
          out.2.elim
            (let next := (a, out.1) :: s.1
             (next, s.2.1.filter (fun b => decide (b ∉ used next)), none))
            (fun b => (s.1, s.2.1, some (some (a, out.1, b))))
        else (s.1, s.2.1, some none)

/-- Convert a work expansion's positional records into binary global occurrence positions. -/
@[expose] def finishExpansion (F : CSP Table ℕ) (e : WorkExpansion) : ExpansionCode :=
  ⟨(CSP.occurrences F).idxOf e.1, e.2.map (CSP.occurrences F).idxOf⟩

/-- Finalize once, after the loop. Classification uses roots of the actual older ancestries. -/
@[expose] def finish (input : Input) (s : State) : Option ResultCode :=
  s.2.2.elim none fun event =>
    event.elim (some (.inl (s.1.map (finishExpansion input.body)))) fun (a, os, b) =>
      let m : MeetingCode := ⟨roots input, s.1.map (finishExpansion input.body),
        finishExpansion input.body (a, os), (CSP.occurrences input.body).idxOf b⟩
      some (if root s.1 a.2.2 = root s.1 b.2.2 then .inr (.inr m) else .inr (.inl m))

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
