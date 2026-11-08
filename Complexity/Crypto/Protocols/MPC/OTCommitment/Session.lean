/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.SenderProgram

/-!
# Single-session OT commitment commands

The total command processor shared by complete-sender execution and the serial role-local world.
It stores submitted tables and the first opening attempt without receiver choices or answers.

## Main definitions

* `SenderOperation`: finite sender commands with a separate opening word.
* `openingWord`: the shared command wire format for an honest opening.
* `Session.advance`: total command processing with immutable terminal attempts.
* `Session.opening`, `Session.receipt`, `Session.observation`: parsing and observations.
* `Session.extracted`, `Session.idealStore`: majority extraction and its ideal state representation.

## Main results

* `decodeOpening_openingWord`: exact round-trip through both opening parsers.
* `Session.advance_stopped`: a terminal session is immutable.
* `Session.advance_tables_of_sealed`: sealing freezes the submitted tables.
* `Session.advance_length`: the table budget and exact-seal invariant are enforced.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Crypto.Protocols.Commitment

/-- Finite command names. Only an opening uses its accompanying word payload. -/
inductive SenderOperation where
  | table (values : Fin 4 → Bool)
  | seal
  | open (bit : Bool)
  | abort
  deriving DecidableEq, Fintype

/-- Sender-visible command history summarized without any receiver choice or answer.
The fields are internal execution state, not replies to the sender. -/
structure Session where
  /-- Tables in execution order, frozen once the session seals or stops. -/
  tables : List (Fin 4 → Bool) := []
  /-- Whether a successful seal has occurred. -/
  sealed : Bool := false
  /-- Whether an abort or the first post-seal opening attempt has occurred. -/
  stopped : Bool := false
  /-- The first opening attempt, if any. Invalid lengths are retained and rejected later. -/
  submission : Option (Bool × List Bool) := none
  deriving DecidableEq

/-- Initial single-session state. -/
def Session.initial : Session := {}

/-- Total command processing. Stopping is independent of opening verification, so a rejected
attempt cannot be followed by another try. -/
def Session.advance (k : ℕ) (request : SenderOperation × List Bool) (s : Session) : Session :=
  if s.stopped then s else
  match request.1 with
  | .table values =>
      if s.sealed then s else
      if s.tables.length < k then { s with tables := s.tables ++ [values] }
      else { s with stopped := true, submission := none }
  | .seal =>
      if s.sealed then s else
      if s.tables.length = k then { s with sealed := true }
      else { s with stopped := true, submission := none }
  | .open bit =>
      if s.sealed then { s with stopped := true, submission := some (bit, request.2) } else s
  | .abort => { s with stopped := true, submission := none }

/-- Once stopped, every command leaves the complete session unchanged. -/
theorem Session.advance_stopped (k : ℕ) (request : SenderOperation × List Bool)
    (s : Session) (h : s.stopped = true) : s.advance k request = s := by
  simp [advance, h]

/-- The committed tables are immutable, even after malformed opening attempts. -/
theorem Session.advance_tables_of_sealed (k : ℕ) (request : SenderOperation × List Bool)
    (s : Session) (h : s.sealed = true) : (s.advance k request).tables = s.tables := by
  rcases request with ⟨op, word⟩
  cases op <;> simp only [advance, h, ite_true]
  all_goals split <;> rfl

/-- The handler enforces its table budget and seals only an exact-length transcript. -/
theorem Session.advance_length (k : ℕ) (request : SenderOperation × List Bool) (s : Session)
    (h : s.tables.length ≤ k ∧ (s.sealed = true → s.tables.length = k)) :
    (s.advance k request).tables.length ≤ k ∧
      ((s.advance k request).sealed = true → (s.advance k request).tables.length = k) := by
  rcases request with ⟨op, word⟩
  cases hs : s.stopped <;> cases hc : s.sealed <;> cases op <;>
    simp only [advance, hs, hc, Bool.false_eq_true, ite_false, ite_true]
  all_goals first | simpa [hc] using h | (split <;> simp_all [List.length_append])

/-- Opening payloads have two exact-length halves. There is no zip-truncation acceptance. -/
def Session.opening (k : ℕ) (s : Session) : Option (Bool × List (Bool × Bool)) := do
  let (bit, word) ← s.submission
  if word.length = 2 * k then some (bit, (word.take k).zip (word.drop k)) else none

/-- The command wire format lists all first components, followed by all second components. -/
def openingWord {k : ℕ} (o : Opening k) : List Bool :=
  List.ofFn (fun i => o i false) ++ List.ofFn (fun i => o i true)

/-- A correctly encoded opening survives both exact-length parsers, including at zero rounds. -/
theorem decodeOpening_openingWord {k : ℕ} (b : Bool) (o : Opening k) :
    decodeOpening k (({ submission := some (b, openingWord o) } : Session).opening k) =
      some (b, o) := by
  have ht : (openingWord o).take k = List.ofFn (fun i => o i false) :=
    List.take_left' List.length_ofFn
  have hd : (openingWord o).drop k = List.ofFn (fun i => o i true) :=
    List.drop_left' List.length_ofFn
  simp only [Session.opening, Option.bind_eq_bind, Option.bind_some, openingWord,
    List.length_append,
    List.length_ofFn, show k + k = 2 * k by omega, ite_true]
  rw [show (List.ofFn (fun i => o i false) ++ List.ofFn (fun i => o i true)).take k = _ from ht,
    show (List.ofFn (fun i => o i false) ++ List.ofFn (fun i => o i true)).drop k = _ from hd]
  simp only [decodeOpening, Option.bind_some, List.length_zip, List.length_ofFn,
    Nat.min_self, ite_true]
  congr 2 with i c : 2
  cases c <;> simp [List.getD_eq_getElem?_getD]

/-- The receiver records whether a receipt was actually issued; pre-seal abort has no receipt. -/
def Session.receipt (s : Session) : Phased.Observation :=
  if s.sealed then .receipt else .idle

/-- The extractor sees the corrupted sender's actual OT tables. -/
def Session.extracted (s : Session) : Bool :=
  extractPairs (s.tables.map fun t =>
    (t (boolPairToFin4 (false, false)), t (boolPairToFin4 (false, true))))

/-- Final receiver observation, computed from the answers actually delivered by OT. -/
def Session.observation (k : ℕ) (choices received : List Bool) (s : Session) :
    Phased.Observation :=
  if s.stopped then
    if s.sealed then (openPairs choices received (s.opening k)).elim .aborted .opened
    else .aborted
  else s.receipt

/-- Ideal functionality state represented by the same phase history. The stored bit is fixed
at the successful seal; later tables cannot change it. -/
def Session.idealStore (k : ℕ) (choices received : List Bool) (s : Session) : Phased.Store :=
  if s.stopped then
    if s.sealed && (openPairs choices received (s.opening k) == some s.extracted)
    then .opened s.extracted else .aborted
  else if s.sealed then .committed s.extracted else .idle

end Cslib.Crypto.Protocols.MPC.OTCommitment
