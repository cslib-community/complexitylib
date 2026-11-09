/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Buffer
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Search
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Positional codes for chronological forest results

These codes represent the existing `CSP.Forest.Result`. Global occurrence indices reject when
out of range. Logs are newest first; timestamps are the number of older expansions, so there is
no independent timestamp to validate. No validity, edge-instance or reachability condition is
imposed by the representation bridge.
-/

public section

namespace Cslib.Complexity.CSP.EdgeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (occurrenceIndex)

/-- Complete native forest-search input. Labels follow actual constraint-then-port order. -/
structure Input where
  /-- Explicit relations and binary original variable names. -/
  body : CSP Table ℕ
  /-- Finite occurrence-label buffer. -/
  labels : List Bool

/-- The explicit-table CSP is framed, followed by a framed Boolean list. Arity and variable
names are binary; table rows and scopes are actual framed lists. -/
enc_structure encInput : Input where
  body : (encCSP encTable encNat), labels : (encList encBool)

/-- An expansion's input and ordered discovered output ports, as global positions. -/
structure ExpansionCode where
  /-- Global input position. -/
  input : ℕ
  /-- Ordered output positions. -/
  outputs : List ℕ
  deriving Repr

/-- Binary input position, framed, followed by a framed list of binary output positions. -/
enc_structure encExpansionCode : ExpansionCode where
  input : encNat, outputs : (encList encNat)

-- Ordinary clients reduce equality of output codes in checked executable examples.
@[expose] section
deriving instance DecidableEq for ExpansionCode
end

/-- A complete meeting, retaining original roots, older expansions and partial current copy. -/
structure MeetingCode where
  /-- Original root names in scan order. -/
  roots : List ℕ
  /-- Completed expansions, newest first. -/
  older : List ExpansionCode
  /-- The current copy before the meeting output. -/
  current : ExpansionCode
  /-- Global meeting-output position. -/
  output : ℕ
  deriving Repr

/-- Roots, older log and current expansion are framed in field order; the last position is
binary. Each list element is framed, including the nested expansion output lists. -/
enc_structure encMeetingCode : MeetingCode where
  roots : (encList encNat), older : (encList encExpansionCode),
  current : encExpansionCode, output : encNat

@[expose] section
deriving instance DecidableEq for MeetingCode
end

/-- Exhausted log, or augmentation meeting, or blossom meeting, in that order. -/
abbrev ResultCode := List ExpansionCode ⊕ (MeetingCode ⊕ MeetingCode)

/-- One sum tag for exhaustion versus event; an event has a second tag for augment versus
blossom. Expansion lists and meetings use their documented binary positional encodings. -/
abbrev encResultCode := encSum (encList encExpansionCode)
  (encSum encMeetingCode encMeetingCode)

/-- Encode an existing expansion by its actual incidence-list positions. -/
@[expose] def codeExpansion {F : CSP Table ℕ} (e : Forest.Expansion F) : ExpansionCode :=
  ⟨occurrenceIndex e.input, e.outputs.map occurrenceIndex⟩

/-- Encode every field of an existing meeting, preserving the partial current expansion. -/
@[expose] def codeMeeting {F : CSP Table ℕ} (m : Forest.Meeting F) : MeetingCode :=
  ⟨m.roots, m.older.map codeExpansion, codeExpansion m.current, occurrenceIndex m.output⟩

/-- Encode the existing result without making any mathematical assertion about its event. -/
@[expose] def code {F : CSP Table ℕ} : Forest.Result F → ResultCode
  | .exhausted es => .inl (es.map codeExpansion)
  | .augment m => .inr (.inl (codeMeeting m))
  | .blossom m => .inr (.inr (codeMeeting m))

/-- Decode an expansion, rejecting any invalid input or output position. -/
@[expose] def decodeExpansion (F : CSP Table ℕ) (e : ExpansionCode) :
    Option (Forest.Expansion F) := do
  let input ← (incidenceList F)[e.input]?
  let outputs ← e.outputs.mapM fun i => (incidenceList F)[i]?
  pure ⟨input, outputs⟩

/-- Decode all positional fields of a meeting. Roots remain binary original names. -/
@[expose] def decodeMeeting (F : CSP Table ℕ) (m : MeetingCode) :
    Option (Forest.Meeting F) := do
  let older ← m.older.mapM (decodeExpansion F)
  let current ← decodeExpansion F m.current
  let output ← (incidenceList F)[m.output]?
  pure ⟨m.roots, older, current, output⟩

/-- Decode to the existing dependent forest result, rejecting malformed indices in every tag. -/
@[expose] def decode (F : CSP Table ℕ) : ResultCode → Option (Forest.Result F)
  | .inl es => (es.mapM (decodeExpansion F)).map Forest.Result.exhausted
  | .inr (.inl m) => (decodeMeeting F m).map Forest.Result.augment
  | .inr (.inr m) => (decodeMeeting F m).map Forest.Result.blossom

/-- Expansion codes are lossless even for externally supplied malformed forest histories. -/
@[simp] theorem decodeExpansion_codeExpansion {F : CSP Table ℕ} (e : Forest.Expansion F) :
    decodeExpansion F (codeExpansion e) = some e := by
  rcases e with ⟨input, outputs⟩
  have hm : outputs.mapM (fun a => some a) = some outputs := by
    simpa only [List.map_id, Option.pure_def, id_eq] using
      (List.mapM_pure (m := Option) (l := outputs) (f := id))
  simp [decodeExpansion, codeExpansion, List.mapM_map, Function.comp_def,
    EdgeAugmenting.getElem?_occurrenceIndex, hm]

/-- Meeting codes retain the full log, roots and partial copy. -/
@[simp] theorem decodeMeeting_codeMeeting {F : CSP Table ℕ} (m : Forest.Meeting F) :
    decodeMeeting F (codeMeeting m) = some m := by
  rcases m with ⟨roots, older, current, output⟩
  have hm : older.mapM (fun a => some a) = some older := by
    simpa only [List.map_id, Option.pure_def, id_eq] using
      (List.mapM_pure (m := Option) (l := older) (f := id))
  simp [decodeMeeting, codeMeeting, List.mapM_map, Function.comp_def,
    EdgeAugmenting.getElem?_occurrenceIndex, hm]

/-- The complete result bridge is lossless, with no semantic or forest invariant premise. -/
@[simp] theorem decode_code {F : CSP Table ℕ} (r : Forest.Result F) :
    decode F (code r) = some r := by
  cases r with
  | exhausted es =>
    have hm : es.mapM (fun a => some a) = some es := by
      simpa only [List.map_id, Option.pure_def, id_eq] using
        (List.mapM_pure (m := Option) (l := es) (f := id))
    simp [decode, code, List.mapM_map, Function.comp_def, hm]
  | augment m => simp [decode, code]
  | blossom m => simp [decode, code]

end Cslib.Complexity.CSP.EdgeForest
