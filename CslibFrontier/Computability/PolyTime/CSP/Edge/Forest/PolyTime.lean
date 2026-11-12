/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Forest.Program
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Native polynomial-time chronological forest search

Certificates use ordinary `ComputableInPolyTime`, realized by the library's native multitape
machines. Work positions are unary, original names binary, and output global positions binary.
The bounds charge actual encoded records and all list/option framing.
-/

public section

namespace Cslib.Complexity.CSP.EdgeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (Record encRecord)

attribute [local fun_prop] EdgeAugmenting.poly_records
  EdgeAugmenting.poly_idxOf EdgeAugmenting.poly_flip EdgeAugmenting.poly_validWith
  EdgeAugmenting.poly_inconsistentWith EdgeAugmenting.poly_zipIdx

private theorem poly_eraseDups :
    ComputableInPolyTime (List.eraseDups (α := ℕ)) (encList encNat) (encList encNat) := by
  change ComputableInPolyTime
    (fun xs : List ℕ => xs.eraseDupsBy (fun a b => a == b)) (encList encNat) (encList encNat)
  exact ComputableInPolyTime.eraseDupsByWithInput
    (ComputableInPolyTime.id' (encIn := encList encNat)) (by fun_prop)

attribute [local fun_prop] poly_eraseDups

private theorem poly_roots : ComputableInPolyTime roots encInput (encList encNat) := by
  unfold roots
  fun_prop

private theorem poly_used : ComputableInPolyTime used encWorkLog (encList encRecord) := by
  unfold used
  fun_prop

private theorem poly_children : ComputableInPolyTime children encWorkLog (encList encNat) := by
  unfold children
  fun_prop

attribute [local fun_prop] poly_roots poly_used poly_children

/-- Root list and work log are framed, followed by the binary queried name. -/
private abbrev encVisit := encPair (encList encNat) (encPair encWorkLog encNat)

private theorem poly_visited : ComputableInPolyTime
    (fun p : List ℕ × WorkLog × ℕ => visited p.1 p.2.1 p.2.2) encVisit encBool := by
  unfold visited
  fun_prop

private theorem poly_visitedWith {α : Type} {e : α ↪ List Bool}
    {rs : α → List ℕ} {es : α → WorkLog} {v : α → ℕ}
    (hr : ComputableInPolyTime rs e (encList encNat))
    (he : ComputableInPolyTime es e encWorkLog)
    (hv : ComputableInPolyTime v e encNat) :
    ComputableInPolyTime (fun x => visited (rs x) (es x) (v x)) e encBool :=
  poly_visited.comp (hr.prod (he.prod hv))

private theorem poly_parentConstraint : ComputableInPolyTime
    (fun p : WorkLog × ℕ => parentConstraint p.1 p.2)
    (encPair encWorkLog encNat) (encOption encUnary) := by
  unfold parentConstraint
  fun_prop

private theorem poly_parentWith {α : Type} {e : α ↪ List Bool}
    {es : α → WorkLog} {v : α → ℕ}
    (he : ComputableInPolyTime es e encWorkLog)
    (hv : ComputableInPolyTime v e encNat) :
    ComputableInPolyTime (fun x => parentConstraint (es x) (v x)) e (encOption encUnary) :=
  poly_parentConstraint.comp (he.prod hv)

attribute [local fun_prop] poly_visitedWith poly_parentWith

private theorem poly_root : ComputableInPolyTime (fun p : WorkLog × ℕ => root p.1 p.2)
    (encPair encWorkLog encNat) encNat := by
  unfold root
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encWorkExpansion) (encL := encWorkLog)
    (growth := fun p => (encWorkLog p.1).length)
    (ComputableInPolyTime.snd encWorkLog encNat).tidy
  · refine ⟨(ComputableInPolyTime.fst encWorkLog encNat).tidy, ?_, inferInstance,
      inferInstance⟩
    exact (show ComputableInPolyTime
      (fun p : ((WorkLog × ℕ) × ℕ) × WorkExpansion =>
        if (p.2.2.find? (fun o => o.2.2 == p.1.2)).isSome then p.2.1.2.2 else p.1.2)
      (encPair (encPair (encPair encWorkLog encNat) encNat) encWorkExpansion) encNat
      from by fun_prop).tidy
  · refine ⟨(ComputableInPolyTime.fst encWorkLog encNat).polyBounded_length, ?_⟩
    intro p v e he
    rcases e with ⟨⟨constraint, port, parentVariable⟩, outputs⟩
    have hb := length_le_encList_of_mem encWorkExpansion he
    change (encWorkExpansion ((constraint, port, parentVariable), outputs)).length ≤
      (encWorkLog p.1).length at hb
    have hr : (encNat parentVariable).length ≤
        (encWorkExpansion ((constraint, port, parentVariable), outputs)).length := by
      simp only [encWorkExpansion, encRecord, encOccurrenceRecord, length_encPair]
      omega
    dsimp only
    split <;> omega

attribute [local fun_prop] poly_root

private theorem poly_partners : ComputableInPolyTime
    (fun p : Input × Record => partners p.1 p.2)
    (encPair encInput encRecord) (encList encRecord) := by
  unfold partners
  apply ComputableInPolyTime.filterWithInput (by fun_prop)
  fun_prop

private theorem poly_partnersWith {α : Type} {e : α ↪ List Bool}
    {input : α → Input} {a : α → Record}
    (hi : ComputableInPolyTime input e encInput)
    (ha : ComputableInPolyTime a e encRecord) :
    ComputableInPolyTime (fun x => partners (input x) (a x)) e (encList encRecord) :=
  poly_partners.comp (hi.prod ha)

attribute [local fun_prop] poly_partnersWith

/-- Scan parameters: roots, older log and input port, each preceding field framed. -/
private abbrev ScanArgs := List ℕ × WorkLog × Record
private abbrev encScanArgs := encPair (encList encNat) (encPair encWorkLog encRecord)

private theorem poly_scanStep : ComputableInPolyTime
    (fun p : (ScanArgs × ScanState) × Record =>
      scanStep p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
    (encPair (encPair encScanArgs encScanState) encRecord) encScanState := by
  unfold scanStep
  fun_prop

/-- Scan invocation: parameters followed by initial children and actual partner list. -/
private abbrev encScanInput := encPair encScanArgs
  (encPair (encList encRecord) (encList encRecord))

private theorem scanStep_size (rs : List ℕ) (es : WorkLog) (a b : Record) (s : ScanState) :
    (encScanState (scanStep rs es a s b)).length ≤
      (encScanState s).length + 2 * (2 * (encRecord b).length + 1) := by
  unfold scanStep
  dsimp only
  split
  · omega
  · split
    · simp [encScanState, encList_append, encList_cons, length_frame]
      omega
    · split
      · omega
      · simp [encScanState]
        omega

private theorem poly_scanInit : ComputableInPolyTime
    (fun p : ScanArgs × List Record × List Record => (p.2.1, none))
    encScanInput encScanState :=
  ((ComputableInPolyTime.snd encScanArgs
    (encPair (encList encRecord) (encList encRecord))).fst').prod (.const none)

private theorem poly_scanList : ComputableInPolyTime
    (fun p : ScanArgs × List Record × List Record => p.2.2)
    encScanInput (encList encRecord) :=
  (ComputableInPolyTime.snd encScanArgs
    (encPair (encList encRecord) (encList encRecord))).snd'

private theorem poly_scan : ComputableInPolyTime
    (fun p : ScanArgs × List Record × List Record =>
      scan p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2) encScanInput encScanState := by
  unfold scan
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (step := fun p s b => scanStep p.1 p.2.1 p.2.2 s b)
    (α := Record) (β := ScanState) (γ := ScanArgs × List Record × List Record)
    (π := ScanArgs) (encIn := encScanInput) (encP := encScanArgs)
    (encB := encScanState) (encA := encRecord) (encL := encList encRecord)
    (ComputableInPolyTime.fst encScanArgs
      (encPair (encList encRecord) (encList encRecord))).tidy
    poly_scanList.tidy
    poly_scanInit.tidy poly_scanStep.tidy
    (growth := fun p => 4 * (encList encRecord p.2.2).length + 4)
  · exact ((PolyBounded.const 4).mul poly_scanList.polyBounded_length).add (.const 4)
  · intro p s b hb
    have he := length_le_encList_of_mem encRecord hb
    exact (scanStep_size p.1.1 p.1.2.1 p.1.2.2 b s).trans (by omega)

private theorem poly_scanWith {α : Type} {e : α ↪ List Bool}
    {rs : α → List ℕ} {es : α → WorkLog} {a : α → Record}
    {os bs : α → List Record}
    (hr : ComputableInPolyTime rs e (encList encNat))
    (he : ComputableInPolyTime es e encWorkLog)
    (ha : ComputableInPolyTime a e encRecord)
    (ho : ComputableInPolyTime os e (encList encRecord))
    (hb : ComputableInPolyTime bs e (encList encRecord)) :
    ComputableInPolyTime (fun x => scan (rs x) (es x) (a x) (os x) (bs x)) e encScanState :=
by
  simpa only [Function.comp_def] using
    poly_scan.comp ((hr.prod (he.prod ha)).prod (ho.prod hb))

attribute [local fun_prop] poly_scanWith

private theorem poly_step : ComputableInPolyTime (fun p : Input × State => step p.1 p.2)
    (encPair encInput encState) encState := by
  unfold step
  fun_prop


private theorem scan_size (rs : List ℕ) (es : WorkLog) (a : Record)
    (bs : List Record) (s : ScanState) :
    (encScanState (bs.foldl (scanStep rs es a) s)).length ≤
      (encScanState s).length + 2 * (encList encRecord bs).length := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    have hi := ih (scanStep rs es a s b)
    have hs := scanStep_size rs es a b s
    simp only [List.foldl_cons, encList_cons, List.length_append, length_frame]
    omega

private theorem step_size (input : Input) (s : State) :
    (encState (step input s)).length ≤ (encState s).length +
      32 * (encList encRecord (CSP.occurrences input.body)).length + 32 := by
  rcases s with ⟨log, remaining, status⟩
  let B := (encList encRecord (CSP.occurrences input.body)).length
  simp only [step]
  split
  · omega
  · cases hn : remaining.find? (fun (_, _, vertex) => visited (roots input) log vertex) with
    | none => simp [encState]; omega
    | some a =>
      simp only [Option.elim_some]
      split
      next ha =>
        have ha' := length_le_encList_of_mem encRecord ha
        have hp : (encList encRecord (partners input a)).length ≤ B :=
          ComputableTidilyInDegree.length_encList_filter_le _ _ _
        have hs := scan_size (roots input) log a (partners input a) ([], none)
        change (encScanState (scan (roots input) log a [] (partners input a))).length ≤
          (encScanState ([], none)).length + 2 * _ at hs
        generalize ho : scan (roots input) log a [] (partners input a) = out at *
        rcases out with ⟨os, event⟩
        have hos : (encList encRecord os).length ≤ B + 1 := by
          simp only [encScanState, length_encPair] at hs
          simp only [encList_nil, List.length_nil, encOption_none] at hs
          omega
        cases event with
        | none =>
          have hf := ComputableTidilyInDegree.length_encList_filter_le encRecord
            (fun b => decide (b ∉ used ((a, os) :: log))) remaining
          simp only [Option.elim_none]
          calc
            _ = 2 * (encWorkLog log).length + 4 * (encWorkExpansion (a, os)).length +
                2 * (encList encRecord (remaining.filter
                  (fun b => decide (b ∉ used ((a, os) :: log))))).length + 4 := by
              simp only [encState, length_encPair, encWorkLog, encList_cons,
                List.length_append, length_frame, encOption_none, List.length_nil]
              ring
            _ ≤ 2 * (encWorkLog log).length + 4 * (encWorkExpansion (a, os)).length +
                2 * (encList encRecord remaining).length + 4 :=
              Nat.add_le_add_right
                (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hf) _) 4
            _ ≤ (encState (log, remaining, status)).length + 32 * B + 32 := by
              simp only [encState, encWorkExpansion, length_encPair]
              omega
        | some b =>
          have hb : (encRecord b).length ≤ 2 * B + 2 := by
            simp only [encScanState, length_encPair, encOption_some, List.length_cons,
              encList_nil, List.length_nil, encOption_none] at hs
            omega
          simp [encState, encEvent]
          omega
      next => simp [encState]; omega

private theorem poly_loop : ComputableInPolyTime
    (fun input => (step input)^[(CSP.occurrences input.body).length + 1]
      ([], CSP.occurrences input.body, none)) encInput encState := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth
    (show ComputableInPolyTime (fun input : Input =>
      (CSP.occurrences input.body).length + 1) encInput encUnary from by fun_prop).tidy
    (show ComputableInPolyTime (fun input : Input =>
      ([], CSP.occurrences input.body, none)) encInput encState from by fun_prop).tidy
    poly_step.tidy
    (growth := fun input => 32 * (encList encRecord (CSP.occurrences input.body)).length + 32)
  refine ⟨?_, step_size⟩
  exact ((PolyBounded.const 32).mul
    (EdgeAugmenting.poly_records.comp (encInput_body_polyTime .id')).polyBounded_length).add
    (.const 32)

attribute [local fun_prop] poly_loop

/-- Compute an occurrence record's binary output position by scanning the actual occurrence
list; an absent record returns the actual list length, also encoded in binary. -/
theorem poly_binaryIndex {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {o : α → Record}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (ho : ComputableInPolyTime o e encRecord) :
    ComputableInPolyTime (fun x => (CSP.occurrences (F x)).idxOf (o x)) e encNat :=
  ComputableInPolyTime.unary_to_binary.comp
    (EdgeAugmenting.poly_idxOf (EdgeAugmenting.poly_records.comp hF) ho)

attribute [local fun_prop] poly_binaryIndex

private theorem poly_finishExpansion : ComputableInPolyTime
    (fun p : CSP Table ℕ × WorkExpansion => finishExpansion p.1 p.2)
    (encPair (encCSP encTable encNat) encWorkExpansion) encExpansionCode := by
  unfold finishExpansion
  fun_prop

private theorem poly_finishExpansionWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {entry : α → WorkExpansion}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (he : ComputableInPolyTime entry e encWorkExpansion) :
    ComputableInPolyTime (fun x => finishExpansion (F x) (entry x)) e encExpansionCode :=
by
  simpa only [Function.comp_def] using poly_finishExpansion.comp (hF.prod he)

attribute [local fun_prop] poly_finishExpansionWith

private theorem poly_finish : ComputableInPolyTime (fun p : Input × State => finish p.1 p.2)
    (encPair encInput encState) (encOption encResultCode) := by
  unfold finish
  fun_prop

attribute [local fun_prop] poly_finish

/-- Uniform ordinary native polynomial time on every raw explicit-table CSP and finite buffer.
No implementation, runtime, semantic or invariant premise is supplied to this certificate. -/
@[fun_prop] theorem computableInPolyTime_run :
    ComputableInPolyTime run encInput (encOption encResultCode) := by
  unfold run
  fun_prop

end Cslib.Complexity.CSP.EdgeForest
