/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClassBalance
public import CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
public import CslibFrontier.Computability.GenericRAM.Native.StreamingFold
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Consuming generated opposite-class pairs without materializing the class

The sorted projected-quarter groups feed nested occurrence folds. Each matching
quarter pair is evaluated at original width and immediately enters the bounded
batch matcher. No half-space counter or complete opposite-class list is executed.
Original full-state and packed-word semantics reuse the proved quarter producer.
The actual uniform certificate charges captured-parameter/state copies and
matching temporaries; those costs still prevent a sharp global source theorem.
This is an implementation refinement toward [WangLvShenZhang2027], Lemma 8/Theorem 7,
PDF pp. 21–22, using its deterministic multitape bit convention (p. 6).

The encoded streaming kernel reads each list once. Time sums actual callback
work, current/next state and token framing over its rounds, with input/setup and
finalization charged separately. Workspace uses actual callback/prefix-state/
token maxima, with the returned state charged independently of time. Maxima are
derived over actual finite execution prefixes, not supplied invariants. Captured
parameters still include retained dictionaries and buffered records, so their
repeated state copies remain a sharp-global-time obstruction.

## Main definitions

* `feedPair`, `consumeGroup`, `consume`: generated matching-pair traversal and bounded batches.
* `run`, `buffer`: full consumer/final flush and logical generated-record prefix observer.
* `visits`: the actual nested matching-pair domain size, distinct from bit time.

## Main results

* `consume_eq`, `run_eq`: exact connection to the logical full-state class, without allocating it.
* `run_none`, `run_sound`, `run_empty`: exhaustive misses, witness provenance and empty-class skip.
* `consume_valid`, `buffer_valid`, `buffer_mem`: derived capacity and provenance at every prefix.
* `visits_le_count`: each class visits only generated matches; empty dictionaries skip them.
* `consumeCertificate`, `runCertificate`: uniform bit execution with replay/temporary costs.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.JoinedProbe
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Original input and produced side, with retained matcher parameters and batch capacity. -/
abbrev Context := (ClassBalance.Input × Bool) × (BatchedAccess.Parameter × ℕ)

/-- A generated quarter match is evaluated once at full width and immediately buffered/probed. -/
def feedPair (context : Context) (state : BatchedAccess.State)
    (a b : SortedMatch.Record) : BatchedAccess.State :=
  let ((input, right), (parameter, capacity)) := context
  BatchedAccess.feed parameter capacity state (ClassBalance.record input right (a.2/2, b.2/2))

/-- Stream a bucket's opposite-side occurrences in the approved left-major/right-minor order. -/
def consumeGroup (context : Context) (state : BatchedAccess.State)
    (group : List SortedMatch.Record) : BatchedAccess.State :=
  (KeyJoin.side false group).foldl (fun state a =>
    (KeyJoin.side true group).foldl (fun state b => feedPair context state a b) state) state

/-- Only quarter groups and one bounded batch are stored, not the generated half-class list. -/
def consume (context : Context) (state : BatchedAccess.State)
    (groups : List (List SortedMatch.Record)) : BatchedAccess.State :=
  groups.foldl (consumeGroup context) state

/-- The nested traversal is exactly the fold over the logical emitted full-state class.
This equation is used for semantics; the certificate below executes the nested folds. -/
theorem consume_eq (context : Context) (state : BatchedAccess.State)
    (groups : List (List SortedMatch.Record)) :
    let ((input, right), (parameter, capacity)) := context
    consume context state groups =
      ((KeyJoin.join groups).map (ClassBalance.record input right)).foldl
        (BatchedAccess.feed parameter capacity) state := by
  rcases context with ⟨⟨input, right⟩, parameter, capacity⟩
  simp only [consume, KeyJoin.join, List.foldl_map, List.foldl_flatMap, KeyJoin.pairs]
  rfl

/-- Actual produced-class prefixes retain the original bounded-batch capacity invariant. -/
theorem consume_valid (context : Context) (groups : List (List SortedMatch.Record))
    (hc : let (_, (_, capacity)) := context; 0 < capacity) :
    let (_, (_, capacity)) := context
    BatchedAccess.Valid capacity (consume context ((0, []), none) groups) := by
  rcases context with ⟨⟨input, right⟩, parameter, capacity⟩
  rw [consume_eq]
  exact BatchedAccess.fold_valid _ _ _ hc

private abbrev recEncoding := encPair encNat encNat
private abbrev contextEncoding := encPair (encPair ClassBalance.encoding encBool)
  (encPair BatchedAccess.parameterEncoding encNat)

/-- The exact encoded parameter/retained state of this online consumer. -/
def encoding : Context ↪ List Bool := contextEncoding

private noncomputable def feedPairCertificate : NativeCertificate
    (fun q : ((Context × SortedMatch.Record) × BatchedAccess.State) × SortedMatch.Record =>
      feedPair q.1.1.1 q.1.2 q.1.1.2 q.2)
    (encPair (encPair (encPair encoding recEncoding) BatchedAccess.stateEncoding) recEncoding)
    BatchedAccess.stateEncoding := by
  let ei := encPair (encPair (encPair encoding recEncoding) BatchedAccess.stateEncoding) recEncoding
  let original : NativeCertificate (id : ((Context × SortedMatch.Record) × BatchedAccess.State) ×
      SortedMatch.Record → _) ei ei := .linear (.of_eq (fun _ => rfl))
  let context := original.fst.fst.fst
  let a := original.fst.fst.snd
  let b := original.snd
  have indices : ComputableInPolyTime (fun q : SortedMatch.Record × SortedMatch.Record =>
      (q.1.2/2, q.2.2/2)) (encPair recEncoding recEncoding) recEncoding := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.prod <;>
      (apply ComputableTidilyInPolyTime.binary_div' <;> dsimp only [recEncoding] <;> fun_prop)
  let index := (NativeCertificate.ofPolyTime indices).comp (a.prod b)
  let record := (NativeCertificate.ofPolyTime ClassBalance.record_polyTime).comp
    (context.fst.prod index)
  let fresh := BatchedAccess.feedCertificate.comp
    (context.snd.prod (original.fst.snd.prod record))
  let parked := original.fst.snd
  let found := parked.snd.post ((ComputableInDegree.isSome recEncoding).inO_one)
  exact NativeCertificate.congr (NativeCertificate.branch found parked fresh) (fun q => by
    rcases q with ⟨⟨⟨context, a⟩, ⟨⟨used, batch⟩, found⟩⟩, b⟩
    cases found <;> simp [feedPair, BatchedAccess.feed])

private noncomputable def consumeGroupCertificate : NativeCertificate
    (fun q : (Context × BatchedAccess.State) × List SortedMatch.Record =>
      consumeGroup q.1.1 q.1.2 q.2)
    (encPair (encPair encoding BatchedAccess.stateEncoding) (encList recEncoding))
    BatchedAccess.stateEncoding := by
  let inner := NativeCertificate.foldlStream (encPair encoding recEncoding)
    BatchedAccess.stateEncoding recEncoding (fun q state b => feedPair q.1 state q.2 b)
    feedPairCertificate
  let ei := encPair (encPair encoding BatchedAccess.stateEncoding) (encList recEncoding)
  let original : NativeCertificate (id : (Context × BatchedAccess.State) ×
      List SortedMatch.Record → _) ei ei := .linear (.of_eq (fun _ => rfl))
  -- Both filters execute on actual quarter records; no opposite-class array is constructed.
  let filterProof := (Classical.choose_spec
    (ComputableInO.filter_stream KeyJoinStream.test_polyTime)).2.2
  let filtered : NativeCertificate
      (fun q : Bool × List SortedMatch.Record => KeyJoin.side q.1 q.2)
      (encPair encBool (encList recEncoding)) (encList recEncoding) := ⟨_, _, filterProof⟩
  let raw : NativeCertificate (id : List SortedMatch.Record → _)
      (encList recEncoding) (encList recEncoding) := .linear (.of_eq (fun _ => rfl))
  let side (right : Bool) := filtered.comp ((NativeCertificate.const right).prod raw)
  let left := (side false).comp original.snd
  let right := (side true).comp original.snd
  let outerEi := encPair (encPair (encPair encoding (encList recEncoding))
    BatchedAccess.stateEncoding) recEncoding
  let arg : NativeCertificate (id : ((Context × List SortedMatch.Record) × BatchedAccess.State) ×
      SortedMatch.Record → _) outerEi outerEi := .linear (.of_eq (fun _ => rfl))
  let round := NativeCertificate.congr (inner.comp
    ((arg.fst.fst.fst.prod arg.snd).prod (arg.fst.snd.prod arg.fst.fst.snd))) (fun _ => rfl)
  let outer := NativeCertificate.foldlStream (encPair encoding (encList recEncoding))
    BatchedAccess.stateEncoding recEncoding
    (fun q state a => q.2.foldl (fun state b => feedPair q.1 state a b) state) round
  exact NativeCertificate.congr (outer.comp
    ((original.fst.fst.prod right).prod (original.fst.snd.prod left))) (fun _ => rfl)

/-- A real fixed uniform streaming machine, with all parameter/state/callback copying and
matching temporaries in its time/prefix-space profile. No sharp bound is assumed. -/
noncomputable def consumeCertificate : NativeCertificate
    (fun q : Context × (BatchedAccess.State × List (List SortedMatch.Record)) =>
      consume q.1 q.2.1 q.2.2)
    (encPair encoding (encPair BatchedAccess.stateEncoding
      (encList (encList (encPair encNat encNat))))) BatchedAccess.stateEncoding :=
  NativeCertificate.foldlStream encoding BatchedAccess.stateEncoding (encList recEncoding)
    consumeGroup consumeGroupCertificate

/-- Generate only the selected projected quarter groups of the produced side. -/
def groups (context : Context) (g : ℕ) : List (List SortedMatch.Record) :=
  let ((input, right), _) := context
  ClassJoin.groups (ClassBalance.queryInput input right g)

/-- Final partial batches are matched after the nested opposite-class fold. -/
def run (context : Context) (g : ℕ) : Option (ℕ × ℕ) :=
  let (_, (parameter, _)) := context
  BatchedAccess.finish parameter (consume context ((0, []), none) (groups context g))

/-- Logical emitted records identify every nested consumer step without allocating that list. -/
theorem run_eq (context : Context) (g : ℕ) :
    let ((input, right), (parameter, capacity)) := context
    run context g = BatchedAccess.finish parameter
      ((ClassBalance.records input right g).foldl (BatchedAccess.feed parameter capacity)
        ((0, []), none)) := by
  rcases context with ⟨⟨input, right⟩, parameter, capacity⟩
  rw [run, consume_eq]
  rfl

/-- Exhaustive miss semantics for the actual generated opposite stream. -/
theorem run_none (context : Context) (g : ℕ)
    (fits : let ((input, right), ((w, (_, kept)), _)) := context
      ∀ r ∈ kept ++ ClassBalance.records input right g, r.1 < 2 ^ w) :
    run context g = none ↔
      let ((input, right), ((_, (_, kept)), _)) := context
      ¬ BatchedAccess.Meets kept (ClassBalance.records input right g) := by
  rcases context with ⟨⟨input, right⟩, ⟨w, orientation, kept⟩, capacity⟩
  rw [run_eq]
  exact BatchedAccess.fold_none _ _ _ fits

/-- Returned packed witnesses come from the retained dictionary and actual generated records. -/
theorem run_sound (context : Context) (g : ℕ) (out : ℕ × ℕ) (hit : run context g = some out) :
    let ((input, right), ((_, (orientation, kept)), _)) := context
    ∃ a ∈ kept, ∃ b ∈ ClassBalance.records input right g, a.1 = b.1 ∧
      out = if orientation then (b.2, a.2) else (a.2, b.2) := by
  rcases context with ⟨⟨input, right⟩, ⟨w, orientation, kept⟩, capacity⟩
  rw [run_eq] at hit
  exact BatchedAccess.fold_sound _ _ _ out hit

/-- An empty retained dictionary cannot return a hit, even for a raw mismatched context.
The machine uses this consequence of actual matcher soundness to skip generation entirely. -/
theorem run_empty (context : Context) (g : ℕ)
    (empty : let (_, ((_, (_, kept)), _)) := context; kept = []) : run context g = none := by
  rcases context with ⟨source, ⟨width, orientation, kept⟩, capacity⟩
  dsimp only at empty
  cases h : run (source, ((width, (orientation, kept)), capacity)) g with
  | none => rfl
  | some out =>
    obtain ⟨a, ha, _⟩ := run_sound _ _ out h
    simp only [empty, List.not_mem_nil] at ha

/-- Buffer observer after any number of generated pairs; the executed program uses nested
folds and stores neither this full logical class list nor all full-state half words. -/
def buffer (context : Context) (g n : ℕ) : List (ℕ × ℕ) :=
  let ((input, right), (parameter, capacity)) := context
  let ((_, batch), _) := ((ClassBalance.records input right g).take n).foldl
    (BatchedAccess.feed parameter capacity) ((0, []), none)
  batch

/-- Every generated-record prefix satisfies the actual capacity invariant. -/
theorem buffer_valid (context : Context) (g n : ℕ)
    (hc : let (_, (_, capacity)) := context; 0 < capacity) :
    let (_, (_, capacity)) := context
    (buffer context g n).length < capacity := by
  rcases context with ⟨⟨input, right⟩, parameter, capacity⟩
  have h := BatchedAccess.fold_valid parameter capacity
    ((ClassBalance.records input right g).take n) hc
  exact h.1 ▸ h.2

/-- Only full states of already generated original half words enter any buffered prefix. -/
theorem buffer_mem (context : Context) (g n : ℕ) (r : ℕ × ℕ)
    (hr : r ∈ buffer context g n) :
    let ((input, right), _) := context
    r ∈ ClassBalance.records input right g := by
  rcases context with ⟨⟨input, right⟩, parameter, capacity⟩
  exact List.mem_of_mem_take (BatchedAccess.buffer_mem parameter capacity
    ((ClassBalance.records input right g).take n) r hr)

/-- Matching-quarter iteration slots of the executed consumer, including found-hit parking.
The empty-dictionary guard skips the entire generated domain. This is not a bit-time bound. -/
def visits (context : Context) (g : ℕ) : ℕ :=
  let (_, ((_, (_, kept)), _)) := context
  if kept.isEmpty then 0 else KeyJoin.count (groups context g)

/-- The actual nested traversal visits at most the generated opposite class, not its half space. -/
theorem visits_le_count (context : Context) (g : ℕ) :
    let ((input, right), _) := context
    visits context g ≤ ClassBalance.count input right g := by
  rcases context with ⟨⟨input, right⟩, ⟨width, orientation, kept⟩, capacity⟩
  dsimp only [visits]
  split <;> simp [groups, ClassBalance.count, ClassJoin.count]

/-- Real quarter generation, direct pair consumption and final sorted-batch readback compose
in one fixed uniform bit machine. No whole opposite class is an executed intermediate value. -/
noncomputable def runCertificate : NativeCertificate
    (fun q : Context × ℕ => run q.1 q.2) (encPair encoding encNat)
    (encOption (encPair encNat encNat)) := by
  let ei := encPair encoding encNat
  let original : NativeCertificate (id : Context × ℕ → _) ei ei := .linear (.of_eq (fun _ => rfl))
  let query := (NativeCertificate.ofPolyTime ClassBalance.queryInput_polyTime).comp
    (original.fst.fst.prod original.snd)
  let produced := ClassJoin.groupsCertificate.comp query
  let initial : NativeCertificate (fun _ : Context × ℕ =>
      (((0 : ℕ), ([] : List (ℕ × ℕ))), (none : Option (ℕ × ℕ)))) ei
      BatchedAccess.stateEncoding := .const _
  let consumed := consumeCertificate.comp (original.fst.prod (initial.prod produced))
  let fresh := NativeCertificate.congr (BatchedAccess.finishCertificate.comp
    (original.fst.snd.fst.prod consumed)) (fun _ => rfl)
  let empty := original.fst.snd.fst.snd.snd.post
    ((ComputableInDegree.listIsEmpty recEncoding).inO_one)
  let missing : NativeCertificate (fun _ : Context × ℕ => (none : Option (ℕ × ℕ))) ei
      (encOption recEncoding) := .const _
  exact NativeCertificate.congr (NativeCertificate.branch empty missing fresh) (fun q => by
    rcases q with ⟨⟨source, ⟨width, orientation, kept⟩, capacity⟩, g⟩
    cases kept with
    | nil => exact (run_empty (source, ((width, (orientation, [])), capacity)) g rfl).symm
    | cons r rows => rfl)

end Cslib.Cryptanalysis.AddXNOR.JoinedProbe
