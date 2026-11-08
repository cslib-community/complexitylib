/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Batched sorted access for a retained source class

Buffer opposite-side occurrences up to a computed class-size capacity, sort and
match each full batch using the uniform radix matcher, then release that batch.
No per-record retained-list lookup is executed. The final partial batch is also
matched. Counts and buffered records preserve occurrence multiplicities, and
returned witnesses retain original packed indices.

The original-input route below reuses actual computed class counts, orientation,
retention and original packed-state evaluation, with structural linear insertion
in place of the old complete-list polynomial retaining callback. Repeated class
scans and counter-state copying costs remain separate gaps;
this access replacement does not conclude the source's global sharp bounds.
This batching is an original implementation refinement of retained-list testing in
[WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.


## Main definitions

* `feed`, `finish`, `probe`: bounded sorted batches and the actual packed-counter producer.
* `retainCertificate`, `sourceCertificate`: structural retention and integrated bit execution.

## Main results

* `fold_none`, `fold_sound`, `original_correct`: exhaustive misses and original witness provenance.
* `fold_valid`, `source_buffer_bound`: actual live batch bounds from computed counts.
* `recordWork_bound`, `total_recordWork`: amortized flush volume, not standalone bit time.
* `original_machine`: one uniform original-input bit machine with all composed phase profiles.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.BatchedAccess
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Physical key width, retained orientation and actual retained occurrences. -/
abbrev Parameter := ℕ × (Bool × List (ℕ × ℕ))

/-- Buffered count/list and the first hit. -/
abbrev State := (ℕ × List (ℕ × ℕ)) × Option (ℕ × ℕ)

/-- Actual full-state matching, normalizing both orientations to forward/inverse payload order. -/
def matchBatch (parameter : Parameter) (batch : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  let (width, (right, kept)) := parameter
  SortedMatch.run (width, if right then (batch, kept) else (kept, batch))

/-- Buffer a record or sort/match/release a full batch. A found hit suppresses later batches. -/
def feed (parameter : Parameter) (capacity : ℕ) (state : State) (r : ℕ × ℕ) : State :=
  let ((used, batch), found) := state
  if found.isSome then state else
    if used + 1 < capacity then ((used + 1, r :: batch), none)
    else ((0, []), matchBatch parameter (r :: batch))

/-- Flush the final partial batch, unless an earlier batch already found a hit. -/
def finish (parameter : Parameter) (state : State) : Option (ℕ × ℕ) :=
  let ((_, batch), found) := state
  found.orElse (fun _ => matchBatch parameter batch)

/-- Mathematical common-key predicate, not supplied dictionary correctness. -/
def Meets (kept batch : List (ℕ × ℕ)) : Prop :=
  ∃ a ∈ kept, ∃ b ∈ batch, a.1 = b.1

private theorem match_none (parameter : Parameter) (batch : List (ℕ × ℕ))
    (fits : let (w, (_, kept)) := parameter; ∀ r ∈ kept ++ batch, r.1 < 2 ^ w) :
    matchBatch parameter batch = none ↔
      let (_, (_, kept)) := parameter; ¬ Meets kept batch := by
  rcases parameter with ⟨w, right, kept⟩
  cases right with
  | false => exact SortedMatch.none_iff (w, (kept, batch)) fits
  | true =>
    have hf : ∀ r ∈ batch ++ kept, r.1 < 2 ^ w := by
      intro r hr
      exact fits r (by simpa only [List.mem_append, or_comm] using hr)
    rw [matchBatch, SortedMatch.none_iff _ hf]
    constructor <;> intro hno hex
    · obtain ⟨a, ha, b, hb, he⟩ := hex
      exact hno ⟨b, hb, a, ha, he.symm⟩
    · obtain ⟨b, hb, a, ha, he⟩ := hex
      exact hno ⟨a, ha, b, hb, he.symm⟩

private theorem match_sound (parameter : Parameter) (batch : List (ℕ × ℕ)) (out : ℕ × ℕ)
    (hit : matchBatch parameter batch = some out) :
    let (_, (right, kept)) := parameter
    ∃ a ∈ kept, ∃ b ∈ batch, a.1 = b.1 ∧
      out = if right then (b.2, a.2) else (a.2, b.2) := by
  rcases parameter with ⟨w, right, kept⟩
  cases right with
  | false => exact SortedMatch.sound (w, (kept, batch)) out hit
  | true =>
    obtain ⟨b, hb, a, ha, he, ho⟩ := SortedMatch.sound (w, (batch, kept)) out hit
    exact ⟨a, ha, b, hb, he.symm, ho⟩

/-- Buffer count agrees with the actual list and remains strictly below capacity. -/
def Valid (capacity : ℕ) (state : State) : Prop :=
  let ((used, batch), _) := state
  used = batch.length ∧ used < capacity

/-- Each feed preserves the derived capacity invariant, including found-hit parking. -/
theorem feed_valid (parameter : Parameter) (capacity : ℕ) (state : State) (r : ℕ × ℕ)
    (h : Valid capacity state) : Valid capacity (feed parameter capacity state r) := by
  rcases state with ⟨⟨used, batch⟩, found⟩
  dsimp only [feed]
  split_ifs <;> simp_all [Valid] <;> omega

private theorem mem_feed (parameter : Parameter) (capacity : ℕ) (state : State)
    (r a : ℕ × ℕ) (ha : a ∈ (feed parameter capacity state r).1.2) :
    a ∈ state.1.2 ∨ a = r := by
  rcases state with ⟨⟨used, batch⟩, found⟩
  dsimp only [feed] at ha
  split_ifs at ha <;> simp_all [or_comm]

private theorem meets_append (kept xs ys : List (ℕ × ℕ)) :
    Meets kept (xs ++ ys) ↔ Meets kept xs ∨ Meets kept ys := by
  simp only [Meets, List.mem_append, or_and_right, exists_or, and_or_left]

/-- Every buffered record comes from the actual records already fed. -/
theorem buffer_mem (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (r : ℕ × ℕ)
    (hr : let ((_, batch), _) := rows.foldl (feed parameter capacity) ((0, []), none)
      r ∈ batch) : r ∈ rows := by
  have h (rows : List (ℕ × ℕ)) (state : State) (r : ℕ × ℕ)
      (hr : r ∈ ((rows.foldl (feed parameter capacity) state).1.2)) :
      r ∈ state.1.2 ∨ r ∈ rows := by
    induction rows generalizing state with
    | nil => exact .inl hr
    | cons x rows ih =>
      rcases ih (feed parameter capacity state x) hr with hb | ht
      · rcases mem_feed parameter capacity state x r hb with hb | rfl
        · exact .inl hb
        · exact .inr (by simp)
      · exact .inr (List.mem_cons_of_mem _ ht)
  simpa using h rows ((0, []), none) r hr

private theorem finish_none (parameter : Parameter) (state : State)
    (fits : let (w, (_, kept)) := parameter; ∀ r ∈ kept ++ state.1.2, r.1 < 2 ^ w) :
    finish parameter state = none ↔ state.2 = none ∧
      let (_, (_, kept)) := parameter; ¬ Meets kept state.1.2 := by
  rcases state with ⟨⟨used, batch⟩, found⟩
  change (found <|> matchBatch parameter batch) = none ↔ _
  rw [Option.orElse_eq_none, match_none parameter batch fits]

private theorem feed_finish_none (parameter : Parameter) (capacity : ℕ) (state : State)
    (r : ℕ × ℕ)
    (fits : let (w, (_, kept)) := parameter; ∀ a ∈ kept ++ r :: state.1.2, a.1 < 2 ^ w) :
    finish parameter (feed parameter capacity state r) = none ↔
      finish parameter state = none ∧
        let (_, (_, kept)) := parameter; ¬ Meets kept [r] := by
  rcases parameter with ⟨w, right, kept⟩
  have hold : ∀ a ∈ kept ++ state.1.2, a.1 < 2 ^ w := by
    intro a ha
    exact fits a (by simp only [List.mem_append, List.mem_cons] at *; tauto)
  rcases state with ⟨⟨used, batch⟩, found⟩
  cases found with
  | some out => simp [feed, finish]
  | none =>
    dsimp only [feed, finish]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Option.orElse_none]
    split_ifs
    · dsimp only
      change matchBatch (w, right, kept) (r :: batch) = none ↔ _
      rw [match_none (w, right, kept) (r :: batch) fits,
        match_none (w, right, kept) batch hold]
      dsimp only
      rw [show r :: batch = [r] ++ batch from rfl, meets_append]
      tauto
    · change (matchBatch (w, right, kept) (r :: batch) <|>
        matchBatch (w, right, kept) []) = none ↔ _
      rw [Option.orElse_eq_none, match_none (w, right, kept) (r :: batch) fits,
        match_none (w, right, kept) batch hold]
      dsimp only
      have hempty : matchBatch (w, right, kept) [] = none :=
        (match_none _ _ (fun a ha => hold a (List.mem_append_left _ (by simpa using ha)))).mpr
          (by simp [Meets])
      simp only [hempty, show r :: batch = [r] ++ batch from rfl, meets_append]
      tauto

/-- Exhaustive miss for the actual buffered/sorted route, with physical key fit only. -/
theorem fold_none (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (fits : let (w, (_, kept)) := parameter; ∀ r ∈ kept ++ rows, r.1 < 2 ^ w) :
    finish parameter (rows.foldl (feed parameter capacity) ((0, []), none)) = none ↔
      let (_, (_, kept)) := parameter; ¬ Meets kept rows := by
  rcases parameter with ⟨w, right, kept⟩
  have h (rows : List (ℕ × ℕ)) (state : State)
      (fits : ∀ r ∈ kept ++ (state.1.2 ++ rows), r.1 < 2 ^ w) :
      finish (w, right, kept) (rows.foldl (feed (w, right, kept) capacity) state) = none ↔
        finish (w, right, kept) state = none ∧ ¬ Meets kept rows := by
    induction rows generalizing state with
    | nil => simp [Meets]
    | cons r rows ih =>
      have hfit : ∀ a ∈ kept ++ r :: state.1.2, a.1 < 2 ^ w := by
        intro a ha
        apply fits a
        simp only [List.mem_append, List.mem_cons] at *
        tauto
      have newfit : ∀ a ∈ kept ++ ((feed (w, right, kept) capacity state r).1.2 ++ rows),
          a.1 < 2 ^ w := by
        intro a ha
        apply fits a
        simp only [List.mem_append] at ha ⊢
        rcases ha with ha | ha | ha
        · exact .inl ha
        · rcases mem_feed (w, right, kept) capacity state r a ha with ha | rfl
          · exact .inr (.inl ha)
          · exact .inr (.inr (by simp))
        · exact .inr (.inr (List.mem_cons_of_mem _ ha))
      rw [List.foldl_cons, ih _ newfit, feed_finish_none _ _ _ _ hfit]
      rw [show r :: rows = [r] ++ rows from rfl, meets_append]
      tauto
  have hempty : finish (w, right, kept) ((0, []), none) = none := by
    apply (finish_none _ _ (fun a ha => fits a (by
      simp only [List.mem_append, List.not_mem_nil, or_false] at ha
      exact List.mem_append_left _ ha))).mpr
    simp [Meets]
  exact (h rows ((0, []), none) (by simpa using fits)).trans
    (by simp only [hempty, true_and])


/-- All buffered prefixes satisfy the actual capacity invariant. -/
theorem fold_valid (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (hc : 0 < capacity) :
    Valid capacity (rows.foldl (feed parameter capacity) ((0, []), none)) := by
  have h (rows : List (ℕ × ℕ)) (state : State) (hv : Valid capacity state) :
      Valid capacity (rows.foldl (feed parameter capacity) state) := by
    induction rows generalizing state with
    | nil => exact hv
    | cons r rows ih => exact ih _ (feed_valid _ _ _ _ hv)
  exact h rows ((0, []), none) ⟨rfl, hc⟩

/-- Record-volume charge for one feed: a full flush reads the retained list and batch.
This is an amortization observer, not a bit-machine time theorem on its own. -/
def feedCharge (parameter : Parameter) (capacity : ℕ) (state : State) : ℕ :=
  let (_, (_, kept)) := parameter
  let ((used, _), found) := state
  if found.isSome then 0 else if used + 1 < capacity then 1 else kept.length + capacity + 1

/-- Cumulative actual flush-volume charges along the buffered execution. -/
def recordWork (parameter : Parameter) (capacity : ℕ) : State → List (ℕ × ℕ) → ℕ
  | _, [] => 0
  | state, r :: rows => feedCharge parameter capacity state +
      recordWork parameter capacity (feed parameter capacity state r) rows

private theorem charge_potential (parameter : Parameter) (capacity : ℕ) (state : State)
    (r : ℕ × ℕ) (h : Valid capacity state)
    (hk : let (_, (_, kept)) := parameter; kept.length ≤ capacity) :
    feedCharge parameter capacity state + 3 * (feed parameter capacity state r).1.1 ≤
      4 + 3 * state.1.1 := by
  rcases parameter with ⟨w, right, kept⟩
  rcases state with ⟨⟨used, batch⟩, found⟩
  dsimp only [feedCharge, feed]
  dsimp only [Valid] at h
  split_ifs <;> dsimp only at * <;> omega

/-- Capacity at least the retained size makes total flush-volume work linear in the
stream length, even with duplicate keys and early hits. Bit sorting costs remain separate. -/
theorem recordWork_bound (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (hc : 0 < capacity)
    (hk : let (_, (_, kept)) := parameter; kept.length ≤ capacity) :
    recordWork parameter capacity ((0, []), none) rows ≤ 4 * rows.length := by
  have h (rows : List (ℕ × ℕ)) (state : State) (hv : Valid capacity state) :
      recordWork parameter capacity state rows +
        3 * (rows.foldl (feed parameter capacity) state).1.1 ≤
          4 * rows.length + 3 * state.1.1 := by
    induction rows generalizing state with
    | nil => simp [recordWork]
    | cons r rows ih =>
      have ht := ih (feed parameter capacity state r) (feed_valid _ _ _ _ hv)
      have hs := charge_potential parameter capacity state r hv hk
      simp only [recordWork, List.foldl_cons, List.length_cons]
      omega
  have := h rows ((0, []), none) ⟨rfl, hc⟩
  dsimp only at this
  omega

/-- Include the final partial-batch read in the amortized record-volume budget.
Input copying, bit operations and counter-state copying are not omitted from machine profiles. -/
theorem total_recordWork (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (hc : 0 < capacity)
    (hk : let (_, (_, kept)) := parameter; kept.length ≤ capacity) :
    let (_, (_, kept)) := parameter
    let ((_, batch), _) := rows.foldl (feed parameter capacity) ((0, []), none)
    recordWork parameter capacity ((0, []), none) rows + kept.length + batch.length + 1 ≤
      4 * rows.length + 2 * capacity + 1 := by
  have hw := recordWork_bound parameter capacity rows hc hk
  have hv := fold_valid parameter capacity rows hc
  rcases parameter with ⟨w, right, kept⟩
  dsimp only [Valid] at hv
  dsimp only at hk ⊢
  omega

private theorem finish_sound (parameter : Parameter) (state : State) (out : ℕ × ℕ)
    (hit : finish parameter state = some out) :
    state.2 = some out ∨
      let (_, (right, kept)) := parameter
      ∃ a ∈ kept, ∃ b ∈ state.1.2, a.1 = b.1 ∧
        out = if right then (b.2, a.2) else (a.2, b.2) := by
  rcases state with ⟨⟨used, batch⟩, found⟩
  change (found <|> matchBatch parameter batch) = some out at hit
  rcases (Option.orElse_eq_some _ _ _).mp hit with old | ⟨_, fresh⟩
  · exact .inl old
  · exact .inr (match_sound parameter batch out fresh)

private theorem feed_found (parameter : Parameter) (capacity : ℕ) (state : State)
    (r out : ℕ × ℕ) (hit : (feed parameter capacity state r).2 = some out) :
    state.2 = some out ∨
      let (_, (right, kept)) := parameter
      ∃ a ∈ kept, ∃ b ∈ r :: state.1.2, a.1 = b.1 ∧
        out = if right then (b.2, a.2) else (a.2, b.2) := by
  rcases parameter with ⟨w, right, kept⟩
  rcases state with ⟨⟨used, batch⟩, found⟩
  cases found with
  | some old =>
    simp only [feed, Option.isSome_some, ite_true] at hit
    exact .inl hit
  | none =>
    by_cases h : used + 1 < capacity
    · simp [feed, h] at hit
    · simp only [feed, Option.isSome_none, Bool.false_eq_true, ite_false, h] at hit
      exact .inr (match_sound (w, right, kept) _ out hit)

/-- Every reported hit comes from an actual retained and streamed occurrence. -/
theorem fold_sound (parameter : Parameter) (capacity : ℕ) (rows : List (ℕ × ℕ))
    (out : ℕ × ℕ)
    (hit : finish parameter (rows.foldl (feed parameter capacity) ((0, []), none)) = some out) :
    let (_, (right, kept)) := parameter
    ∃ a ∈ kept, ∃ b ∈ rows, a.1 = b.1 ∧
      out = if right then (b.2, a.2) else (a.2, b.2) := by
  rcases parameter with ⟨w, right, kept⟩
  have h (rows : List (ℕ × ℕ)) (state : State)
      (hit : (rows.foldl (feed (w, right, kept) capacity) state).2 = some out) :
      state.2 = some out ∨ ∃ a ∈ kept, ∃ b ∈ state.1.2 ++ rows,
        a.1 = b.1 ∧ out = if right then (b.2, a.2) else (a.2, b.2) := by
    induction rows generalizing state with
    | nil => exact .inl hit
    | cons r rows ih =>
      rcases ih (feed (w, right, kept) capacity state r) hit with
        old | ⟨a, ha, b, hb, he, ho⟩
      · rcases feed_found (w, right, kept) capacity state r out old with
          old | ⟨a, ha, b, hb, he, ho⟩
        · exact .inl old
        · refine .inr ⟨a, ha, b, ?_, he, ho⟩
          simp only [List.mem_cons] at hb
          simp only [List.mem_append, List.mem_cons]
          tauto
      · refine .inr ⟨a, ha, b, ?_, he, ho⟩
        rcases List.mem_append.mp hb with hb | hb
        · rcases mem_feed (w, right, kept) capacity state r b hb with hb | rfl
          · exact List.mem_append_left _ hb
          · simp
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)
  rcases finish_sound (w, right, kept) _ out hit with old | ⟨a, ha, b, hb, he, ho⟩
  · simpa using h rows ((0, []), none) old
  · exact ⟨a, ha, b, buffer_mem _ _ _ b hb, he, ho⟩


/-- Runtime width/orientation and retained binary records. -/
def parameterEncoding : Parameter ↪ List Bool :=
  encPair encUnary (encPair encBool (encList RadixPartition.recordEncoding))

/-- Buffered count, actual framed records and optional packed witness. -/
def stateEncoding : State ↪ List Bool :=
  encPair (encPair encNat (encList RadixPartition.recordEncoding))
    (encOption RadixPartition.recordEncoding)

/-- One fixed radix/scan machine handles either retained orientation. -/
noncomputable def matchCertificate : NativeCertificate
    (fun q : Parameter × List (ℕ × ℕ) => matchBatch q.1 q.2)
    (encPair parameterEncoding (encList RadixPartition.recordEncoding))
    (encOption RadixPartition.recordEncoding) := by
  let ei := encPair parameterEncoding (encList RadixPartition.recordEncoding)
  let original : NativeCertificate (id : Parameter × List (ℕ × ℕ) → _) ei ei :=
    .linear (.of_eq (fun _ => rfl))
  let right := original.fst.snd.fst
  let forward := original.fst.fst.prod (original.fst.snd.snd.prod original.snd)
  let backward := original.fst.fst.prod (original.snd.prod original.fst.snd.snd)
  let arguments := NativeCertificate.branch right backward forward
  exact NativeCertificate.congr (SortedMatch.runCertificate.comp arguments) (fun q => by
    dsimp only [matchBatch, Function.comp_def, id_eq]
    split_ifs <;> rfl)

private def feedEncoding := encPair (encPair parameterEncoding encNat)
  (encPair stateEncoding RadixPartition.recordEncoding)

/-- Real batching uses linear framed insertion and structural projections. Only binary scalar
arithmetic is sent through polynomial-time callbacks; no callback captures a complete batch. -/
noncomputable def feedCertificate : NativeCertificate
    (fun q : (Parameter × ℕ) × (State × (ℕ × ℕ)) => feed q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair parameterEncoding encNat)
      (encPair stateEncoding RadixPartition.recordEncoding))
    stateEncoding := by
  let original : NativeCertificate (id : (Parameter × ℕ) × (State × (ℕ × ℕ)) → _)
      feedEncoding feedEncoding := .linear (.of_eq (fun _ => rfl))
  let state := original.snd.fst
  let found := state.snd.post
    ((ComputableInDegree.isSome RadixPartition.recordEncoding).inO_one)
  have hs : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let used := (NativeCertificate.ofPolyTime hs).comp state.fst.fst
  let buffer := (original.snd.snd.prod state.fst.snd).post
    ((ComputableInDegree.cons RadixPartition.recordEncoding).inO_one)
  have hlt : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.1 < q.2))
      (encPair encNat encNat) encBool := by fun_prop
  let small := (NativeCertificate.ofPolyTime hlt).comp (used.prod original.fst.snd)
  let none : NativeCertificate (fun _ : (Parameter × ℕ) × (State × (ℕ × ℕ)) =>
      (none : Option (ℕ × ℕ))) feedEncoding (encOption RadixPartition.recordEncoding) := .const _
  let growing := (used.prod buffer).prod none
  let matched := matchCertificate.comp (original.fst.fst.prod buffer)
  let empty : NativeCertificate (fun _ : (Parameter × ℕ) × (State × (ℕ × ℕ)) =>
      ((0 : ℕ), ([] : List (ℕ × ℕ)))) feedEncoding
      (encPair encNat (encList RadixPartition.recordEncoding)) := .const _
  let flushed := empty.prod matched
  exact NativeCertificate.congr
    (NativeCertificate.branch found state (NativeCertificate.branch small growing flushed))
    (fun q => by simp only [feed, Function.comp_def, id_eq, decide_eq_true_eq])

/-- Final-batch matching is selected only if no earlier batch returned a hit. -/
noncomputable def finishCertificate : NativeCertificate
    (fun q : Parameter × State => finish q.1 q.2) (encPair parameterEncoding stateEncoding)
    (encOption RadixPartition.recordEncoding) := by
  let ei := encPair parameterEncoding stateEncoding
  let original : NativeCertificate (id : Parameter × State → _) ei ei :=
    .linear (.of_eq (fun _ => rfl))
  let found := original.snd.snd
  let final := matchCertificate.comp (original.fst.prod original.snd.fst.snd)
  let yes : NativeCertificate (fun q : (Parameter × State) × (ℕ × ℕ) => some q.2)
      (encPair ei RadixPartition.recordEncoding) (encOption RadixPartition.recordEncoding) :=
    ((NativeCertificate.linear (.of_eq (fun _ => rfl))).snd).some
  exact NativeCertificate.congr (found.option final yes) (fun q => by
    dsimp only [finish, id_eq, Function.comp_def]
    cases q.2.2 <;> rfl)


/-- Original class task, retained occurrences and computed batch capacity. -/
abbrev Task := ((ClassStreaming.Input × Bool) × List (ℕ × ℕ)) × ℕ

/-- Physical matching parameters are taken from the actual original class task. -/
def parameters (task : Task) : Parameter :=
  let (((input, right), kept), _) := task
  let (halves, _) := input
  let ((width, _), _) := halves
  (width, (right, kept))

/-- One opposite packed word is evaluated; only accepted records enter the bounded buffer. -/
def probeStep (task : Task) (state : ℕ × State) : ℕ × State :=
  let (((input, right), _), capacity) := task
  let (index, buffered) := state
  (index + 1, if ClassStreaming.accepts input (!right) index then
    feed (parameters task) capacity buffered (ClassStreaming.row input (!right) index)
    else buffered)

/-- The actual producer is a packed counter, not a materialized opposite-class list. -/
def probe (task : Task) : Option (ℕ × ℕ) :=
  let (((input, right), _), _) := task
  let final := (probeStep task)^[ClassStreaming.limit input (!right)] (0, ((0, []), none))
  let (_, buffered) := final
  finish (parameters task) buffered

private theorem probe_prefix (task : Task) (n : ℕ) :
    (probeStep task)^[n] (0, ((0, []), none)) =
      let (((input, right), _), capacity) := task
      (n, (ClassStreaming.records input (!right) n).foldl
        (feed (parameters task) capacity) ((0, []), none)) := by
  rcases task with ⟨⟨⟨input, right⟩, kept⟩, capacity⟩
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ClassStreaming.records_succ]
    dsimp only [probeStep]
    cases ClassStreaming.accepts input (!right) n <;> simp [List.foldl_append]

/-- The computed retained occurrence count determines capacity; no capacity advice is input. -/
def search (input : ClassStreaming.Input) : Option (ℕ × ℕ) :=
  let right := ClassStreaming.retainRight input
  let kept := ClassStreaming.retain input right
  let capacity := ClassStreaming.count input right + 1
  probe (((input, right), kept), capacity)

/-- Every live source batch is strictly below its computed smaller-class capacity. -/
theorem source_buffer_bound (input : ClassStreaming.Input) (n : ℕ) :
    let right := ClassStreaming.retainRight input
    let kept := ClassStreaming.retain input right
    let capacity := ClassStreaming.count input right + 1
    let task : Task := (((input, right), kept), capacity)
    let (_, ((_, batch), _)) := (probeStep task)^[n] (0, ((0, []), none))
    batch.length < capacity := by
  dsimp only
  rw [probe_prefix]
  dsimp only
  have h := fold_valid (parameters (((input, ClassStreaming.retainRight input),
    ClassStreaming.retain input (ClassStreaming.retainRight input)),
    ClassStreaming.count input (ClassStreaming.retainRight input) + 1)) (ClassStreaming.count input
    (ClassStreaming.retainRight input) + 1) (ClassStreaming.records input
      (!(ClassStreaming.retainRight input)) n) (by omega)
  exact h.1 ▸ h.2

private theorem probe_none (task : Task)
    (fits : let (((input, right), kept), _) := task
      let (halves, _) := input
      let ((width, _), _) := halves
      ∀ r ∈ kept ++ ClassStreaming.records input (!right) (ClassStreaming.limit input (!right)),
        r.1 < 2 ^ width) :
    probe task = none ↔
      let (((input, right), kept), _) := task
      ¬ Meets kept (ClassStreaming.records input (!right)
        (ClassStreaming.limit input (!right))) := by
  rcases task with ⟨⟨⟨input, right⟩, kept⟩, capacity⟩
  dsimp only [probe]
  rw [probe_prefix]
  dsimp only
  exact fold_none (parameters _) capacity _ fits

private theorem probe_sound (task : Task) (out : ℕ × ℕ) (hit : probe task = some out) :
    let (((input, right), kept), _) := task
    ∃ a ∈ kept, ∃ b ∈ ClassStreaming.records input (!right) (ClassStreaming.limit input (!right)),
      a.1 = b.1 ∧ out = if right then (b.2, a.2) else (a.2, b.2) := by
  rcases task with ⟨⟨⟨input, right⟩, kept⟩, capacity⟩
  dsimp only [probe] at hit
  rw [probe_prefix] at hit
  dsimp only at hit ⊢
  exact fold_sound (parameters _) capacity _ out hit

/-- The source-derived capacity covers the retained list, so full-batch sorting volume is
amortized linearly over emitted opposite occurrences. This is not a bit-time bound. -/
theorem source_recordWork (input : ClassStreaming.Input) (rows : List (ℕ × ℕ)) :
    let right := ClassStreaming.retainRight input
    let kept := ClassStreaming.retain input right
    recordWork (parameters (((input, right), kept), ClassStreaming.count input right + 1))
      (ClassStreaming.count input right + 1) ((0, []), none) rows ≤ 4 * rows.length := by
  apply recordWork_bound _ _ rows (by omega)
  dsimp only [parameters]
  rw [(ClassStreaming.retain_perm input _).length_eq, List.length_reverse,
    ← ClassStreaming.count_eq]
  omega

private theorem original_fits {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p g : ℕ)
    (right : Bool) :
    let input : ClassStreaming.Input :=
      (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))
    ∀ r ∈ ClassStreaming.retain input right ++
      ClassStreaming.records input (!right) (ClassStreaming.limit input (!right)), r.1 < 2 ^ m := by
  dsimp only
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [(ClassStreaming.retain_perm _ right).mem_iff, List.mem_reverse] at hr
    exact (ClassStreaming.records_fit as bs s p g right r hr).1
  · exact (ClassStreaming.records_fit as bs s p g (!right) r hr).1

/-- Batch probing preserves exhaustive selected-class misses for original fitting words. -/
theorem search_none {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p g : ℕ) :
    let input : ClassStreaming.Input :=
      (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))
    search input = none ↔ ClassStreaming.search input = none := by
  dsimp only
  unfold search ClassStreaming.search
  rw [probe_none _ (original_fits as bs s p g _), ClassStreaming.probe_none]
  rfl

/-- Every batched hit retains actual original-class witness provenance in either orientation. -/
theorem search_sound (input : ClassStreaming.Input) (out : ℕ × ℕ)
    (hit : search input = some out) :
    ∃ a ∈ ClassStreaming.records input false (ClassStreaming.limit input false),
      ∃ b ∈ ClassStreaming.records input true (ClassStreaming.limit input true),
        a.1 = b.1 ∧ out = (a.2, b.2) := by
  obtain ⟨a, ha, b, hb, hk, ho⟩ := probe_sound _ out hit
  rw [(ClassStreaming.retain_perm input _).mem_iff, List.mem_reverse] at ha
  cases h : ClassStreaming.retainRight input with
  | false => exact ⟨a, by simpa only [h] using ha, b,
      by simpa only [h, Bool.not_false] using hb, hk, by simpa [h] using ho⟩
  | true => exact ⟨b, by simpa only [h, Bool.not_true] using hb, a,
      by simpa only [h] using ha, hk.symm, by simpa [h] using ho⟩

/-- One class is fully released before the next class's buffers are initialized. -/
def allStep (input : SortedMeet.Input × ℕ) (state : ℕ × Option (ℕ × ℕ)) :
    ℕ × Option (ℕ × ℕ) :=
  let (halves, depth) := input
  let (g, found) := state
  (g + 1, found.orElse (fun _ => search (halves, (depth, g))))

/-- Fixed-size outer counter program; no unrolled list of class programs. -/
def allSearch (input : SortedMeet.Input × ℕ) : Option (ℕ × ℕ) :=
  let (_, depth) := input
  ((allStep input)^[2 ^ depth] (0, none)).2

private theorem all_none (input : SortedMeet.Input × ℕ) :
    allSearch input = none ↔ ∀ g < 2 ^ input.2, search (input.1, (input.2, g)) = none := by
  have h (n : ℕ) : ((allStep input)^[n] (0, none)).2 = none ↔
      ∀ g < n, search (input.1, (input.2, g)) = none := by
    rw [show allStep input = ClassStreaming.advance (fun g found =>
      found.orElse (fun _ => search (input.1, (input.2, g)))) from rfl, ClassStreaming.advance_eq]
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (_ <|> _) = none ↔ _
      rw [Option.orElse_eq_none, ih]
      constructor
      · rintro ⟨h, hn⟩ g hg
        rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hg | rfl
        · exact h g hg
        · exact hn
      · intro h
        exact ⟨fun g hg => h g (by omega), h n (by omega)⟩
  exact h _

private theorem all_sound (input : SortedMeet.Input × ℕ) (out : ℕ × ℕ)
    (hit : allSearch input = some out) :
    ∃ g < 2 ^ input.2, search (input.1, (input.2, g)) = some out := by
  have h (n : ℕ) (hit : ((allStep input)^[n] (0, none)).2 = some out) :
      ∃ g < n, search (input.1, (input.2, g)) = some out := by
    rw [show allStep input = ClassStreaming.advance (fun g found =>
      found.orElse (fun _ => search (input.1, (input.2, g)))) from rfl,
      ClassStreaming.advance_eq] at hit
    induction n with
    | zero => simp at hit
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hit
      change (_ <|> _) = some out at hit
      rcases (Option.orElse_eq_some _ _ _).mp hit with old | ⟨_, fresh⟩
      · obtain ⟨g, hg, hhit⟩ := ih old
        exact ⟨g, by omega, hhit⟩
      · exact ⟨n, by omega, fresh⟩
  exact h _ hit

/-- Decoding restores suffix operators to their original order. -/
def solve (input : SortedMeet.Input × ℕ) : Option (List Bool) :=
  let (halves, _) := input
  (allSearch input).map (SortedMeet.decodeWitness halves)

/-- The existing count-only balance prepass precedes all retained/sorted batches. -/
def run (input : Source.Input) : ℕ × Option (List Bool) :=
  let prepared := ClassStreaming.prepare input
  (ClassStreaming.balance prepared, solve prepared)

private theorem solve_none {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p : ℕ) :
    solve (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), p) = none ↔
      ¬ Solvable (as ++ bs) s 0 := by
  rw [solve, Option.map_eq_none_iff, all_none]
  simp only [search_none]
  exact (ClassStreaming.all_none
    (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), p)).symm.trans
      (ClassStreaming.allSearch_none as bs s p)

private theorem solve_sound {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p : ℕ)
    (ops : List Bool) (hit : solve (((m, s.toNat),
      (as.map BitVec.toNat, bs.map BitVec.toNat)), p) = some ops) :
    ops.length = (as ++ bs).length ∧ eval (ops.zip (as ++ bs)) s = 0 := by
  unfold solve at hit
  cases h : allSearch (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), p) with
  | none => simp [h] at hit
  | some out =>
    simp only [h, Option.map_some, Option.some.injEq] at hit
    obtain ⟨g, _, hs⟩ := all_sound _ out h
    obtain ⟨a, ha, b, hb, hk, ho⟩ := search_sound _ out hs
    have hf := (SortedQuarterMachine.correct as s).2.2 a |>.mp
      ((ClassStreaming.allRecords_mem _ _ _).mp ((ClassStreaming.mem_records _ _ _).mp ha).1)
    have hi := (SortedMeet.mem_inverse bs 0 b).mp
      ((ClassStreaming.allRecords_mem _ _ _).mp ((ClassStreaming.mem_records _ _ _).mp hb).1)
    subst ops
    rw [ho]
    constructor
    · simp [SortedMeet.decodeWitness]
    · simp only [SortedMeet.decodeWitness, List.length_map]
      rw [List.zip_append (by simp : (Native.Quarter.decode as.length a.2).length = as.length)]
      apply (eval_append_eq_iff _ _ _ _).mpr
      apply BitVec.eq_of_toNat_eq
      exact hf.2.symm.trans (hk.trans hi.2)

/-- Original-source exhaustive absence and sound witness output for all quarter residues. -/
theorem original_correct {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    let (_, result) := run (Source.ofWords p a tail)
    (result = none ↔ ¬ Solvable tail a 0) ∧
      ∀ ops, result = some ops → ops.length = tail.length ∧ eval (ops.zip tail) a = 0 := by
  have cut := Source.quarters_append tail
  constructor
  · simp only [ClassStreaming.prepare, SortedMeet.prepare_ofWords]
    rw [solve_none, cut]
  · intro ops hit
    simp only [ClassStreaming.prepare, SortedMeet.prepare_ofWords] at hit
    simpa only [cut] using solve_sound _ _ a _ ops hit


/-- Captured original class, orientation, retained records and binary capacity. -/
def taskEncoding : Task ↪ List Bool :=
  encPair (encPair (encPair ClassStreaming.encoding encBool)
    (encList RadixPartition.recordEncoding)) encNat

private def counterEncoding := encPair encNat stateEncoding

private noncomputable def parametersCertificate : NativeCertificate parameters
    taskEncoding parameterEncoding := by
  let original : NativeCertificate (id : Task → _) taskEncoding taskEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let task := original.fst.fst
  exact NativeCertificate.congr
    (task.fst.fst.fst.fst.prod (task.snd.prod original.fst.snd)) (fun _ => rfl)

private noncomputable def oppositeCertificate : NativeCertificate
    (fun q : Task => let (((input, right), _), _) := q; (input, !right))
    taskEncoding (encPair ClassStreaming.encoding encBool) := by
  let original : NativeCertificate (id : Task → _) taskEncoding taskEncoding :=
    .linear (.of_eq (fun _ => rfl))
  have hn : ComputableInPolyTime Bool.not encBool encBool := by fun_prop
  exact NativeCertificate.congr (original.fst.fst.fst.prod
    ((NativeCertificate.ofPolyTime hn).comp original.fst.fst.snd)) (fun _ => rfl)

private noncomputable def probeStepCertificate : NativeCertificate
    (fun q : Task × (ℕ × State) => probeStep q.1 q.2)
    (encPair taskEncoding counterEncoding) counterEncoding := by
  let ei := encPair taskEncoding counterEncoding
  let original : NativeCertificate (id : Task × (ℕ × State) → _) ei ei :=
    .linear (.of_eq (fun _ => rfl))
  let opposite := oppositeCertificate.comp original.fst
  let argument := opposite.prod original.snd.fst
  let accepted := (NativeCertificate.ofPolyTime ClassStreaming.accepts_polyTime).comp argument
  let row := (NativeCertificate.ofPolyTime ClassStreaming.row_polyTime).comp argument
  let parameter := parametersCertificate.comp original.fst
  let feedArguments := (parameter.prod original.fst.snd).prod (original.snd.snd.prod row)
  let fed := feedCertificate.comp feedArguments
  let updated := NativeCertificate.branch accepted fed original.snd.snd
  have hs : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let index := (NativeCertificate.ofPolyTime hs).comp original.snd.fst
  exact NativeCertificate.congr (index.prod updated) (fun _ => rfl)

/-- The producer evaluates original words directly into bounded batches. All array operations
are structural/linear or certified radix operations; scalar callbacks exclude retained arrays. -/
noncomputable def probeCertificate : NativeCertificate probe taskEncoding
    (encOption RadixPartition.recordEncoding) := by
  let original : NativeCertificate (id : Task → _) taskEncoding taskEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let clock := (NativeCertificate.ofPolyTime ClassStreaming.limit_polyTime).comp oppositeCertificate
  let initial := original.prod (NativeCertificate.const (em := counterEncoding)
    ((0 : ℕ), (((0 : ℕ), ([] : List (ℕ × ℕ))), (none : Option (ℕ × ℕ)))))
  let eb := encPair taskEncoding counterEncoding
  let state : NativeCertificate (id : Task × (ℕ × State) → _) eb eb :=
    .linear (.of_eq (fun _ => rfl))
  let body := state.fst.prod probeStepCertificate
  let loop := NativeCertificate.iterate clock initial body
  let final : NativeCertificate
      (fun task : Task => let (((input, right), _), _) := task
        ((probeStep task)^[ClassStreaming.limit input (!right)] (0, ((0, []), none))).2)
      taskEncoding stateEncoding := NativeCertificate.congr loop.snd.snd (fun task => by
        rcases task with ⟨⟨⟨input, right⟩, kept⟩, capacity⟩
        change ((fun q : Task × (ℕ × State) => (q.1, probeStep q.1 q.2))^[
          ClassStreaming.limit input (!right)] ((((input, right), kept), capacity),
            (0, ((0, []), none)))).2.2 = _
        rw [ClassStreaming.captured_iterate])
  exact NativeCertificate.congr
    (finishCertificate.comp (parametersCertificate.prod final)) (fun _ => rfl)


private noncomputable def collectStepCertificate : NativeCertificate
    (fun q : (ClassStreaming.Input × Bool) × (ℕ × List (ℕ × ℕ)) =>
      ClassStreaming.retainStep q.1.1 q.1.2 q.2)
    (encPair (encPair ClassStreaming.encoding encBool)
      (encPair encNat (encList RadixPartition.recordEncoding)))
    (encPair encNat (encList RadixPartition.recordEncoding)) := by
  let ep := encPair ClassStreaming.encoding encBool
  let es := encPair encNat (encList RadixPartition.recordEncoding)
  let ei := encPair ep es
  let original : NativeCertificate (id : (ClassStreaming.Input × Bool) × (ℕ × List (ℕ × ℕ)) → _)
      ei ei := .linear (.of_eq (fun _ => rfl))
  let argument := original.fst.prod original.snd.fst
  let accepted := (NativeCertificate.ofPolyTime ClassStreaming.accepts_polyTime).comp argument
  let row := (NativeCertificate.ofPolyTime ClassStreaming.row_polyTime).comp argument
  let inserted := (row.prod original.snd.snd).post
    ((ComputableInDegree.cons RadixPartition.recordEncoding).inO_one)
  let selected := NativeCertificate.branch accepted inserted original.snd.snd
  have hs : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let index := (NativeCertificate.ofPolyTime hs).comp original.snd.fst
  exact NativeCertificate.congr (index.prod selected) (fun _ => rfl)

/-- Retention reuses the proved counter semantics, with linear framed insertion instead of
running a polynomial callback on the complete growing retained list. -/
noncomputable def retainCertificate : NativeCertificate
    (fun q : ClassStreaming.Input × Bool => ClassStreaming.retain q.1 q.2)
    (encPair ClassStreaming.encoding encBool) (encList RadixPartition.recordEncoding) := by
  let ep := encPair ClassStreaming.encoding encBool
  let collected := ClassStreaming.loopCertificate ep (encList RadixPartition.recordEncoding)
    _ (fun q => ClassStreaming.retainStep q.1 q.2) []
    ClassStreaming.limit_polyTime collectStepCertificate
  have hw : ComputableInPolyTime (fun q : ClassStreaming.Input × Bool => q.1.1.1.1)
      ep encUnary := by
    dsimp only [ep, ClassStreaming.encoding, SortedMeet.encoding]; fun_prop
  let prepared := (NativeCertificate.ofPolyTime hw).prod collected
  exact NativeCertificate.congr (SortedMatch.sortCertificate.comp prepared) (fun _ => rfl)

/-- Computed orientation, retained class and computed capacity are materialized before probing. -/
noncomputable def searchCertificate : NativeCertificate search ClassStreaming.encoding
    (encOption RadixPartition.recordEncoding) := by
  let original : NativeCertificate (id : ClassStreaming.Input → _)
      ClassStreaming.encoding ClassStreaming.encoding := .linear (.of_eq (fun _ => rfl))
  let selected := original.prod ClassStreaming.orientationCertificate
  let kept := retainCertificate.comp selected
  have hs : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let capacity := (NativeCertificate.ofPolyTime hs).comp
    (ClassStreaming.countCertificate.comp selected)
  let prepared := (selected.prod kept).prod capacity
  exact NativeCertificate.congr (probeCertificate.comp prepared) (fun _ => rfl)

private def allEncoding := encPair SortedMeet.encoding encUnary
private def allStateEncoding := encPair encNat (encOption RadixPartition.recordEncoding)

private noncomputable def allStepCertificate : NativeCertificate
    (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => allStep q.1 q.2)
    (encPair allEncoding allStateEncoding) allStateEncoding := by
  let ei := encPair allEncoding allStateEncoding
  let original : NativeCertificate (id : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) → _)
      ei ei := .linear (.of_eq (fun _ => rfl))
  let found := original.snd.snd
  have hp : ComputableInPolyTime
      (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => (q.1.1, (q.1.2, q.2.1)))
      ei ClassStreaming.encoding := by
    dsimp only [ei, allEncoding, allStateEncoding, ClassStreaming.encoding]; fun_prop
  let fresh := searchCertificate.comp (NativeCertificate.ofPolyTime hp)
  let yes : NativeCertificate
      (fun q : ((SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ))) × (ℕ × ℕ) => some q.2)
      (encPair ei RadixPartition.recordEncoding) (encOption RadixPartition.recordEncoding) :=
    ((NativeCertificate.linear (.of_eq (fun _ => rfl))).snd).some
  let chosen := found.option fresh yes
  have hi : ComputableInPolyTime
      (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => q.2.1 + 1) ei encNat := by
    dsimp only [ei, allStateEncoding]; fun_prop
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime hi).prod chosen) (fun q => by
    dsimp only [allStep, id_eq, Function.comp_def]
    cases q.2.2 <;> rfl)

/-- Every batch and class is released by actual finite counter execution, with all transient
sort/buffer/input/output tapes present in the composed time and prefix-peak space profiles. -/
noncomputable def allCertificate : NativeCertificate allSearch
    (encPair SortedMeet.encoding encUnary) (encOption RadixPartition.recordEncoding) := by
  have hn : ComputableInPolyTime (fun q : SortedMeet.Input × ℕ => 2 ^ q.2)
      allEncoding encNat := by dsimp only [allEncoding]; fun_prop
  exact ClassStreaming.loopCertificate allEncoding (encOption RadixPartition.recordEncoding)
    _ allStep none hn allStepCertificate

private noncomputable def solveCertificate : NativeCertificate solve allEncoding
    (encOption encBits) := by
  let original : NativeCertificate (id : SortedMeet.Input × ℕ → _) allEncoding allEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let readback := NativeCertificate.ofPolyTime SortedMeet.readback_polyTime
  exact NativeCertificate.congr (readback.comp (original.fst.prod allCertificate)) (fun _ => rfl)

/-- The actual original-input balance/class/batch/witness machine. Earlier enumeration and
counter-state copying costs remain; no sharp global bit bound is inferred from batch volume. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding
    (encPair encNat (encOption encBits)) :=
  (ClassStreaming.balanceCertificate.prod solveCertificate).comp
    (NativeCertificate.ofPolyTime ClassStreaming.prepare_polyTime)

/-- One finite bit machine precedes every source parameter and original operand list. -/
theorem original_machine : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q)
    (machine : Turing.MultiTapeTM k Bool Q), ∀ {m : ℕ} (p : ℕ) (a : BitVec m)
      (tail : List (BitVec m)),
      machine.ComputesInTimeAndSpace (Source.encoding (Source.ofWords p a tail))
        (encPair encNat (encOption encBits) (run (Source.ofWords p a tail)))
        (c * (sourceCertificate.time (Source.ofWords p a tail) + 1))
        (c * (sourceCertificate.space (Source.ofWords p a tail) + 1)) ∧
      (let (_, result) := run (Source.ofWords p a tail);
        (result = none ↔ ¬ Solvable tail a 0) ∧
          ∀ ops, result = some ops → ops.length = tail.length ∧ eval (ops.zip tail) a = 0
      ) := by
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := sourceCertificate.computes
  exact ⟨c, k, Q, hQ, machine, fun p a tail => ⟨computes _, original_correct p a tail⟩⟩

end Cslib.Cryptanalysis.AddXNOR.BatchedAccess
