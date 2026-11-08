/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Counter-driven class retention and streamed opposite-side probing

Actual packed counters compute class sizes before retaining the smaller class.
The opposite side is evaluated one record at a time, and classes release their
retained list before advancing. Mathematical record lists below are observers;
no half-space list is an input to the executed counters.

This route reuses the generated-record and inverse semantics of `SortedMeet`.
It scans all packed words for each class and uses linear retained-list lookup.
Its actual machine profiles charge these repeated scans and polynomial callback
workspace. It is not the output-sensitive projected-quarter join of
[WangLvShenZhang2027], Lemma 8/Theorem 7 (PDF pp. 21–22), and does not yet
prove the sharp source time or peak-space asymptotics.


## Main definitions

* `count`, `retainRight`, `retain`: actual count passes and sorted smaller-class retention.
* `balance`, `allSearch`, `run`: count-only maximum prepass, class reuse and original-input output.

## Main results

* `count_eq`, `retained_length`, `retain_prefix`: exact occurrence counts and retaining prefixes.
* `global_retained_prefix`, `retaining_prefix_wire`: computed-count and physical wire bounds.
* `original_correct`, `original_machine`: original witness/miss and actual uniform bit execution.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.ClassStreaming
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Original halves, with projection depth and selected low-bit class. -/
abbrev Input := SortedMeet.Input × (ℕ × ℕ)

/-- Physical width/depth are unary; class and packed words are binary. -/
def encoding : Input ↪ List Bool := encPair SortedMeet.encoding (encPair encUnary encNat)

/-- Actual original-direction operands and endpoint for one side. -/
def sideInput (input : Input) (right : Bool) : SortedQuarterMachine.Input :=
  let ((width, seed), (left, suffix)) := input.1
  if right then SortedMeet.inverseInput ((width, 0), suffix) else ((width, seed), left)

/-- One full state and its packed word, computed directly from original operands. -/
def row (input : Input) (right : Bool) (u : ℕ) : ℕ × ℕ :=
  let source := input.1
  let parameters := source.1
  let width := parameters.1
  let r := SortedQuarterMachine.record (sideInput input right) u
  if right then SortedMeet.reflect width r else r

/-- Binary packed-counter limit; no enumerated list is constructed. -/
def limit (input : Input) (right : Bool) : ℕ := 2 ^ (sideInput input right).2.length

/-- The actual computed low-bit comparison. -/
def accepts (input : Input) (right : Bool) (u : ℕ) : Bool :=
  let parameters := input.2
  let depth := parameters.1
  let selectedClass := parameters.2
  decide ((row input right u).1 % 2 ^ depth = selectedClass)

/-- Semantic observer for a counter prefix; the machine does not build this range. -/
def records (input : Input) (right : Bool) (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range n).filter (accepts input right)).map (row input right)

private theorem records_succ (input : Input) (right : Bool) (n : ℕ) :
    records input right (n + 1) = records input right n ++
      if accepts input right n then [row input right n] else [] := by
  simp only [records, List.range_succ, List.filter_append, List.map_append]
  cases h : accepts input right n <;> simp [h]

private def advance {α : Type} (f : ℕ → α → α) (state : ℕ × α) : ℕ × α :=
  (state.1 + 1, f state.1 state.2)

private theorem advance_eq {α : Type} (f : ℕ → α → α) (init : α) (n : ℕ) :
    (advance f)^[n] (0, init) = (n, (List.range n).foldl (fun a i => f i a) init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, List.range_succ, List.foldl_append]
    rfl

/-- Count without collecting any states or witnesses. -/
def countStep (input : Input) (right : Bool) (state : ℕ × ℕ) : ℕ × ℕ :=
  advance (fun i count => count + if accepts input right i then 1 else 0) state

/-- The class count is computed by an actual binary-counter pass. -/
def count (input : Input) (right : Bool) : ℕ :=
  ((countStep input right)^[limit input right] (0, 0)).2

/-- The retaining pass emits only members of its selected class. -/
def retainStep (input : Input) (right : Bool) (state : ℕ × List (ℕ × ℕ)) :
    ℕ × List (ℕ × ℕ) :=
  advance (fun i rows => if accepts input right i then row input right i :: rows else rows) state

/-- Only this selected class is materialized, in reverse enumeration order. -/
def collect (input : Input) (right : Bool) : List (ℕ × ℕ) :=
  ((retainStep input right)^[limit input right] (0, [])).2

/-- The selected full-state class is sorted by the existing uniform radix machine. -/
def retain (input : Input) (right : Bool) : List (ℕ × ℕ) :=
  let source := input.1
  let parameters := source.1
  let width := parameters.1
  RadixSort.sort (width, collect input right)

private theorem count_prefix (input : Input) (right : Bool) (n : ℕ) :
    (countStep input right)^[n] (0, 0) = (n, (records input right n).length) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [countStep, advance, records, List.range_succ, List.filter_append,
      List.map_append, List.length_append, List.length_map]
    cases h : accepts input right n <;> simp [h]

/-- Computed counts are occurrence counts, including coincident full states. -/
theorem count_eq (input : Input) (right : Bool) :
    count input right = (records input right (limit input right)).length := by
  unfold count
  rw [count_prefix]

/-- Every retaining prefix is exactly the reversed actual class prefix. -/
theorem retain_prefix (input : Input) (right : Bool) (n : ℕ) :
    (retainStep input right)^[n] (0, []) = (n, (records input right n).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [retainStep, advance, records, List.range_succ, List.filter_append,
      List.map_append, List.reverse_append]
    cases h : accepts input right n <;> simp [h]

/-- Exact class retention, derived from execution rather than assumed memory validity. -/
theorem collect_eq (input : Input) (right : Bool) :
    collect input right = (records input right (limit input right)).reverse := by
  unfold collect
  rw [retain_prefix]

/-- Sorting the selected class preserves every occurrence and its packed witness. -/
theorem retain_perm (input : Input) (right : Bool) :
    (retain input right).Perm (records input right (limit input right)).reverse := by
  unfold retain
  rw [collect_eq]
  exact (RadixSort.prefix_invariants _ _).2

/-- Select orientation from both computed counts, with ties retaining the forward side. -/
def retainRight (input : Input) : Bool := decide (count input true < count input false)

/-- The actual retained list has the smaller occurrence count. -/
theorem retained_length (input : Input) :
    (retain input (retainRight input)).length = min (count input false) (count input true) := by
  rw [(retain_perm input _).length_eq, List.length_reverse, ← count_eq]
  unfold retainRight
  by_cases h : count input true < count input false <;> simp [h, Nat.min_def]

/-- Linear lookup against the one retained class; the opposite record is not collected. -/
def lookup (right : Bool) (kept : List (ℕ × ℕ)) (r : ℕ × ℕ) : Option (ℕ × ℕ) :=
  (kept.find? (fun a => decide (a.1 = r.1))).map
    (fun a => if right then (r.2, a.2) else (a.2, r.2))

/-- Probe one packed word, preserving the first hit. -/
def probeStep (input : Input) (right : Bool) (kept : List (ℕ × ℕ))
    (state : ℕ × Option (ℕ × ℕ)) : ℕ × Option (ℕ × ℕ) :=
  advance (fun i found => found.orElse (fun _ =>
    if accepts input (!right) i then lookup right kept (row input (!right) i) else none)) state

/-- The opposite side is streamed by a binary-counter loop. -/
def probe (input : Input) (right : Bool) (kept : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  ((probeStep input right kept)^[limit input (!right)] (0, none)).2

/-- Counts precede retention; the opposite full half space is never materialized. -/
def search (input : Input) : Option (ℕ × ℕ) :=
  let right := retainRight input
  let kept := retain input right
  probe input right kept

private theorem lookup_none (right : Bool) (kept : List (ℕ × ℕ)) (r : ℕ × ℕ) :
    lookup right kept r = none ↔ ¬ ∃ a ∈ kept, a.1 = r.1 := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  constructor
  · intro h ⟨a, ha, he⟩; exact h a ha he
  · intro h a ha he; exact h ⟨a, ha, he⟩

private theorem probe_none (input : Input) (right : Bool) (kept : List (ℕ × ℕ)) :
    probe input right kept = none ↔
      ¬ ∃ a ∈ kept, ∃ b ∈ records input (!right) (limit input (!right)), a.1 = b.1 := by
  have h (n : ℕ) (found : Option (ℕ × ℕ)) :
      ((probeStep input right kept)^[n] (0, found)).2 = none ↔
        found = none ∧ ¬ ∃ a ∈ kept, ∃ b ∈ records input (!right) n, a.1 = b.1 := by
    rw [show probeStep input right kept = advance (fun i found => found.orElse (fun _ =>
      if accepts input (!right) i then lookup right kept (row input (!right) i) else none))
        from rfl,
      advance_eq]
    induction n with
    | zero => simp [records]
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
      change ((_ <|> (if accepts input (!right) n then
        lookup right kept (row input (!right) n) else none)) = none) ↔ _
      rw [Option.orElse_eq_none, ih]
      rw [records_succ]
      cases accepts input (!right) n with
      | false => simp
      | true =>
        simp only [ite_true, List.mem_append, List.mem_singleton, or_and_right,
          exists_or, exists_eq_left, and_or_left, lookup_none]
        constructor
        · rintro ⟨⟨hf, hn⟩, hc⟩
          exact ⟨hf, fun h => h.elim hn hc⟩
        · rintro ⟨hf, hn⟩
          exact ⟨⟨hf, fun h => hn (.inl h)⟩, fun h => hn (.inr h)⟩
  exact (h _ none).trans (by simp)

/-- Exhaustive miss for the selected class, irrespective of the chosen smaller side. -/
theorem search_none (input : Input) : search input = none ↔
    ¬ ∃ a ∈ records input false (limit input false),
      ∃ b ∈ records input true (limit input true), a.1 = b.1 := by
  unfold search
  rw [probe_none]
  simp only [(retain_perm input _).mem_iff, List.mem_reverse]
  cases h : retainRight input <;> simp only [Bool.not_false, Bool.not_true]
  · constructor <;> intro hno hex
    · obtain ⟨a, ha, b, hb, he⟩ := hex
      exact hno ⟨b, hb, a, ha, he.symm⟩
    · obtain ⟨b, hb, a, ha, he⟩ := hex
      exact hno ⟨a, ha, b, hb, he.symm⟩


private theorem lookup_sound (right : Bool) (kept : List (ℕ × ℕ)) (r out : ℕ × ℕ)
    (hit : lookup right kept r = some out) :
    ∃ a ∈ kept, a.1 = r.1 ∧ out = if right then (r.2, a.2) else (a.2, r.2) := by
  unfold lookup at hit
  cases hf : kept.find? (fun a => decide (a.1 = r.1)) with
  | none => simp [hf] at hit
  | some a =>
    simp only [hf, Option.map_some, Option.some.injEq] at hit
    exact ⟨a, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, hit.symm⟩

private theorem probe_sound (input : Input) (right : Bool) (kept : List (ℕ × ℕ))
    (out : ℕ × ℕ) (hit : probe input right kept = some out) :
    ∃ a ∈ kept, ∃ b ∈ records input (!right) (limit input (!right)),
      a.1 = b.1 ∧ out = if right then (b.2, a.2) else (a.2, b.2) := by
  have h (n : ℕ) (out : ℕ × ℕ)
      (hit : ((probeStep input right kept)^[n] (0, none)).2 = some out) :
      ∃ a ∈ kept, ∃ b ∈ records input (!right) n,
        a.1 = b.1 ∧ out = if right then (b.2, a.2) else (a.2, b.2) := by
    rw [show probeStep input right kept = advance (fun i found => found.orElse (fun _ =>
      if accepts input (!right) i then lookup right kept (row input (!right) i) else none))
        from rfl,
      advance_eq] at hit
    induction n with
    | zero => simp at hit
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hit
      change (_ <|> (if accepts input (!right) n then
        lookup right kept (row input (!right) n) else none)) = some out at hit
      rcases (Option.orElse_eq_some _ _ _).mp hit with old | ⟨_, fresh⟩
      · obtain ⟨a, ha, b, hb, hk, ho⟩ := ih old
        exact ⟨a, ha, b, by rw [records_succ]; exact List.mem_append_left _ hb, hk, ho⟩
      · cases ha : accepts input (!right) n with
        | false => simp [ha] at fresh
        | true =>
          simp only [ha, ite_true] at fresh
          obtain ⟨a, ha', hk, ho⟩ := lookup_sound right kept _ out fresh
          exact ⟨a, ha', row input (!right) n, by simp [records_succ, ha], hk, ho⟩
  exact h _ out hit

/-- A returned pair has actual forward and inverse occurrences in the selected class. -/
theorem search_sound (input : Input) (out : ℕ × ℕ) (hit : search input = some out) :
    ∃ a ∈ records input false (limit input false),
      ∃ b ∈ records input true (limit input true), a.1 = b.1 ∧ out = (a.2, b.2) := by
  obtain ⟨a, ha, b, hb, hk, ho⟩ := probe_sound input (retainRight input) _ out hit
  rw [(retain_perm input _).mem_iff, List.mem_reverse] at ha
  cases h : retainRight input with
  | false => exact ⟨a, by simpa only [h] using ha, b,
      by simpa only [h, Bool.not_false] using hb, hk, by simpa [h] using ho⟩
  | true => exact ⟨b, by simpa only [h, Bool.not_true] using hb, a,
      by simpa only [h] using ha, hk.symm, by simpa [h] using ho⟩

/-- Unfiltered records are a semantic observer only, never an executed half-space array. -/
def allRecords (input : Input) (right : Bool) : List (ℕ × ℕ) :=
  (List.range (limit input right)).map (row input right)

/-- The streaming observer is the selected low-bit class of the actual generated records. -/
theorem mem_records (input : Input) (right : Bool) (r : ℕ × ℕ) :
    let parameters := input.2
    let depth := parameters.1
    let selectedClass := parameters.2
    r ∈ records input right (limit input right) ↔
      r ∈ allRecords input right ∧ r.1 % 2 ^ depth = selectedClass := by
  dsimp only
  simp only [records, allRecords, List.mem_map, List.mem_filter, List.mem_range, accepts,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u, ⟨hu, hg⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, hg⟩
  · rintro ⟨⟨u, hu, rfl⟩, hg⟩
    exact ⟨u, ⟨hu, hg⟩, rfl⟩

/-- Reuse the actual sorted generator's permutation, with full inverse payload provenance. -/
theorem allRecords_mem (input : Input) (right : Bool) (r : ℕ × ℕ) :
    let source := input.1
    let parameters := source.1
    let width := parameters.1
    let halves := source.2
    let forward := halves.1
    let backward := halves.2
    r ∈ allRecords input right ↔ r ∈
      if right then SortedMeet.inverse ((width, 0), backward)
      else SortedQuarterMachine.run (parameters, forward) := by
  dsimp only
  have h (q : SortedQuarterMachine.Input) (r : ℕ × ℕ) :
      r ∈ SortedQuarterMachine.run q ↔
        r ∈ (List.range (2 ^ q.2.length)).map (SortedQuarterMachine.record q) := by
    exact (RadixSort.prefix_invariants _ _).2.mem_iff.trans (by
      rw [SortedQuarterMachine.indices_eq_range])
  cases right with
  | false => exact (h _ _).symm
  | true =>
    simp only [allRecords, limit, row, sideInput, ite_true, SortedMeet.inverse, List.mem_map]
    constructor
    · rintro ⟨u, hu, he⟩
      exact ⟨SortedQuarterMachine.record _ u,
        (h _ _).mpr (List.mem_map.mpr ⟨u, hu, rfl⟩), he⟩
    · rintro ⟨a, ha, he⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ((h _ _).mp ha)
      exact ⟨u, hu, he⟩

/-- One class is executed and released before the next; only a hit survives. -/
def allStep (input : SortedMeet.Input × ℕ) (state : ℕ × Option (ℕ × ℕ)) :
    ℕ × Option (ℕ × ℕ) :=
  advance (fun g found => found.orElse (fun _ => search (input.1, (input.2, g)))) state

/-- Uniform outer binary class counter, with no list of class programs. -/
def allSearch (input : SortedMeet.Input × ℕ) : Option (ℕ × ℕ) :=
  ((allStep input)^[2 ^ input.2] (0, none)).2

private theorem all_none (input : SortedMeet.Input × ℕ) :
    allSearch input = none ↔ ∀ g < 2 ^ input.2, search (input.1, (input.2, g)) = none := by
  have h (n : ℕ) : ((allStep input)^[n] (0, none)).2 = none ↔
      ∀ g < n, search (input.1, (input.2, g)) = none := by
    rw [show allStep input = advance (fun g found =>
      found.orElse (fun _ => search (input.1, (input.2, g)))) from rfl, advance_eq]
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
    rw [show allStep input = advance (fun g found =>
      found.orElse (fun _ => search (input.1, (input.2, g)))) from rfl, advance_eq] at hit
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

/-- Exhaustive original-half miss, with the actual low class chosen for any proposed meeting. -/
theorem allSearch_none {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p : ℕ) :
    allSearch (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), p) = none ↔
      ¬ Solvable (as ++ bs) s 0 := by
  rw [all_none, ← SortedMeet.meeting_iff as bs s]
  constructor
  · intro h ⟨a, ha, b, hb, he⟩
    let g := a.1 % 2 ^ p
    have hg : g < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
    apply (search_none _).mp (h g hg)
    exact ⟨a, (mem_records _ _ _).mpr ⟨(allRecords_mem _ _ _).mpr ha, rfl⟩,
      b, (mem_records _ _ _).mpr ⟨(allRecords_mem _ _ _).mpr hb, by rw [← he]⟩, he⟩
  · intro h g _
    apply (search_none _).mpr
    rintro ⟨a, ha, b, hb, he⟩
    exact h ⟨a, (allRecords_mem _ _ _).mp ((mem_records _ _ _).mp ha).1,
      b, (allRecords_mem _ _ _).mp ((mem_records _ _ _).mp hb).1, he⟩

/-- Every all-class hit is also a hit of the reviewed full-state batch matcher. -/
theorem allSearch_sound (input : SortedMeet.Input × ℕ) (out : ℕ × ℕ)
    (hit : allSearch input = some out) :
    let source := input.1
    let parameters := source.1
    let width := parameters.1
    let halves := source.2
    let forward := halves.1
    let backward := halves.2
    ∃ a ∈ SortedQuarterMachine.run (parameters, forward),
      ∃ b ∈ SortedMeet.inverse ((width, 0), backward),
        a.1 = b.1 ∧ out = (a.2, b.2) := by
  dsimp only
  obtain ⟨g, _, hs⟩ := all_sound input out hit
  obtain ⟨a, ha, b, hb, he, ho⟩ := search_sound _ out hs
  exact ⟨a, (allRecords_mem _ _ _).mp ((mem_records _ _ _).mp ha).1,
    b, (allRecords_mem _ _ _).mp ((mem_records _ _ _).mp hb).1, he, ho⟩


/-- No retaining prefix exceeds the computed smaller class occurrence count. This bounds the
retained list, separately from internal machine workspace and encoded temporaries. -/
theorem retained_prefix_length (input : Input) (j : ℕ)
    (hj : j ≤ limit input (retainRight input)) :
    (((retainStep input (retainRight input))^[j] (0, [])).2).length ≤
      min (count input false) (count input true) := by
  rw [retain_prefix, List.length_reverse, ← retained_length,
    (retain_perm input _).length_eq, List.length_reverse]
  exact (((List.range_sublist.mpr hj).filter _).map _).length_le

private def recordEncoding : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat
private def taskEncoding : (Input × Bool) ↪ List Bool := encPair encoding encBool

private theorem sideInput_polyTime : ComputableInPolyTime
    (fun q : Input × Bool => sideInput q.1 q.2) taskEncoding SortedQuarterMachine.encoding := by
  unfold sideInput SortedMeet.inverseInput
  dsimp only [taskEncoding, encoding, SortedMeet.encoding, SortedQuarterMachine.encoding]
  apply ComputableInPolyTime.of_tidy
  fun_prop

private theorem row_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × ℕ => row q.1.1 q.1.2 q.2)
    (encPair taskEncoding encNat) recordEncoding := by
  have hi := sideInput_polyTime.comp (ComputableInPolyTime.fst taskEncoding encNat)
  have hr := SortedQuarterMachine.record_value_polyTime.comp
    (hi.prod (ComputableInPolyTime.snd taskEncoding encNat))
  have hr' : ComputableInPolyTime
      (fun q : (Input × Bool) × ℕ => SortedQuarterMachine.record
        (sideInput q.1.1 q.1.2) q.2) (encPair taskEncoding encNat) recordEncoding := hr
  have hrT := hr'.tidy
  have hw : ComputableTidilyInPolyTime (fun q : (Input × Bool) × ℕ => q.1.1.1.1.1)
      (encPair taskEncoding encNat) encUnary := by
    dsimp only [taskEncoding, encoding, SortedMeet.encoding]; fun_prop
  have hb : ComputableTidilyInPolyTime (fun q : (Input × Bool) × ℕ => q.1.2)
      (encPair taskEncoding encNat) encBool := by dsimp only [taskEncoding]; fun_prop
  have hp := ComputableTidilyInPolyTime.binary_two_pow.comp hw
  have hm := ComputableTidilyInPolyTime.binary_sub' hp
    (ComputableTidilyInPolyTime.const (encMid := encNat) 1)
  have hk := ComputableTidilyInPolyTime.binary_sub' hm
    ((ComputableTidilyInPolyTime.fst encNat encNat).comp hrT)
  exact ComputableInPolyTime.of_tidy
    (hb.cond (hk.prod ((ComputableTidilyInPolyTime.snd encNat encNat).comp hrT)) hrT)

private theorem accepts_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × ℕ => accepts q.1.1 q.1.2 q.2)
    (encPair taskEncoding encNat) encBool := by
  have hr := row_polyTime.tidy
  have hd : ComputableTidilyInPolyTime (fun q : (Input × Bool) × ℕ => q.1.1.2.1)
      (encPair taskEncoding encNat) encUnary := by
    dsimp only [taskEncoding, encoding]; fun_prop
  have hg : ComputableTidilyInPolyTime (fun q : (Input × Bool) × ℕ => q.1.1.2.2)
      (encPair taskEncoding encNat) encNat := by
    dsimp only [taskEncoding, encoding]; fun_prop
  have hp := ComputableTidilyInPolyTime.binary_two_pow.comp hd
  have hm := ComputableTidilyInPolyTime.binary_mod'
    ((ComputableTidilyInPolyTime.fst encNat encNat).comp hr) hp
  exact ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.decide_eq' (encB := encNat) hm hg)

private theorem limit_polyTime : ComputableInPolyTime
    (fun q : Input × Bool => limit q.1 q.2) taskEncoding encNat := by
  have len := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.length_list encNat).comp
      ((ComputableTidilyInPolyTime.snd (encPair encUnary encNat) (encList encNat)).comp
        sideInput_polyTime.tidy))
  exact ComputableInPolyTime.binary_two_pow.comp len

private theorem captured_iterate {π α : Type} (step : π → α → α) (p : π) (a : α) (n : ℕ) :
    (fun q : π × α => (q.1, step q.1 q.2))^[n] (p, a) = (p, (step p)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']

private noncomputable def loopCertificate {π α : Type} (encP : π ↪ List Bool)
    (encA : α ↪ List Bool) (n : π → ℕ) (step : π → (ℕ × α) → ℕ × α) (init : α)
    (hn : ComputableInPolyTime n encP encNat)
    (hs : NativeCertificate (fun q : π × (ℕ × α) => step q.1 q.2)
      (encPair encP (encPair encNat encA)) (encPair encNat encA)) :
    NativeCertificate (fun p => ((step p)^[n p] (0, init)).2) encP encA := by
  let es := encPair encNat encA
  let eb := encPair encP es
  let original : NativeCertificate (id : π → _) encP encP := .linear (.of_eq (fun _ => rfl))
  let state : NativeCertificate (id : π × (ℕ × α) → _) eb eb := .linear (.of_eq (fun _ => rfl))
  let body := state.fst.prod hs
  let initial := original.prod (NativeCertificate.const (em := es) (0, init))
  let clock := NativeCertificate.ofPolyTime hn
  let loop := NativeCertificate.iterate clock initial body
  exact NativeCertificate.congr loop.snd.snd (fun p => by
    change ((fun q : π × (ℕ × α) => (q.1, step q.1 q.2))^[n p] (p, (0, init))).2.2 = _
    rw [captured_iterate])

private theorem countStep_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × (ℕ × ℕ) => countStep q.1.1 q.1.2 q.2)
    (encPair taskEncoding (encPair encNat encNat)) (encPair encNat encNat) := by
  have ha := accepts_polyTime.tidy.comp
    ((ComputableTidilyInPolyTime.fst taskEncoding (encPair encNat encNat)).prod
      ((ComputableTidilyInPolyTime.fst encNat encNat).comp
        (ComputableTidilyInPolyTime.snd taskEncoding (encPair encNat encNat))))
  unfold countStep advance
  apply ComputableInPolyTime.of_tidy
  fun_prop

private theorem retainStep_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × (ℕ × List (ℕ × ℕ)) => retainStep q.1.1 q.1.2 q.2)
    (encPair taskEncoding (encPair encNat (encList recordEncoding)))
    (encPair encNat (encList recordEncoding)) := by
  have arg := (ComputableTidilyInPolyTime.fst taskEncoding
    (encPair encNat (encList recordEncoding))).prod
    ((ComputableTidilyInPolyTime.fst encNat (encList recordEncoding)).comp
      (ComputableTidilyInPolyTime.snd taskEncoding (encPair encNat (encList recordEncoding))))
  have ha := accepts_polyTime.tidy.comp arg
  have hr := row_polyTime.tidy.comp arg
  unfold retainStep advance
  apply ComputableInPolyTime.of_tidy
  fun_prop

/-- Count-pass certificates retain a binary count, not a class array. -/
noncomputable def countCertificate : NativeCertificate
    (fun q : Input × Bool => count q.1 q.2) (encPair encoding encBool) encNat :=
  loopCertificate taskEncoding encNat _ (fun q => countStep q.1 q.2) 0
    limit_polyTime (NativeCertificate.ofPolyTime countStep_polyTime)

/-- The retaining loop charges all callback work, maximum encoded state and binary control.
Polynomial callback workspace is not replaced by the retained-list length theorem. -/
private noncomputable def collectCertificate : NativeCertificate
    (fun q : Input × Bool => collect q.1 q.2)
    (encPair encoding encBool) (encList (encPair encNat encNat)) :=
  loopCertificate taskEncoding (encList recordEncoding) _ (fun q => retainStep q.1 q.2) []
    limit_polyTime (NativeCertificate.ofPolyTime retainStep_polyTime)


/-- Actual selected-class sorting charges input, output and sort callback temporaries. -/
noncomputable def retainCertificate : NativeCertificate
    (fun q : Input × Bool => retain q.1 q.2)
    (encPair encoding encBool) (encList (encPair encNat encNat)) := by
  have hw : ComputableInPolyTime (fun q : Input × Bool => q.1.1.1.1)
      taskEncoding encUnary := by
    dsimp only [taskEncoding, encoding, SortedMeet.encoding]; fun_prop
  let source := (NativeCertificate.ofPolyTime hw).prod collectCertificate
  exact NativeCertificate.congr (SortedMatch.sortCertificate.comp source) (fun _ => rfl)

private theorem lookup_polyTime : ComputableInPolyTime
    (fun q : (Bool × List (ℕ × ℕ)) × (ℕ × ℕ) => lookup q.1.1 q.1.2 q.2)
    (encPair (encPair encBool (encList recordEncoding)) recordEncoding)
    (encOption recordEncoding) := by
  let ei := encPair (encPair encBool (encList recordEncoding)) recordEncoding
  have hl : ComputableTidilyInPolyTime
      (fun q : (Bool × List (ℕ × ℕ)) × (ℕ × ℕ) => q.1.2) ei (encList recordEncoding) := by
    dsimp only [ei]; fun_prop
  have ht : ComputableTidilyInPolyTime
      (fun q : ((Bool × List (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) =>
        decide (q.2.1 = q.1.2.1)) (encPair ei recordEncoding) encBool := by
    dsimp only [ei, recordEncoding]; fun_prop
  have hf := hl.findWithInput (test := fun q a => decide (a.1 = q.2.1)) ht
  have body : ComputableTidilyInPolyTime
      (fun q : ((Bool × List (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) =>
        some (if q.1.1.1 then (q.1.2.2, q.2.2) else (q.2.2, q.1.2.2)))
      (encPair ei recordEncoding) (encOption recordEncoding) := by
    dsimp only [ei, recordEncoding]; fun_prop
  have h := hf.optionElimWithInput
    (body := fun q a => some (if q.1.1 then (q.2.2, a.2) else (a.2, q.2.2)))
    (ComputableTidilyInPolyTime.const none) body
  convert ComputableInPolyTime.of_tidy h using 1
  funext q
  dsimp only [lookup]
  cases (q.1.2.find? (fun a => decide (a.1 = q.2.1))) <;> rfl

private def probeEncoding := encPair taskEncoding (encList recordEncoding)
private def probeStateEncoding := encPair encNat (encOption recordEncoding)

private theorem probeStep_polyTime : ComputableInPolyTime
    (fun q : ((Input × Bool) × List (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ)) =>
      probeStep q.1.1.1 q.1.1.2 q.1.2 q.2)
    (encPair probeEncoding probeStateEncoding) probeStateEncoding := by
  let ei := encPair probeEncoding probeStateEncoding
  have arg : ComputableTidilyInPolyTime
      (fun q : ((Input × Bool) × List (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ)) =>
        ((q.1.1.1, !q.1.1.2), q.2.1)) ei (encPair taskEncoding encNat) := by
    dsimp only [ei, probeEncoding, probeStateEncoding, taskEncoding]; fun_prop
  have ha := accepts_polyTime.tidy.comp arg
  have hr := row_polyTime.tidy.comp arg
  have hpar : ComputableTidilyInPolyTime
      (fun q : ((Input × Bool) × List (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ)) =>
        (q.1.1.2, q.1.2)) ei (encPair encBool (encList recordEncoding)) := by
    dsimp only [ei, probeEncoding, taskEncoding]; fun_prop
  have hl := lookup_polyTime.tidy.comp (hpar.prod hr)
  have fresh := ha.cond hl (ComputableTidilyInPolyTime.const none)
  have found : ComputableTidilyInPolyTime
      (fun q : ((Input × Bool) × List (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ)) => q.2.2)
      ei (encOption recordEncoding) := by dsimp only [ei, probeStateEncoding]; fun_prop
  have hi : ComputableTidilyInPolyTime
      (fun q : ((Input × Bool) × List (ℕ × ℕ)) × (ℕ × Option (ℕ × ℕ)) => q.2.1 + 1)
      ei encNat := by dsimp only [ei, probeStateEncoding]; fun_prop
  have hc := ComputableInPolyTime.of_tidy (hi.prod (found.optionIsSome.cond found fresh))
  convert hc using 1
  · funext q
    dsimp only [probeStep, advance, Function.comp_def]
    cases q.2.2 <;> rfl
  · rfl

/-- Opposite packed words are evaluated singly; the retained list is captured and charged. -/
noncomputable def probeCertificate : NativeCertificate
    (fun q : (Input × Bool) × List (ℕ × ℕ) => probe q.1.1 q.1.2 q.2)
    (encPair (encPair encoding encBool) (encList (encPair encNat encNat)))
    (encOption (encPair encNat encNat)) := by
  have hn : ComputableInPolyTime
      (fun q : (Input × Bool) × List (ℕ × ℕ) => limit q.1.1 (!q.1.2)) probeEncoding encNat := by
    have h : ComputableInPolyTime
        (fun q : (Input × Bool) × List (ℕ × ℕ) => (q.1.1, !q.1.2))
        probeEncoding taskEncoding := by
      dsimp only [probeEncoding, taskEncoding]; fun_prop
    exact limit_polyTime.comp h
  exact loopCertificate probeEncoding (encOption recordEncoding) _
    (fun q => probeStep q.1.1 q.1.2 q.2) none hn (NativeCertificate.ofPolyTime probeStep_polyTime)

/-- Both actual counters run before the retained side is chosen. -/
noncomputable def orientationCertificate : NativeCertificate retainRight encoding encBool := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let forward := countCertificate.comp
    (original.prod (NativeCertificate.const (em := encBool) false))
  let backward := countCertificate.comp
    (original.prod (NativeCertificate.const (em := encBool) true))
  have cmp : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.1 < q.2))
      (encPair encNat encNat) encBool := by fun_prop
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime cmp).comp (backward.prod forward))
    (fun _ => rfl)

/-- Count, retain one class, then stream/probe its opposite. No half-space producer is composed. -/
noncomputable def searchCertificate : NativeCertificate search encoding
    (encOption (encPair encNat encNat)) := by
  let original : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let selected := original.prod orientationCertificate
  let kept := retainCertificate.comp selected
  exact NativeCertificate.congr (probeCertificate.comp (selected.prod kept)) (fun _ => rfl)

private def allEncoding := encPair SortedMeet.encoding encUnary

private noncomputable def allStepCertificate : NativeCertificate
    (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => allStep q.1 q.2)
    (encPair allEncoding probeStateEncoding) probeStateEncoding := by
  let ei := encPair allEncoding probeStateEncoding
  let original : NativeCertificate (id : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) → _)
      ei ei := .linear (.of_eq (fun _ => rfl))
  let found := original.snd.snd
  have hparam : ComputableInPolyTime
      (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => (q.1.1, (q.1.2, q.2.1)))
      ei encoding := by dsimp only [ei, allEncoding, probeStateEncoding, encoding]; fun_prop
  let fresh := searchCertificate.comp (NativeCertificate.ofPolyTime hparam)
  let yes : NativeCertificate
      (fun q : ((SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ))) × (ℕ × ℕ) => some q.2)
      (encPair ei recordEncoding) (encOption recordEncoding) :=
    ((NativeCertificate.linear (.of_eq (fun _ => rfl))).snd).some
  let chosen := found.option fresh yes
  have hi : ComputableInPolyTime
      (fun q : (SortedMeet.Input × ℕ) × (ℕ × Option (ℕ × ℕ)) => q.2.1 + 1) ei encNat := by
    dsimp only [ei, probeStateEncoding]; fun_prop
  let result := (NativeCertificate.ofPolyTime hi).prod chosen
  exact NativeCertificate.congr result (fun q => by
    dsimp only [allStep, advance, id_eq, Function.comp_def]
    cases q.2.2 <;> rfl)

/-- The outer counter charges maxima over actual class executions, including all temporaries.
The previous class's list is absent from its output; only counter/input/hit cross classes. -/
noncomputable def allCertificate : NativeCertificate allSearch
    (encPair SortedMeet.encoding encUnary) (encOption (encPair encNat encNat)) := by
  have hn : ComputableInPolyTime (fun q : SortedMeet.Input × ℕ => 2 ^ q.2)
      allEncoding encNat := by dsimp only [allEncoding]; fun_prop
  exact loopCertificate allEncoding (encOption recordEncoding) _ allStep none hn allStepCertificate


/-- A count-only prepass computes the maximum smaller-class size before any class is retained. -/
def balanceStep (input : SortedMeet.Input × ℕ) (state : ℕ × ℕ) : ℕ × ℕ :=
  advance (fun g best => max best (min (count (input.1, (input.2, g)) false)
    (count (input.1, (input.2, g)) true))) state

/-- Actual computed maximum; no class-size or balance advice is supplied. -/
def balance (input : SortedMeet.Input × ℕ) : ℕ :=
  ((balanceStep input)^[2 ^ input.2] (0, 0)).2

private theorem balance_succ (input : SortedMeet.Input × ℕ) (n : ℕ) :
    (balanceStep input)^[n + 1] (0, 0) =
      (n + 1, max (((balanceStep input)^[n] (0, 0)).2)
        (min (count (input.1, (input.2, n)) false) (count (input.1, (input.2, n)) true))) := by
  have hi : ((balanceStep input)^[n] (0, 0)).1 = n := by
    unfold balanceStep
    rw [advance_eq]
  rw [Function.iterate_succ_apply']
  simp only [balanceStep, advance, hi]

/-- Every actual smaller class is bounded by the computed maximum. -/
theorem class_le_balance (input : SortedMeet.Input × ℕ) (g : ℕ) (hg : g < 2 ^ input.2) :
    min (count (input.1, (input.2, g)) false) (count (input.1, (input.2, g)) true) ≤
      balance input := by
  have h (n : ℕ) (g : ℕ) (hg : g < n) :
      min (count (input.1, (input.2, g)) false) (count (input.1, (input.2, g)) true) ≤
        ((balanceStep input)^[n] (0, 0)).2 := by
    induction n with
    | zero => omega
    | succ n ih =>
      rw [balance_succ]
      by_cases hj : g < n
      · exact (ih hj).trans (le_max_left _ _)
      · have he : g = n := by omega
        subst g
        exact le_max_right _ _
  exact h _ g hg

/-- The prepass computes exactly the maximum of the smaller occurrence counts. -/
theorem balance_eq (input : SortedMeet.Input × ℕ) : balance input =
    listMax (fun g => min (count (input.1, (input.2, g)) false)
      (count (input.1, (input.2, g)) true)) (List.range (2 ^ input.2)) := by
  apply Nat.le_antisymm
  · have h (n : ℕ) (b : ℕ) (hb : ∀ g < n,
        min (count (input.1, (input.2, g)) false) (count (input.1, (input.2, g)) true) ≤ b) :
        ((balanceStep input)^[n] (0, 0)).2 ≤ b := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        rw [balance_succ]
        exact max_le (ih fun g hg => hb g (by omega)) (hb n (by omega))
    exact h _ _ (fun g hg => le_listMax (f := fun g =>
      min (count (input.1, (input.2, g)) false) (count (input.1, (input.2, g)) true))
      (List.mem_range.mpr hg))
  · exact listMax_le (fun g hg => class_le_balance input g (List.mem_range.mp hg))

/-- Every retained prefix of every visited class is bounded by the actually computed balance.
This is a list-occurrence bound, not a bound on auxiliary multitape workspace. -/
theorem global_retained_prefix (input : SortedMeet.Input × ℕ) (g : ℕ)
    (hg : g < 2 ^ input.2) (j : ℕ)
    (hj : j ≤ limit (input.1, (input.2, g)) (retainRight (input.1, (input.2, g)))) :
    (((retainStep (input.1, (input.2, g)) (retainRight (input.1, (input.2, g))))^[j]
      (0, [])).2).length ≤ balance input :=
  (retained_prefix_length _ j hj).trans (class_le_balance input g hg)

private noncomputable def balanceStepCertificate : NativeCertificate
    (fun q : (SortedMeet.Input × ℕ) × (ℕ × ℕ) => balanceStep q.1 q.2)
    (encPair allEncoding (encPair encNat encNat)) (encPair encNat encNat) := by
  let ei := encPair allEncoding (encPair encNat encNat)
  have hp : ComputableInPolyTime
      (fun q : (SortedMeet.Input × ℕ) × (ℕ × ℕ) => (q.1.1, (q.1.2, q.2.1)))
      ei encoding := by dsimp only [ei, allEncoding, encoding]; fun_prop
  let original : NativeCertificate (id : (SortedMeet.Input × ℕ) × (ℕ × ℕ) → _)
      ei ei := .linear (.of_eq (fun _ => rfl))
  let parameter := NativeCertificate.ofPolyTime hp
  let cf := countCertificate.comp (parameter.prod (NativeCertificate.const (em := encBool) false))
  let cb := countCertificate.comp (parameter.prod (NativeCertificate.const (em := encBool) true))
  have hc : ComputableInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      (q.1.1 + 1, max q.1.2 (min q.2.1 q.2.2)))
      (encPair (encPair encNat encNat) (encPair encNat encNat)) (encPair encNat encNat) := by
    let er := encPair (encPair encNat encNat) (encPair encNat encNat)
    have hf : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.1)
        er encNat := by dsimp only [er]; fun_prop
    have hb : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.2.2)
        er encNat := by dsimp only [er]; fun_prop
    have hp : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.2)
        er encNat := by dsimp only [er]; fun_prop
    have hi : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × (ℕ × ℕ) => q.1.1 + 1)
        er encNat := by dsimp only [er]; fun_prop
    have hmin := (ComputableTidilyInPolyTime.binary_le' hf hb).cond hf hb
    have hmax := (ComputableTidilyInPolyTime.binary_le' hp hmin).cond hmin hp
    simpa only [Nat.min_def, Nat.max_def, decide_eq_true_eq] using
      ComputableInPolyTime.of_tidy (hi.prod hmax)
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime hc).comp
    (original.snd.prod (cf.prod cb))) (fun _ => rfl)

/-- The global balance prepass uses only packed counters/counts, with all their tape costs. -/
noncomputable def balanceCertificate : NativeCertificate balance
    (encPair SortedMeet.encoding encUnary) encNat := by
  have hn : ComputableInPolyTime (fun q : SortedMeet.Input × ℕ => 2 ^ q.2)
      allEncoding encNat := by dsimp only [allEncoding]; fun_prop
  exact loopCertificate allEncoding encNat _ balanceStep 0 hn balanceStepCertificate

/-- Decode the streamed hit to original-order operators. -/
def solve (input : SortedMeet.Input × ℕ) : Option (List Bool) :=
  (allSearch input).map (SortedMeet.decodeWitness input.1)

/-- Original cut/seed/zero target and computed capped projection depth. -/
def prepare (input : Source.Input) : SortedMeet.Input × ℕ :=
  let source := Source.prepare input
  let endpoints := source.1
  let parameters := endpoints.1
  let depth := parameters.2
  (SortedMeet.prepare input, depth)

/-- The count-only balance prepass precedes all retention; output includes its computed value. -/
def run (input : Source.Input) : ℕ × Option (List Bool) :=
  let prepared := prepare input
  (balance prepared, solve prepared)

/-- A streamed original-half hit decodes to a full original-order solution. -/
theorem solve_sound {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p : ℕ)
    (ops : List Bool) (hit : solve (((m, s.toNat),
      (as.map BitVec.toNat, bs.map BitVec.toNat)), p) = some ops) :
    ops.length = (as ++ bs).length ∧ eval (ops.zip (as ++ bs)) s = 0 := by
  unfold solve at hit
  cases h : allSearch (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), p) with
  | none => simp [h] at hit
  | some out =>
    simp only [h, Option.map_some, Option.some.injEq] at hit
    obtain ⟨a, ha, b, hb, hk, ho⟩ := allSearch_sound _ out h
    have hf := (SortedQuarterMachine.correct as s).2.2 a |>.mp ha
    have hi := (SortedMeet.mem_inverse bs 0 b).mp hb
    subst ops
    rw [ho]
    constructor
    · simp [SortedMeet.decodeWitness]
    · simp only [SortedMeet.decodeWitness, List.length_map]
      rw [List.zip_append (by simp : (Native.Quarter.decode as.length a.2).length = as.length)]
      apply (eval_append_eq_iff _ _ _ _).mpr
      apply BitVec.eq_of_toNat_eq
      exact hf.2.symm.trans (hk.trans hi.2)

/-- Exhaustive original-input miss and original-order witness correctness, for every cut residue. -/
theorem original_correct {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    ((run (Source.ofWords p a tail)).2 = none ↔ ¬ Solvable tail a 0) ∧
      ∀ ops, (run (Source.ofWords p a tail)).2 = some ops →
        ops.length = tail.length ∧ eval (ops.zip tail) a = 0 := by
  have cut := Source.quarters_append tail
  constructor
  · simp only [run, prepare, solve, Option.map_eq_none_iff, SortedMeet.prepare_ofWords]
    rw [allSearch_none, cut]
  · intro ops hit
    simp only [run, prepare, SortedMeet.prepare_ofWords] at hit
    simpa only [cut] using solve_sound _ _ a _ ops hit

private noncomputable def solveCertificate : NativeCertificate solve allEncoding
    (encOption encBits) := by
  let original : NativeCertificate (id : SortedMeet.Input × ℕ → _) allEncoding allEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let readback := NativeCertificate.ofPolyTime SortedMeet.readback_polyTime
  exact NativeCertificate.congr (readback.comp (original.fst.prod allCertificate)) (fun _ => rfl)

private theorem prepare_polyTime : ComputableInPolyTime prepare Source.encoding allEncoding := by
  have h : ComputableInPolyTime (fun q : ProgramGeneration.Source => q.1.1.2)
      ProgramGeneration.sourceEncoding encUnary := by
    dsimp only [ProgramGeneration.sourceEncoding, BitInput.encoding]; fun_prop
  exact SortedMeet.prepare_polyTime.prod (h.comp Source.prepare_polyTime)

/-- One composed original-input machine, including balance before retention, class reuse,
all internal callback profiles, binary clocks and original witness output. -/
noncomputable def sourceCertificate : NativeCertificate run Source.encoding
    (encPair encNat (encOption encBits)) :=
  (balanceCertificate.prod solveCertificate).comp (NativeCertificate.ofPolyTime prepare_polyTime)

/-- A single finite bit machine precedes all source parameters and original operands.
Its general composed profiles are not a sharp source asymptotic bound. -/
theorem original_machine : ∃ (c k : ℕ) (Q : Type) (_ : Finite Q)
    (machine : Turing.MultiTapeTM k Bool Q), ∀ {m : ℕ} (p : ℕ) (a : BitVec m)
      (tail : List (BitVec m)),
      machine.ComputesInTimeAndSpace (Source.encoding (Source.ofWords p a tail))
        (encPair encNat (encOption encBits) (run (Source.ofWords p a tail)))
        (c * (sourceCertificate.time (Source.ofWords p a tail) + 1))
        (c * (sourceCertificate.space (Source.ofWords p a tail) + 1)) ∧
      ((run (Source.ofWords p a tail)).2 = none ↔ ¬ Solvable tail a 0) ∧
      ∀ ops, (run (Source.ofWords p a tail)).2 = some ops →
        ops.length = tail.length ∧ eval (ops.zip tail) a = 0 := by
  obtain ⟨c, ⟨k, Q, hQ, machine, computes⟩, _⟩ := sourceCertificate.computes
  exact ⟨c, k, Q, hQ, machine, fun p a tail => ⟨computes _, original_correct p a tail⟩⟩


/-- Physical full-state and packed-word widths come from original operands and real execution. -/
theorem records_fit {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p g : ℕ)
    (right : Bool) (r : ℕ × ℕ)
    (hr : r ∈ records ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g)))
      right (limit ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))) right)) :
    r.1 < 2 ^ m ∧ r.2 < 2 ^ (if right then bs.length else as.length) := by
  have h := (allRecords_mem _ right r).mp ((mem_records _ right r).mp hr).1
  cases right with
  | false =>
    have hf := (SortedQuarterMachine.correct as s).2.2 r |>.mp h
    exact ⟨hf.2 ▸ (eval ((Native.Quarter.decode as.length r.2).zip as) s).isLt, hf.1⟩
  | true =>
    have hb := (SortedMeet.mem_inverse bs 0 r).mp h
    exact ⟨hb.2 ▸ (backward (((Native.Quarter.decode bs.length r.2).reverse).zip bs) 0).isLt, hb.1⟩

/-- Encoded retained-prefix volume is bounded using actual physical word/payload widths and
computed class counts. This does not bound the interpreter-free callbacks' auxiliary workspace. -/
theorem retaining_prefix_wire {m : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (p g j : ℕ)
    (hj : j ≤ limit ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g)))
      (retainRight ((((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))))) :
    let input : Input := (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))
    (RadixPartition.inputEncoding
      (m, ((retainStep input (retainRight input))^[j] (0, [])).2)).length ≤
      2 * m + 1 + min (count input false) (count input true) *
        (4 * m + 2 * (as.length + bs.length) + 3) := by
  dsimp only
  let input : Input := (((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat)), (p, g))
  let rows := ((retainStep input (retainRight input))^[j] (0, [])).2
  have fits (r : ℕ × ℕ) (hr : r ∈ rows) : r.1 < 2 ^ m ∧ r.2 < 2 ^ (as.length + bs.length) := by
    change r ∈ ((retainStep input (retainRight input))^[j] (0, [])).2 at hr
    rw [retain_prefix, List.mem_reverse] at hr
    have sub := ((List.range_sublist.mpr hj).filter (accepts input (retainRight input))).map
      (row input (retainRight input))
    have hmem := sub.subset hr
    have hf := records_fit as bs s p g (retainRight input) r hmem
    refine ⟨hf.1, hf.2.trans_le (Nat.pow_le_pow_right (by decide) ?_)⟩
    cases retainRight input <;> simp
  have hw := (RadixSort.wire_bounds (m, rows) (as.length + bs.length) fits).2
  have hn := retained_prefix_length input j hj
  exact hw.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)

end Cslib.Cryptanalysis.AddXNOR.ClassStreaming
