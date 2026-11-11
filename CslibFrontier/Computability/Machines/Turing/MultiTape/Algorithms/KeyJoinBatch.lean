/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
public import Mathlib.Algebra.Order.Floor.Div
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinStream
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Bounded row-aligned windows of a projected-quarter join

A window selects complete right occurrence runs by their first Cartesian rank.
Only the selected left run is crossed with the right run. Quarter lists are
rescanned, but unselected Cartesian pairs are neither generated nor looked up.
The actual machine uses binary scalar counters and direct output emission; no
retained dictionary or growing output buffer is callback state.

## Main definitions

* `groupWindow`, `window`: one bucket and a complete grouped rank window.
* `windowCertificate`: uniform bounded-output join execution with actual callback profiles.

## Main results

* `window_mem_join`, `window_cover`: actual pair provenance and exhaustive batch coverage.
* `window_length`, `batch_allowance`: derived output and restart-volume bounds.
-/

public section
namespace Turing.MultiTapeTM.KeyJoinBatch
open Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er
private abbrev en := encPair encNat encNat

private def cutNext (state : ℕ × ℕ) (_ : SortedMatch.Record) : ℕ × ℕ :=
  let (skip, count) := state
  if skip = 0 then (0, count-1) else (skip-1, count)

private def cutEmit (state : ℕ × ℕ) (row : SortedMatch.Record) : List SortedMatch.Record :=
  let (skip, count) := state
  if skip = 0 ∧ 0 < count then [row] else []

private theorem cut_eq (skip count : ℕ) (rows : List SortedMatch.Record) :
    NativeCertificate.emitFold cutNext cutEmit (skip, count) rows =
      (rows.drop skip).take count := by
  induction rows generalizing skip count with
  | nil => simp [NativeCertificate.emitFold]
  | cons row rows ih =>
    cases skip <;> cases count <;>
      simp [NativeCertificate.emitFold, cutNext, cutEmit, ih]

/-- A single encoded scan cuts a list using binary skip/count state. Output is emitted,
not repeatedly copied as a growing next-state list. -/
private noncomputable def cutCertificate : NativeCertificate
    (fun q : (ℕ × ℕ) × List SortedMatch.Record => (q.2.drop q.1.1).take q.1.2)
    (encPair en el) el := by
  have next : ComputableInPolyTime (fun q : (ℕ × ℕ) × SortedMatch.Record => cutNext q.1 q.2)
      (encPair en er) en := by dsimp only [cutNext]; fun_prop
  have emit : ComputableInPolyTime (fun q : (ℕ × ℕ) × SortedMatch.Record => cutEmit q.1 q.2)
      (encPair en er) el := by
    have test : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × SortedMatch.Record => decide (q.1.1 = 0 ∧ 0 < q.1.2))
        (encPair en er) encBool := by fun_prop
    have single : ComputableTidilyInPolyTime (fun r : SortedMatch.Record => [r]) er el :=
      .of_linear (.of_frame (fun _ => by simp))
    exact .of_tidy ((test.tidy.cond
      (single.comp (ComputableTidilyInPolyTime.snd en er)) (.const [])).of_enc_eq (fun q => by
        simp [cutEmit]))
  exact NativeCertificate.congr (NativeCertificate.emitFoldCertificate en er er cutNext cutEmit
    (.ofPolyTime next) (.ofPolyTime emit)) (fun q => cut_eq q.1.1 q.1.2 q.2)

/-- Count list occurrences with a binary scalar state and one encoded list read. -/
private noncomputable def lengthCertificate : NativeCertificate
    (fun rows : List SortedMatch.Record => rows.length) el encNat := by
  let ei := encPair (encPair encBool encNat) er
  have step : ComputableInPolyTime (fun q : (Bool × ℕ) × SortedMatch.Record => q.1.2 + 1)
      ei encNat := by fun_prop
  let loop := NativeCertificate.foldlStream encBool encNat er
    (fun _ n _ => n+1) (.ofPolyTime step)
  let input : NativeCertificate (id : List SortedMatch.Record → _) el el :=
    .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (loop.comp
    ((NativeCertificate.const false).prod ((NativeCertificate.const 0).prod input)))
    (fun _ => by simp)

/-- Complete right rows whose first local Cartesian rank belongs to the supplied interval. -/
def groupWindow (bounds : ℕ × ℕ) (group : List SortedMatch.Record) : List (ℕ × ℕ) :=
  let (skip, count) := bounds
  let left := KeyJoin.side false group
  let right := KeyJoin.side true group
  let first := skip ⌈/⌉ right.length
  let last := (skip+count) ⌈/⌉ right.length
  ((left.drop first).take (last-first)).flatMap (fun a =>
    right.map (fun b => (a.2/2, b.2/2)))

/-- Subtract one bucket's full pair population from the binary rank window. -/
def advance (bounds : ℕ × ℕ) (group : List SortedMatch.Record) : ℕ × ℕ :=
  let (skip, count) := bounds
  let population := KeyJoin.population group
  (skip-population, count-(population-skip))

/-- Emit one bounded row-aligned window, holding only quarter runs and its actual output. -/
def window (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record)) : List (ℕ × ℕ) :=
  NativeCertificate.emitFold advance groupWindow bounds groups

private noncomputable def sideCertificate (right : Bool) : NativeCertificate
    (KeyJoin.side right) el el := by
  let proof := (Classical.choose_spec
    (ComputableInO.filter_stream KeyJoinStream.test_polyTime)).2.2
  let filtered : NativeCertificate (fun q : Bool × List SortedMatch.Record => KeyJoin.side q.1 q.2)
      (encPair encBool el) el := ⟨_, _, proof⟩
  let original : NativeCertificate (id : List SortedMatch.Record → _) el el :=
    .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (filtered.comp
    ((NativeCertificate.const right).prod original)) (fun _ => rfl)

private noncomputable def populationCertificate :
    NativeCertificate KeyJoin.population el encNat := by
  have mul : ComputableInPolyTime (fun q : ℕ × ℕ => q.1*q.2) en encNat := by fun_prop
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime mul).comp
    ((lengthCertificate.comp (sideCertificate false)).prod
      (lengthCertificate.comp (sideCertificate true)))) (fun _ => rfl)

private noncomputable def advanceCertificate : NativeCertificate
    (fun q : (ℕ × ℕ) × List SortedMatch.Record => advance q.1 q.2) (encPair en el) en := by
  let original : NativeCertificate (id : (ℕ × ℕ) × List SortedMatch.Record → _)
      (encPair en el) (encPair en el) := .linear (.of_eq (fun _ => rfl))
  let population := populationCertificate.comp original.snd
  have update : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ =>
      (q.1.1-q.2, q.1.2-(q.2-q.1.1))) (encPair en encNat) en := by fun_prop
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime update).comp
    (original.fst.prod population)) (fun _ => rfl)

private noncomputable def groupWindowCertificate : NativeCertificate
    (fun q : (ℕ × ℕ) × List SortedMatch.Record => groupWindow q.1 q.2) (encPair en el) el := by
  let original : NativeCertificate (id : (ℕ × ℕ) × List SortedMatch.Record → _)
      (encPair en el) (encPair en el) := .linear (.of_eq (fun _ => rfl))
  let left := (sideCertificate false).comp original.snd
  let right := (sideCertificate true).comp original.snd
  let size := lengthCertificate.comp right
  have ceil : ComputableInPolyTime (fun q : ℕ × ℕ => q.1 ⌈/⌉ q.2) en encNat := by
    apply ComputableInPolyTime.of_tidy
    have a := ComputableTidilyInPolyTime.fst encNat encNat
    have b := ComputableTidilyInPolyTime.snd encNat encNat
    have h := ComputableTidilyInPolyTime.binary_div'
      (ComputableTidilyInPolyTime.binary_sub' (a.binary_add' b) (.const 1)) b
    simpa only [Nat.ceilDiv_eq_add_pred_div] using h
  have bounds : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ =>
      (q.1.1 ⌈/⌉ q.2, (q.1.1+q.1.2) ⌈/⌉ q.2 - q.1.1 ⌈/⌉ q.2))
      (encPair en encNat) en := by
    have lo : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => q.1.1)
        (encPair en encNat) encNat := by fun_prop
    have count : ComputableInPolyTime (fun q : (ℕ × ℕ) × ℕ => q.1.2)
        (encPair en encNat) encNat := by fun_prop
    have divisor := ComputableInPolyTime.snd en encNat
    have first := ceil.comp (lo.prod divisor)
    have sum := ComputableInPolyTime.of_tidy (lo.tidy.binary_add' count.tidy)
    have last := ceil.comp (sum.prod divisor)
    exact first.prod (ComputableInPolyTime.binary_sub' last first)
  let limits := (NativeCertificate.ofPolyTime bounds).comp (original.fst.prod size)
  let selected := cutCertificate.comp (limits.prod left)
  let proof := (Classical.choose_spec KeyJoinStream.cross_computable).2.2
  let cross : NativeCertificate KeyJoinStream.cross (encPair el el) el := ⟨_, _, proof⟩
  exact NativeCertificate.congr (cross.comp (right.prod selected)) (fun _ => rfl)

/-- Actual scalar-state group scanning and bounded Cartesian emission. No retained dictionary
or incremental output buffer occurs in the state copied by these callbacks. -/
noncomputable def windowCertificate : NativeCertificate
    (fun q : (ℕ × ℕ) × List (List SortedMatch.Record) => window q.1 q.2)
    (encPair (encPair encNat encNat) (encList (encList RadixPartition.recordEncoding)))
    (encList RadixPartition.recordEncoding) :=
  NativeCertificate.congr (NativeCertificate.emitFoldCertificate en el er advance groupWindow
    advanceCertificate groupWindowCertificate) (fun _ => rfl)

private theorem mem_cut {α : Type} (xs : List α) (lo hi : ℕ) (a : α) :
    a ∈ (xs.drop lo).take (hi-lo) ↔
      ∃ i, ∃ h : i < xs.length, lo ≤ i ∧ i < hi ∧ xs[i] = a := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp h
    have hlen : j < (xs.drop lo).length := (lt_min_iff.mp hj).2
    have hi' : lo+j < xs.length := by simp only [List.length_drop] at hlen; omega
    refine ⟨lo+j, hi', by omega, ?_, ?_⟩
    · have := (lt_min_iff.mp hj).1; omega
    · simpa only [List.getElem_drop] using he
  · rintro ⟨i, hi', hlo, hhi, he⟩
    have hj : i-lo < min (hi-lo) (xs.drop lo).length := by
      simp only [List.length_drop]; omega
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i-lo, hj, by simpa only [List.getElem_drop, Nat.add_sub_of_le hlo] using he⟩

private def headPosition (group : List SortedMatch.Record) (pair : ℕ × ℕ) (start : ℕ) : Prop :=
  ∃ i, ∃ h : i < (KeyJoin.side false group).length,
    ∃ b ∈ KeyJoin.side true group,
      pair = ((KeyJoin.side false group)[i].2/2, b.2/2) ∧
        start = i * (KeyJoin.side true group).length

private def position : List (List SortedMatch.Record) → (ℕ × ℕ) → ℕ → Prop
  | [], _, _ => False
  | group :: groups, pair, start => headPosition group pair start ∨
      (KeyJoin.population group ≤ start ∧ position groups pair (start-KeyJoin.population group))

private theorem groupWindow_mem (bounds : ℕ × ℕ) (group : List SortedMatch.Record)
    (pair : ℕ × ℕ) : pair ∈ groupWindow bounds group ↔
      ∃ start, headPosition group pair start ∧ bounds.1 ≤ start ∧ start < bounds.1+bounds.2 := by
  rcases bounds with ⟨skip, count⟩
  dsimp only [groupWindow]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, he⟩
    obtain ⟨i, hi, hlo, hhi, he'⟩ := (mem_cut _ _ _ _).mp ha
    have hr : 0 < (KeyJoin.side true group).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hb)
    have lower := (ceilDiv_le_iff_le_mul hr).mp hlo
    have upper := ceilDiv_le_iff_le_mul (b := skip+count) (c := i) hr
    refine ⟨i * (KeyJoin.side true group).length, ?_, ?_, ?_⟩
    · exact ⟨i, hi, b, hb, by rw [he']; exact he.symm, rfl⟩
    · simpa only [Nat.mul_comm] using lower
    · rw [Nat.mul_comm]; omega
  · rintro ⟨start, ⟨i, hi, b, hb, he, rfl⟩, hlo, hhi⟩
    have hr : 0 < (KeyJoin.side true group).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem hb)
    have lower := (ceilDiv_le_iff_le_mul hr).mpr (by simpa only [Nat.mul_comm] using hlo)
    have upper := ceilDiv_le_iff_le_mul (b := skip+count) (c := i) hr
    have hlast : i < (skip+count) ⌈/⌉ (KeyJoin.side true group).length := by
      rw [Nat.mul_comm] at hhi; omega
    exact ⟨(KeyJoin.side false group)[i], (mem_cut _ _ _ _).mpr ⟨i, hi, lower, hlast, rfl⟩,
      b, hb, he.symm⟩

private theorem position_exists (groups : List (List SortedMatch.Record)) (pair : ℕ × ℕ) :
    (∃ start, position groups pair start) ↔ pair ∈ KeyJoin.join groups := by
  induction groups with
  | nil => simp [position, KeyJoin.join]
  | cons group groups ih =>
    simp only [KeyJoin.join, List.flatMap_cons, List.mem_append]
    constructor
    · rintro ⟨start, head | ⟨_, tail⟩⟩
      · obtain ⟨i, hi, b, hb, rfl, _⟩ := head
        exact Or.inl (List.mem_flatMap.mpr ⟨_, List.getElem_mem hi,
          List.mem_map.mpr ⟨b, hb, rfl⟩⟩)
      · exact Or.inr (ih.mp ⟨_, tail⟩)
    · rintro (head | tail)
      · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp head
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
        exact ⟨i * (KeyJoin.side true group).length,
          Or.inl ⟨i, hi, b, hb, he.symm, rfl⟩⟩
      · obtain ⟨start, hs⟩ := ih.mpr tail
        exact ⟨KeyJoin.population group+start, Or.inr ⟨by omega, by simpa using hs⟩⟩

private theorem position_lt (groups : List (List SortedMatch.Record)) (pair : ℕ × ℕ)
    (start : ℕ) (h : position groups pair start) : start < KeyJoin.count groups := by
  induction groups generalizing start with
  | nil => exact False.elim h
  | cons group groups ih =>
    change headPosition group pair start ∨ _ at h
    change start < KeyJoin.population group + KeyJoin.count groups
    rcases h with head | ⟨hl, ht⟩
    · obtain ⟨i, hi, b, hb, _, rfl⟩ := head
      have hr : 0 < (KeyJoin.side true group).length :=
        List.length_pos_iff.mpr (List.ne_nil_of_mem hb)
      have hmul := Nat.mul_lt_mul_of_pos_right hi hr
      change _ < KeyJoin.population group at hmul
      omega
    · have hh := ih _ ht
      omega

private theorem window_position (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record))
    (pair : ℕ × ℕ) : pair ∈ window bounds groups ↔
      ∃ start, position groups pair start ∧ bounds.1 ≤ start ∧ start < bounds.1+bounds.2 := by
  induction groups generalizing bounds with
  | nil => simp [window, NativeCertificate.emitFold, position]
  | cons group groups ih =>
    rcases bounds with ⟨skip, count⟩
    change pair ∈ groupWindow (skip, count) group ++ window (advance (skip, count) group) groups ↔ _
    rw [List.mem_append, groupWindow_mem, ih]
    dsimp only [advance]
    constructor
    · rintro (⟨start, hs, hlo, hhi⟩ | ⟨start, hs, hlo, hhi⟩)
      · exact ⟨start, Or.inl hs, hlo, hhi⟩
      · refine ⟨KeyJoin.population group+start, Or.inr ⟨by omega, by simpa using hs⟩, ?_, ?_⟩ <;>
          omega
    · rintro ⟨start, (head | ⟨hl, tail⟩), hlo, hhi⟩
      · exact Or.inl ⟨start, head, hlo, hhi⟩
      · exact Or.inr ⟨start-KeyJoin.population group, tail, by omega, by omega⟩

/-- Every emitted pair is an actual occurrence match of the full generated class. -/
theorem window_mem_join (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record))
    (pair : ℕ × ℕ) (h : pair ∈ window bounds groups) : pair ∈ KeyJoin.join groups := by
  obtain ⟨start, hs, _⟩ := (window_position bounds groups pair).mp h
  exact (position_exists groups pair).mp ⟨start, hs⟩

/-- Every actual class pair belongs to a computed row-aligned batch, with no traversal or
witness correctness premise. Empty groups and colliding occurrences are allowed. -/
theorem window_cover (capacity : ℕ) (hc : 0 < capacity) (groups : List (List SortedMatch.Record))
    (pair : ℕ × ℕ) (h : pair ∈ KeyJoin.join groups) :
    ∃ i < KeyJoin.count groups ⌈/⌉ capacity, pair ∈ window (i*capacity, capacity) groups := by
  obtain ⟨start, hs⟩ := (position_exists groups pair).mpr h
  have ht := position_lt groups pair start hs
  have low := Nat.div_mul_le_self start capacity
  have rem := Nat.mod_lt start hc
  have decomp := Nat.mod_add_div start capacity
  have ceil := ceilDiv_le_iff_le_mul (b := KeyJoin.count groups) (c := start/capacity) hc
  refine ⟨start/capacity, ?_, (window_position _ _ _).mpr ⟨start, hs, low, ?_⟩⟩
  · rw [Nat.mul_comm] at ceil
    omega
  · rw [Nat.mul_comm capacity] at decomp
    omega

private theorem groupWindow_length (bounds : ℕ × ℕ) (group : List SortedMatch.Record) :
    (groupWindow bounds group).length ≤
      min bounds.2 (KeyJoin.population group-bounds.1) + group.length := by
  rcases bounds with ⟨skip, count⟩
  let L := (KeyJoin.side false group).length
  let R := (KeyJoin.side true group).length
  let first := skip ⌈/⌉ R
  let last := (skip+count) ⌈/⌉ R
  have he : (groupWindow (skip, count) group).length = min (last-first) (L-first) * R := by
    simp [groupWindow, List.length_flatMap, List.length_map, first, last, L, R]
  have hR : R ≤ group.length := List.length_filter_le _ _
  rw [he]
  by_cases hr : R = 0
  · simp [hr]
  · have hr' : 0 < R := by omega
    have lower : skip ≤ first * R := by
      simpa only [first, Nat.mul_comm] using
        ((ceilDiv_le_iff_le_mul (b := skip) (c := first) hr').mp le_rfl)
    have upper : last * R ≤ skip+count+R-1 := by
      dsimp only [last]
      rw [Nat.ceilDiv_eq_add_pred_div]
      exact Nat.div_mul_le_self _ _
    have h₁ := Nat.mul_le_mul_right R (Nat.min_le_left (last-first) (L-first))
    have h₂ := Nat.mul_le_mul_right R (Nat.min_le_right (last-first) (L-first))
    rw [Nat.sub_mul] at h₁ h₂
    have pop : KeyJoin.population group = L*R := rfl
    rw [pop]
    omega

/-- Every materialized batch has at most its rank capacity plus quarter input records.
The bound follows from the actual row selection and advancing binary state, not a memory premise. -/
theorem window_length (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record)) :
    (window bounds groups).length ≤ bounds.2 + groups.flatten.length := by
  induction groups generalizing bounds with
  | nil => simp [window, NativeCertificate.emitFold]
  | cons group groups ih =>
    rcases bounds with ⟨skip, count⟩
    have head := groupWindow_length (skip, count) group
    have tail := ih (advance (skip, count) group)
    change (groupWindow (skip, count) group ++
      window (advance (skip, count) group) groups).length ≤ _
    simp only [List.length_append, List.flatten_cons]
    dsimp only at head
    dsimp only [advance] at tail ⊢
    omega

/-- A complete set of windows pays one quarter/dictionary allowance per batch, up to one
final partial batch. This is the arithmetic charge used by the actual restarted algorithm. -/
theorem batch_allowance (population capacity : ℕ) :
    (population ⌈/⌉ capacity) * capacity ≤ population + capacity := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have := Nat.div_mul_le_self (population+capacity-1) capacity
  omega

end Turing.MultiTapeTM.KeyJoinBatch
