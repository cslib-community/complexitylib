/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.Certificate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Foundations.Data.List.Fold

/-!
# Uniform matching of full-state record batches

Tag binary payloads by their source side, sort by the actual state key and stream
adjacent records. Any common key has a boundary between opposite tags, even with
arbitrary collisions and duplicate witnesses. The scan retains one record and
one found witness; input/output, sorting, tags and internal scan buffers are
charged separately from the retained state. This is a batch operation, not a
claim that an arbitrarily large class may be materialized in smaller-side space.
-/

public section
namespace Turing.MultiTapeTM.SortedMatch
open Cslib.GenericRAM

/-- Full state and packed witness; tags use one extra payload bit. -/
abbrev Record := ℕ × ℕ

/-- Keep the actual state and attach an explicit source-side bit. -/
def tag (right : Bool) (r : Record) : Record :=
  let (state, witness) := r
  (state, 2 * witness + if right then 1 else 0)

/-- Two neighboring records meet exactly when their keys agree and side tags differ. -/
def cross (a b : Record) : Bool := decide (a.1 = b.1 ∧ a.2 % 2 ≠ b.2 % 2)

/-- Return witnesses in left/right order, independently of their sorted order. -/
def answer (a b : Record) : ℕ × ℕ :=
  if a.2 % 2 = 0 then (a.2 / 2, b.2 / 2) else (b.2 / 2, a.2 / 2)

/-- Compare the retained preceding record with the next one. -/
def edge (previous : Option Record) (row : Record) : Option (ℕ × ℕ) :=
  if previous.isSome && cross (previous.getD (0, 0)) row then
    some (answer (previous.getD (0, 0)) row) else none

/-- A continuing scan keeps only the previous row and the first witness. -/
def next (state : (Option Record × Option (ℕ × ℕ)) × Record) :
    Option Record × Option (ℕ × ℕ) :=
  let ((previous, found), row) := state
  (some row, if found.isSome then found else edge previous row)

/-- Streaming scan of the sorted tagged records. -/
def scan (rows : List Record) : Option (ℕ × ℕ) :=
  (rows.foldl (fun state row => next (state, row)) (none, none)).2

private def searchFrom (previous : Option Record) : List Record → Option (ℕ × ℕ)
  | [] => none
  | row :: rows => (edge previous row).orElse (fun _ => searchFrom (some row) rows)

private theorem fold_from (rows : List Record) (previous : Option Record)
    (found : Option (ℕ × ℕ)) :
    (rows.foldl (fun state row => next (state, row)) (previous, found)).2 =
      found.orElse (fun _ => searchFrom previous rows) := by
  induction rows generalizing previous found with
  | nil => cases found <;> rfl
  | cons row rows ih =>
    rw [List.foldl_cons]
    cases found with
    | some value =>
      change (rows.foldl (fun state row => next (state, row)) (some row, some value)).2 = some value
      simpa using ih (some row) (some value)
    | none =>
      change (rows.foldl (fun state row => next (state, row))
        (some row, edge previous row)).2 = searchFrom previous (row :: rows)
      rw [ih]
      rfl

private theorem scan_cons (row : Record) (rows : List Record) :
    scan (row :: rows) = searchFrom (some row) rows := by
  rw [scan, List.foldl_cons, fold_from]
  rfl

private theorem scan_cons_cons (a b : Record) (rows : List Record) :
    scan (a :: b :: rows) = if cross a b then some (answer a b) else scan (b :: rows) := by
  rw [scan_cons, searchFrom, scan_cons]
  cases h : cross a b <;> simp [edge, h]

/-- Every reported match comes from two actual input occurrences of opposite sides. -/
theorem scan_sound (rows : List Record) (out : ℕ × ℕ) (hit : scan rows = some out) :
    ∃ a ∈ rows, ∃ b ∈ rows, cross a b = true ∧ answer a b = out := by
  induction rows with
  | nil => simp [scan] at hit
  | cons a rows ih =>
    cases rows with
    | nil => simp [scan_cons, searchFrom] at hit
    | cons b rows =>
      rw [scan_cons_cons] at hit
      by_cases h : cross a b = true
      · simp only [h, ite_true, Option.some.injEq] at hit
        exact ⟨a, by simp, b, by simp, h, hit⟩
      · simp only [h] at hit
        obtain ⟨x, hx, y, hy, hxy, ho⟩ := ih hit
        exact ⟨x, by simp [hx], y, by simp [hy], hxy, ho⟩

private theorem scan_none_pairwise (rows : List Record)
    (sorted : rows.Pairwise (fun a b => a.1 ≤ b.1)) (miss : scan rows = none) :
    rows.Pairwise (fun a b => a.1 = b.1 → a.2 % 2 = b.2 % 2) := by
  induction rows with
  | nil => simp
  | cons a rows ih =>
    cases rows with
    | nil => simp
    | cons b rows =>
      rw [scan_cons_cons] at miss
      have hab : cross a b = false := by
        cases h : cross a b <;> simp_all
      have tailmiss : scan (b :: rows) = none := by
        simpa only [hab, Bool.false_eq_true, ite_false] using miss
      have ht := ih sorted.tail tailmiss
      refine List.pairwise_cons.mpr ⟨?_, ht⟩
      intro z hz heq
      have habkey : a.1 = b.1 := by
        have h₁ := List.rel_of_pairwise_cons sorted (by simp : b ∈ b :: rows)
        have h₂ := List.rel_of_pairwise_cons sorted hz
        have h₃ : b.1 ≤ z.1 := by
          rcases List.mem_cons.mp hz with rfl | hz
          · rfl
          · exact List.rel_of_pairwise_cons sorted.tail hz
        omega
      have habtag : a.2 % 2 = b.2 % 2 := by
        simp only [cross, decide_eq_false_iff_not] at hab
        tauto
      rcases List.mem_cons.mp hz with rfl | hz
      · exact habtag
      · exact habtag.trans (List.rel_of_pairwise_cons ht hz (by omega))

/-- A sorted batch misses exactly when it has no cross-side common key. -/
theorem scan_none_iff (rows : List Record) (sorted : rows.Pairwise (fun a b => a.1 ≤ b.1)) :
    scan rows = none ↔ ¬ ∃ a ∈ rows, ∃ b ∈ rows, cross a b = true := by
  constructor
  · intro h
    have hp := scan_none_pairwise rows sorted h
    rintro ⟨a, ha, b, hb, hx⟩
    have same : a.1 = b.1 ∧ a.2 % 2 ≠ b.2 % 2 := by simpa only [cross, decide_eq_true_eq] using hx
    have htag : a.2 % 2 = b.2 % 2 := by
      let : Std.Symm (fun a b : Record => a.1 = b.1 → a.2 % 2 = b.2 % 2) :=
        ⟨fun _ _ h heq => (h heq.symm).symm⟩
      by_cases he : a = b
      · simp [he]
      · exact hp.forall ha hb he same.1
    exact same.2 htag
  · intro h
    cases hs : scan rows with
    | none => rfl
    | some out => exact False.elim (h (by
        obtain ⟨a, ha, b, hb, hx, _⟩ := scan_sound rows out hs
        exact ⟨a, ha, b, hb, hx⟩))

/-- Runtime width and the two actually materialized full-state batches. -/
abbrev Input := ℕ × (List Record × List Record)

/-- Unary key width and both binary record lists. -/
def encoding : Input ↪ List Bool :=
  encPair encUnary (encPair (encList RadixPartition.recordEncoding)
    (encList RadixPartition.recordEncoding))

/-- The two labels are generated by computation, not supplied as a side-correctness premise. -/
def tagged (input : Input) : List Record :=
  let (_, (left, right)) := input
  left.map (tag false) ++ right.map (tag true)

/-- One fixed sort and one fixed streaming scan, for all runtime widths and batches. -/
def run (input : Input) : Option (ℕ × ℕ) :=
  let (width, _) := input
  scan (RadixSort.sort (width, tagged input))

private theorem cross_tag (side other : Bool) (a b : Record) :
    cross (tag side a) (tag other b) = decide (a.1 = b.1 ∧ side ≠ other) := by
  cases side <;> cases other <;> simp [cross, tag, Nat.add_mod]

private theorem answer_left_right (a b : Record) :
    answer (tag false a) (tag true b) = (a.2, b.2) := by
  have h : (tag false a).2 % 2 = 0 := by simp [tag]
  simp only [answer, h, ite_true]
  change ((2 * a.2 + 0) / 2, (2 * b.2 + 1) / 2) = (a.2, b.2)
  apply Prod.ext <;> omega

private theorem answer_right_left (a b : Record) :
    answer (tag true b) (tag false a) = (a.2, b.2) := by
  have h : (tag true b).2 % 2 ≠ 0 := by simp [tag, Nat.add_mod]
  simp only [answer, h, ite_false]
  change ((2 * a.2 + 0) / 2, (2 * b.2 + 1) / 2) = (a.2, b.2)
  apply Prod.ext <;> omega

private theorem mem_tagged (input : Input) (r : Record) :
    r ∈ tagged input ↔ (∃ a ∈ input.2.1, tag false a = r) ∨
      (∃ b ∈ input.2.2, tag true b = r) := by
  simp only [tagged, List.mem_append, List.mem_map]

private theorem sorted_perm (input : Input) :
    (RadixSort.sort (input.1, tagged input)).Perm (tagged input) :=
  (RadixSort.prefix_invariants (tagged input) input.1).2

/-- A returned pair retains two actual witnesses for the same actual full state. -/
theorem sound (input : Input) (out : ℕ × ℕ) (hit : run input = some out) :
    ∃ a ∈ input.2.1, ∃ b ∈ input.2.2, a.1 = b.1 ∧ out = (a.2, b.2) := by
  obtain ⟨a, ha, b, hb, hx, ho⟩ := scan_sound _ out hit
  have ha' := (mem_tagged input a).mp ((sorted_perm input).mem_iff.mp ha)
  have hb' := (mem_tagged input b).mp ((sorted_perm input).mem_iff.mp hb)
  rcases ha' with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩ <;>
    rcases hb' with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · simp [cross_tag] at hx
  · have hkey : l.1 = r.1 := by simpa [cross_tag] using hx
    exact ⟨l, hl, r, hr, hkey, ho.symm.trans (answer_left_right l r)⟩
  · have hkey : l.1 = r.1 := by simpa [cross_tag] using hx
    exact ⟨r, hr, l, hl, hkey.symm, ho.symm.trans (answer_right_left r l)⟩
  · simp [cross_tag] at hx

/-- Fitting keys make the radix scan exhaustive, including empty lists and arbitrary collisions. -/
theorem none_iff (input : Input)
    (fits : ∀ r ∈ input.2.1 ++ input.2.2, r.1 < 2 ^ input.1) :
    run input = none ↔ ¬ ∃ a ∈ input.2.1, ∃ b ∈ input.2.2, a.1 = b.1 := by
  have hfit : ∀ r ∈ tagged input, r.1 < 2 ^ input.1 := by
    intro r hr
    rcases (mem_tagged input r).mp hr with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact fits a (List.mem_append_left _ ha)
    · exact fits a (List.mem_append_right _ ha)
  have hsorted := (RadixSort.correct (input.1, tagged input) hfit).2
  change scan _ = none ↔ _
  rw [scan_none_iff _ hsorted]
  constructor
  · intro h ⟨a, ha, b, hb, hk⟩
    apply h
    refine ⟨tag false a, (sorted_perm input).mem_iff.mpr ?_, tag true b,
      (sorted_perm input).mem_iff.mpr ?_, ?_⟩
    · exact (mem_tagged input _).mpr (Or.inl ⟨a, ha, rfl⟩)
    · exact (mem_tagged input _).mpr (Or.inr ⟨b, hb, rfl⟩)
    · simpa [cross_tag] using hk
  · intro h ⟨a, ha, b, hb, hx⟩
    have ha' := (mem_tagged input a).mp ((sorted_perm input).mem_iff.mp ha)
    have hb' := (mem_tagged input b).mp ((sorted_perm input).mem_iff.mp hb)
    rcases ha' with ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩ <;>
      rcases hb' with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · simp [cross_tag] at hx
    · exact h ⟨l, hl, r, hr, by simpa [cross_tag] using hx⟩
    · have hk : l.1 = r.1 := by simpa [cross_tag] using hx
      exact h ⟨r, hr, l, hl, hk.symm⟩
    · simp [cross_tag] at hx

private abbrev recEncoding : Record ↪ List Bool := encPair encNat encNat
private abbrev stateEncoding : (Option Record × Option (ℕ × ℕ)) ↪ List Bool :=
  encPair (encOption recEncoding) (encOption recEncoding)

private theorem cross_polyTime : ComputableTidilyInPolyTime
    (fun q : Record × Record => cross q.1 q.2) (encPair recEncoding recEncoding) encBool := by
  unfold cross
  apply ComputableTidilyInPolyTime.decide_and
  · apply ComputableTidilyInPolyTime.decide_eq' <;> fun_prop
  · apply ComputableTidilyInPolyTime.decide_ne (encB := encNat) <;>
      (apply ComputableTidilyInPolyTime.binary_mod' <;> fun_prop)

private theorem answer_polyTime : ComputableTidilyInPolyTime
    (fun q : Record × Record => answer q.1 q.2) (encPair recEncoding recEncoding) recEncoding := by
  unfold answer
  apply ComputableTidilyInPolyTime.ite_decide
  · apply ComputableTidilyInPolyTime.decide_eq' (encB := encNat)
    · apply ComputableTidilyInPolyTime.binary_mod' <;> fun_prop
    · exact .const 0
  · apply ComputableTidilyInPolyTime.prod <;>
      (apply ComputableTidilyInPolyTime.binary_div' <;> fun_prop)
  · apply ComputableTidilyInPolyTime.prod <;>
      (apply ComputableTidilyInPolyTime.binary_div' <;> fun_prop)

private theorem edge_polyTime : ComputableTidilyInPolyTime
    (fun q : Option Record × Record => edge q.1 q.2)
    (encPair (encOption recEncoding) recEncoding) (encOption recEncoding) := by
  have prev := ComputableTidilyInPolyTime.fst (encOption recEncoding) recEncoding
  have row := ComputableTidilyInPolyTime.snd (encOption recEncoding) recEncoding
  have get := prev.optionGetDWithInput (ComputableTidilyInPolyTime.const (0, 0))
  have test := prev.optionIsSome.bool_and' (cross_polyTime.comp (get.prod row))
  have output := (ComputableTidilyInPolyTime.optionSome recEncoding).comp
    (answer_polyTime.comp (get.prod row))
  exact test.cond output (.const none)

private theorem next_polyTime : ComputableTidilyInPolyTime next
    (encPair stateEncoding recEncoding) stateEncoding := by
  have st := ComputableTidilyInPolyTime.fst stateEncoding recEncoding
  have prev := (ComputableTidilyInPolyTime.fst (encOption recEncoding)
    (encOption recEncoding)).comp st
  have found := (ComputableTidilyInPolyTime.snd (encOption recEncoding)
    (encOption recEncoding)).comp st
  have row := ComputableTidilyInPolyTime.snd stateEncoding recEncoding
  exact ((ComputableTidilyInPolyTime.optionSome recEncoding).comp row).prod
    (found.optionIsSome.cond found (edge_polyTime.comp (prev.prod row)))

private theorem answer_wire (a b : Record) (B : ℕ)
    (ha : (recEncoding a).length ≤ B) (hb : (recEncoding b).length ≤ B) :
    (recEncoding (answer a b)).length ≤ 3 * B + 1 := by
  have hda : (encNat (a.2 / 2)).length ≤ (encNat a.2).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size (Nat.div_le_self a.2 2)
  have hdb : (encNat (b.2 / 2)).length ≤ (encNat b.2).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size (Nat.div_le_self b.2 2)
  simp only [recEncoding, length_encPair] at ha hb
  unfold answer
  split_ifs <;> simp only [recEncoding, length_encPair] <;> omega

private theorem scan_prefix_wire (rows : List Record) (j : ℕ) (hj : j ≤ rows.length) :
    (stateEncoding (streamState (none, none) next rows j)).length ≤
      5 * (streamRecordLength recEncoding rows + 1) + 5 := by
  let B := streamRecordLength recEncoding rows + 1
  have rowwire (i : ℕ) (hi : i < rows.length) : (recEncoding rows[i]).length ≤ B :=
    (le_listMax (f := fun row => (recEncoding row).length) (List.getElem_mem hi)).trans
      (Nat.le_succ _)
  have trace := List.foldl_take_invariant rows (fun s row => next (s, row)) (none, none)
    (fun _ state => (encOption recEncoding state.1).length ≤ B + 1 ∧
      (encOption recEncoding state.2).length ≤ 3 * B + 2)
    (by simp)
    (fun i hi state hs => by
      have hr := rowwire i hi
      refine ⟨?_, ?_⟩
      · simpa only [next, encOption_some, List.length_cons] using Nat.add_le_add_right hr 1
      · rcases state with ⟨previous, found⟩
        cases found with
        | some out => simpa only [next, Option.isSome_some, ite_true] using hs.2
        | none =>
          cases previous with
          | none => simp [next, edge]
          | some a =>
            have ha : (recEncoding a).length ≤ B := by
              simpa only [encOption_some, List.length_cons, Nat.add_le_add_iff_right] using hs.1
            have hw := Nat.add_le_add_right (answer_wire a rows[i] B ha hr) 1
            cases h : cross a rows[i]
            · simp [next, edge, h]
            · simpa only [next, edge, Option.isSome_none, Option.isSome_some,
                Option.getD_some, Bool.true_and, h, ite_true, Bool.false_eq_true,
                ite_false, encOption_some, List.length_cons, Nat.add_assoc, Nat.reduceAdd] using hw)
  obtain ⟨hp, hf⟩ := trace j hj
  simp only [streamState, stateEncoding, length_encPair]
  omega

/-- One actual streaming scan, charging the complete batch plus a polynomial per-record budget.
The retained row/witness and all internal callbacks are bounded at every execution prefix. -/
theorem scan_computable :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO scan (encList (encPair encNat encNat)) (encOption (encPair encNat encNat))
        (fun rows => (encList (encPair encNat encNat) rows).length +
          (rows.length + 1) * P (streamRecordLength (encPair encNat encNat) rows + 1))
        (fun rows => (encList (encPair encNat encNat) rows).length +
          (rows.length + 1) * P (streamRecordLength (encPair encNat encNat) rows + 1)) := by
  have decode : ComputableTidilyInPolyTime (id : Record → Record)
      (encFramed recEncoding) recEncoding := .of_linear (.of_unframe (fun _ => by simp))
  have adapted := next_polyTime.comp
    ((ComputableTidilyInPolyTime.fst stateEncoding (encFramed recEncoding)).prod
      (decode.comp (ComputableTidilyInPolyTime.snd stateEncoding (encFramed recEncoding))))
  obtain ⟨tN, sN, htN, hsN, hnext⟩ := adapted
  simp only [Function.comp_def, id_eq] at hnext
  obtain ⟨A, hA, hmA, hbound⟩ := exists_mono_poly (htN.add hsN)
  have finish := ComputableTidilyInPolyTime.snd (encOption recEncoding) (encOption recEncoding)
  obtain ⟨tF, sF, htF, hsF, hfinish⟩ := finish
  obtain ⟨F, hF, hmF, hfb⟩ := exists_mono_poly (htF.add hsF)
  obtain ⟨cI, hinit⟩ := computableInTimeAndSpace_of_const
    (encIn := encList recEncoding) (encOut := stateEncoding)
    ((none, none) : Option Record × Option (ℕ × ℕ))
  obtain ⟨cE, hemit⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair stateEncoding (encFramed recEncoding)) (encOut := encBits) ([] : List Bool)
  let P : ℕ → ℕ := fun B => A (12 * B + 12) + F (5 * B + 5) + 10 * B + 2 * cE + 20
  have hP : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have hmP : Monotone P := fun a b hab => by
    have := hmA (show 12 * a + 12 ≤ 12 * b + 12 by omega)
    have := hmF (show 5 * a + 5 ≤ 5 * b + 5 by omega)
    dsimp only [P]
    omega
  have callbacks (rows : List Record) (j : ℕ) (hj : j < rows.length) :
      tN (streamState (none, none) next rows j, rows[j]) +
        sN (streamState (none, none) next rows j, rows[j]) ≤
      A (12 * (streamRecordLength recEncoding rows + 1) + 12) := by
    have hs := scan_prefix_wire rows j hj.le
    have hr := le_listMax (f := fun row => (recEncoding row).length) (List.getElem_mem hj)
    change (recEncoding rows[j]).length ≤ streamRecordLength recEncoding rows at hr
    apply (hbound _).trans
    apply hmA
    simp only [stateEncoding, recEncoding, length_encPair] at hs hr
    simp only [stateEncoding, recEncoding, length_encPair, encFramed_apply, length_frame]
    omega
  obtain ⟨C, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold
    (g := scan) (encA := encFramed recEncoding) (encS := stateEncoding)
    (encIn := encList recEncoding) (encOut := encOption recEncoding)
    (next := next) (finish := Prod.snd)
    rawFrameReader (fun row => frame (recEncoding row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) id (fun _ => rfl)
    hinit.computableTidilyInTimeAndSpace hnext hemit.computableTidilyInTimeAndSpace hfinish
    (fun rows => by simp only [Function.const_apply, encBits_apply, streamEmit_const_nil,
      List.nil_append,
      streamState, List.take_length, scan, id_eq])
    (tMax := fun rows => P (streamRecordLength recEncoding rows + 1))
    (sMax := fun rows => P (streamRecordLength recEncoding rows + 1))
    (lMax := fun rows => 5 * (streamRecordLength recEncoding rows + 1) + 5)
    (fun rows j hj => by
      simp only [Function.const_apply, id_eq]
      have := callbacks rows j hj
      dsimp only [P]
      omega)
    (fun rows j hj => by
      simp only [Function.const_apply, id_eq]
      have := callbacks rows j hj
      dsimp only [P]
      omega)
    (fun rows j hj => scan_prefix_wire rows j hj)
    (fun rows j hj => by
      have hr := le_listMax (f := fun row => (recEncoding row).length) (List.getElem_mem hj)
      change (recEncoding rows[j]).length ≤ streamRecordLength recEncoding rows at hr
      simp only [id_eq, encFramed_apply, length_frame]
      omega)
  simp only [Function.const_apply, id_eq] at hc
  let plain := NativeCertificate.ofTimeAndSpace hc.computableInTimeAndSpace
  let K := C * (2 * cI + 20) + 1
  have estimates (rows : List Record) :
      plain.time rows ≤ K * ((encList recEncoding rows).length +
        (rows.length + 1) * P (streamRecordLength recEncoding rows + 1) + 1) ∧
      (C * (0 + sF (streamState (none, none) next rows rows.length) +
        P (streamRecordLength recEncoding rows + 1) +
          (5 * (streamRecordLength recEncoding rows + 1) + 5) + 1)) ≤
        K * ((encList recEncoding rows).length +
          (rows.length + 1) * P (streamRecordLength recEncoding rows + 1) + 1) := by
    have hw := scan_prefix_wire rows rows.length le_rfl
    have hf := (hfb (streamState (none, none) next rows rows.length)).trans (hmF hw)
    have hp : 5 * (streamRecordLength recEncoding rows + 1) + 5 ≤
        P (streamRecordLength recEncoding rows + 1) := by dsimp only [P]; omega
    have ht : tF (streamState (none, none) next rows rows.length) ≤
        P (streamRecordLength recEncoding rows + 1) := by dsimp only [P]; omega
    have hs : sF (streamState (none, none) next rows rows.length) ≤
        P (streamRecordLength recEncoding rows + 1) := by dsimp only [P]; omega
    let D := (encList recEncoding rows).length +
      (rows.length + 1) * P (streamRecordLength recEncoding rows + 1) + 1
    have hD : 1 ≤ D := by dsimp only [D]; omega
    have hPD : P (streamRecordLength recEncoding rows + 1) ≤ D := by
      dsimp only [D]
      nlinarith
    constructor
    · have hNP := Nat.mul_le_mul_left rows.length hp
      have hnP := Nat.mul_le_mul_left rows.length (show
        1 ≤ P (streamRecordLength recEncoding rows + 1) by omega)
      have hinner : 2 * cI + 2 + tF (streamState (none, none) next rows rows.length) +
          (encList recEncoding rows).length + rows.length *
            (P (streamRecordLength recEncoding rows + 1) +
              (5 * (streamRecordLength recEncoding rows + 1) + 5) + 1) +
          (5 * (streamRecordLength recEncoding rows + 1) + 5) + 1 ≤ 2 * cI + 2 + 3 * D := by
        dsimp only [D]
        nlinarith only [ht, hp, hNP, hnP]
      have hscale : 2 * cI + 2 + 3 * D ≤ (2 * cI + 20) * D := by nlinarith only [hD]
      have hC := Nat.mul_le_mul_left C (hinner.trans hscale)
      have hK := Nat.mul_le_mul_right D (Nat.le_succ (C * (2 * cI + 20)))
      change C * _ ≤ K * D
      dsimp only [K]
      nlinarith only [hC, hK]
    · have hinner : 0 + sF (streamState (none, none) next rows rows.length) +
          P (streamRecordLength recEncoding rows + 1) +
            (5 * (streamRecordLength recEncoding rows + 1) + 5) + 1 ≤ 4 * D := by omega
      have hC := Nat.mul_le_mul_left C hinner
      have hK : 4 * C ≤ K := by dsimp only [K]; nlinarith
      have hscale := Nat.mul_le_mul_right D hK
      change C * _ ≤ K * D
      nlinarith only [hC, hscale]
  refine ⟨P, hP, hmP, plain.computes.mono (2 * K) ?_ ?_⟩
  · intro rows
    have h := (estimates rows).1
    nlinarith only [h]
  · intro rows
    obtain ⟨ht, hs⟩ := estimates rows
    change _ + plain.time rows ≤ _
    nlinarith only [ht, hs]

private theorem tag_polyTime : ComputableTidilyInPolyTime
    (fun q : Bool × Record => tag q.1 q.2) (encPair encBool recEncoding) recEncoding := by
  unfold tag
  fun_prop

/-- A real streamed tagging machine; its polynomial is fixed before all runtime batches. -/
theorem tag_computable :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun input : Bool × List Record => input.2.map (tag input.1))
        (encPair encBool (encList (encPair encNat encNat))) (encList (encPair encNat encNat))
        (fun input => (encPair encBool (encList (encPair encNat encNat)) input).length +
          (input.2.length + 1) * P (streamFilterWidth encBool (encPair encNat encNat) input))
        (fun input => (encPair encBool (encList (encPair encNat encNat)) input).length +
          (input.2.length + 1) * P (streamFilterWidth encBool (encPair encNat encNat) input)) := by
  have singleton : ComputableTidilyInPolyTime (fun r : Record => [r])
      recEncoding (encList recEncoding) := .of_linear (.of_frame (fun _ => by simp))
  obtain ⟨P, hp, hm, hc⟩ := ComputableInO.flatMap_stream
    (ComputableInPolyTime.of_tidy (singleton.comp tag_polyTime))
  refine ⟨P, hp, hm, hc.of_enc_eq ?_⟩
  intro input
  rw [List.map_eq_flatMap]
  rfl

private noncomputable def tagCertificate : NativeCertificate
    (fun input : Bool × List Record => input.2.map (tag input.1))
    (encPair encBool (encList recEncoding)) (encList recEncoding) := by
  let P := Classical.choose tag_computable
  have h := (Classical.choose_spec tag_computable).2.2
  exact ⟨_, _, h⟩

private noncomputable def sortCertificate : NativeCertificate RadixSort.sort
    (encPair encUnary (encList recEncoding)) (encList recEncoding) := by
  let P := Classical.choose RadixSort.computable
  have h := (Classical.choose_spec RadixSort.computable).2.2
  have input := h.of_encIn_eq (encD := encPair encUnary (encList recEncoding)) id (fun _ => rfl)
  exact ⟨_, _, input.of_enc_eq (encC := encList recEncoding) (fun _ => rfl)⟩

private noncomputable def scanCertificate : NativeCertificate scan
    (encList recEncoding) (encOption recEncoding) := by
  let P := Classical.choose scan_computable
  have h := (Classical.choose_spec scan_computable).2.2
  exact ⟨_, _, h⟩

/-- Construct the actual tagged-union/sort/scan machine. Both materialized batches and all
intermediate copies/headers/scan buffers are charged by the composed profiles. In particular
this certificate does not replace their simultaneous size by the smaller input's size. -/
noncomputable def runCertificate : NativeCertificate run encoding
    (encOption (encPair encNat encNat)) := by
  let original : NativeCertificate (id : Input → Input) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let left := tagCertificate.comp
    ((NativeCertificate.const (em := encBool) false).prod (original.snd.fst))
  let right := tagCertificate.comp
    ((NativeCertificate.const (em := encBool) true).prod (original.snd.snd))
  let tagged := (left.prod right).post (ComputableInO.append' (enc := recEncoding))
  let sorted := sortCertificate.comp (original.fst.prod tagged)
  exact NativeCertificate.congr (scanCertificate.comp sorted) (fun _ => rfl)

end Turing.MultiTapeTM.SortedMatch
