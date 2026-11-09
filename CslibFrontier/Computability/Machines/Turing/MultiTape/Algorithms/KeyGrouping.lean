/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.SplitBy

/-!
# Writing equal-key groups without a growing group accumulator

A single record reader remembers only the previous binary key. It writes nested
framed records directly to the output, inserting an outer-group terminator when
the key changes and at the end. No group list is carried between machine rounds.
The computed function is Core's `List.splitBy`, preserving order and occurrences.
The resource bounds include input/output framing and every callback temporary.


## Main definitions

* `run`: Core's consecutive equal-key grouping, with payloads and order preserved.
* `outputEncoding`: nested framed records, suitable for a later group consumer.

## Main results

* `flatten_run`, `group_keys`, `group_nonempty`: exact occurrence and group semantics.
* `wire_length`, `wire_le`: exact nested framing and its linear volume bound.
* `run_computable`: one-pass bit execution with small-state prefix bounds.
-/

public section
namespace Turing.MultiTapeTM.KeyGrouping

/-- Maximal consecutive equal-key runs, preserving every payload and duplicate occurrence. -/
def run (rows : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  rows.splitBy (fun a b => decide (a.1 = b.1))

/-- Both levels of grouping use the usual framed-list encoding. -/
def outputEncoding : List (List (ℕ × ℕ)) ↪ List Bool :=
  encList (encList RadixPartition.recordEncoding)

/-- Grouping neither drops nor rearranges records. -/
theorem flatten_run (rows : List (ℕ × ℕ)) : (run rows).flatten = rows :=
  List.flatten_splitBy _ _

private def escape (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, b])

private theorem escape_append (a b : List Bool) : escape (a ++ b) = escape a ++ escape b := by
  simp only [escape, List.flatMap_append]

private theorem frame_escape (bits : List Bool) : frame bits = escape bits ++ [false] := rfl

private def piece (row : ℕ × ℕ) : List Bool := escape (frame (RadixPartition.recordEncoding row))

private def next (q : Option ℕ × (ℕ × ℕ)) : Option ℕ := some q.2.1

private def emit (q : Option ℕ × (ℕ × ℕ)) : List Bool :=
  let (previous, row) := q
  (if previous.isSome && decide (previous.getD 0 ≠ row.1) then [false] else []) ++ piece row

private def close (previous : Option ℕ) : List Bool := if previous.isSome then [false] else []

private theorem close_state (key : ℕ) (rows : List (ℕ × ℕ)) :
    close (streamState (some key) next rows rows.length) = [false] := by
  simp only [streamState, List.take_length]
  induction rows generalizing key with
  | nil => rfl
  | cons row rows ih => simpa only [List.foldl_cons, next] using ih row.1

private theorem loop_wire (rows : List (ℕ × ℕ)) (previous : ℕ × ℕ)
    (bucket : List (ℕ × ℕ)) (done : List (List (ℕ × ℕ))) :
    outputEncoding (List.splitBy.loop (fun a b : ℕ × ℕ => decide (a.1 = b.1))
      rows previous bucket done) =
      outputEncoding done.reverse ++
        escape (encList RadixPartition.recordEncoding (bucket.reverse ++ [previous])) ++
        streamEmit next emit (some previous.1) rows ++ [false] := by
  induction rows generalizing previous bucket done with
  | nil =>
    simp only [List.splitBy.loop, List.reverse_cons, outputEncoding, encList_append,
      encList_cons, encList_nil, List.append_nil, List.reverse_cons, streamEmit]
    rw [frame_escape]
    simp only [List.append_assoc]
  | cons row rows ih =>
    rw [List.splitBy.loop]
    cases h : decide (previous.1 = row.1) with
    | false =>
      rw [ih]
      simp only [List.reverse_cons, outputEncoding, encList_append, encList_cons,
        encList_nil, List.append_nil, List.reverse_nil, List.nil_append,
        streamEmit, next]
      have hn : previous.1 ≠ row.1 := of_decide_eq_false h
      simp [emit, hn, piece, frame_escape, escape_append, List.append_assoc]
    | true =>
      rw [ih]
      have he : previous.1 = row.1 := of_decide_eq_true h
      simp only [List.reverse_cons, encList_append, escape_append, List.append_assoc,
        streamEmit, next, emit, Option.isSome_some, Option.getD_some, he,
        ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_eq_true,
        ite_false, List.nil_append, piece, encList_cons, encList_nil, List.append_nil]

/-- Exact nested framing is emitted by small-state streaming, not by repeatedly copying groups. -/
private theorem encoded_run (rows : List (ℕ × ℕ)) :
    outputEncoding (run rows) = streamEmit next emit none rows ++
      close (streamState none next rows rows.length) := by
  cases rows with
  | nil => rfl
  | cons row rows =>
    rw [run, List.splitBy, loop_wire]
    simp only [outputEncoding, encList_nil, List.reverse_nil, List.nil_append,
      encList_cons, List.append_nil, streamEmit, emit, Option.isSome_none, Bool.false_and,
      Bool.false_eq_true, ite_false, next, piece]
    have hstate : streamState none next (row :: rows) (row :: rows).length =
        streamState (some row.1) next rows rows.length := by
      simp only [streamState, List.take_length, List.foldl_cons, next]
    rw [hstate, close_state]

/-- Nested framing adds only one terminator per group and one tag per original wire bit. -/
theorem wire_length (rows : List (ℕ × ℕ)) :
    (outputEncoding (run rows)).length =
      2 * (encList RadixPartition.recordEncoding rows).length + (run rows).length := by
  have h (groups : List (List (ℕ × ℕ))) :
      (outputEncoding groups).length =
        2 * (encList RadixPartition.recordEncoding groups.flatten).length + groups.length := by
    induction groups with
    | nil => rfl
    | cons group groups ih =>
      simp only [outputEncoding, encList_cons, List.length_append, length_frame,
        List.flatten_cons, encList_append, List.length_cons] at *
      omega
  simpa only [flatten_run] using h (run rows)

/-- Empty groups are never written. -/
theorem group_nonempty (rows : List (ℕ × ℕ)) (group : List (ℕ × ℕ))
    (hg : group ∈ run rows) : group ≠ [] := by
  rintro rfl
  exact List.nil_notMem_splitBy _ _ hg

/-- Every group has one key; on a sorted input these are the required equal-key buckets. -/
theorem group_keys (rows : List (ℕ × ℕ)) (group : List (ℕ × ℕ)) (hg : group ∈ run rows) :
    group.Pairwise (fun a b => a.1 = b.1) := by
  have hc := List.isChain_of_mem_splitBy hg
  have he : group.IsChain (fun a b : ℕ × ℕ => a.1 = b.1) :=
    hc.imp (fun _ _ h => of_decide_eq_true h)
  let : Trans (fun a b : ℕ × ℕ => a.1 = b.1) (fun a b : ℕ × ℕ => a.1 = b.1)
      (fun a b : ℕ × ℕ => a.1 = b.1) := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  exact he.pairwise

/-- Framed grouped output is at most three times the original record wire. -/
theorem wire_le (rows : List (ℕ × ℕ)) :
    (outputEncoding (run rows)).length ≤
      3 * (encList RadixPartition.recordEncoding rows).length := by
  have count (groups : List (List (ℕ × ℕ))) (hne : ∀ g ∈ groups, g ≠ []) :
      groups.length ≤ groups.flatten.length := by
    induction groups with
    | nil => rfl
    | cons group groups ih =>
      have hg : 0 < group.length := List.length_pos_iff.mpr (hne group (by simp))
      have ht := ih (fun g hg => hne g (List.mem_cons_of_mem _ hg))
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
  have hn := count (run rows) (group_nonempty rows)
  rw [flatten_run] at hn
  have hi := length_le_length_encList RadixPartition.recordEncoding rows
  rw [wire_length]
  omega

private theorem piece_polyTime : ComputableTidilyInPolyTime piece
    RadixPartition.recordEncoding encBits := by
  have hf : ComputableTidilyInPolyTime frame encBits encBits :=
    .of_linear (.of_frame (fun _ => rfl))
  have h := (ComputableTidilyInDegree.bitsDropLast).computableTidilyInPolyTime.comp
    (hf.comp (hf.comp (ComputableTidilyInPolyTime.encode RadixPartition.recordEncoding)))
  have hp (row : ℕ × ℕ) :
      piece row = (frame (frame (RadixPartition.recordEncoding row))).dropLast := by
    rw [frame_escape, List.dropLast_concat]
    rfl
  convert h using 1
  funext row
  exact hp row

private theorem next_polyTime : ComputableTidilyInPolyTime next
    (encPair (encOption encNat) RadixPartition.recordEncoding) (encOption encNat) :=
  (ComputableTidilyInPolyTime.optionSome encNat).comp
    ((ComputableTidilyInPolyTime.fst encNat encNat).comp
      (ComputableTidilyInPolyTime.snd (encOption encNat) RadixPartition.recordEncoding))

private theorem emit_polyTime : ComputableTidilyInPolyTime emit
    (encPair (encOption encNat) RadixPartition.recordEncoding) encBits := by
  have previous := ComputableTidilyInPolyTime.fst (encOption encNat) RadixPartition.recordEncoding
  have row := ComputableTidilyInPolyTime.snd (encOption encNat) RadixPartition.recordEncoding
  have key := (ComputableTidilyInPolyTime.fst encNat encNat).comp row
  have get := previous.optionGetDWithInput (ComputableTidilyInPolyTime.const 0)
  have change := previous.optionIsSome.bool_and'
    (ComputableTidilyInPolyTime.decide_ne (encB := encNat) get key)
  exact (change.cond (ComputableTidilyInPolyTime.const [false])
    (ComputableTidilyInPolyTime.const [])).bitsAppend (piece_polyTime.comp row)

private theorem close_polyTime : ComputableTidilyInPolyTime close (encOption encNat) encBits :=
  (ComputableTidilyInPolyTime.id'.optionIsSome).cond
    (ComputableTidilyInPolyTime.const [false]) (ComputableTidilyInPolyTime.const [])

private theorem state_wire (rows : List (ℕ × ℕ)) (j : ℕ) (hj : j ≤ rows.length) :
    (encOption encNat (streamState none next rows j)).length ≤
      streamRecordLength RadixPartition.recordEncoding rows + 1 := by
  let B := streamRecordLength RadixPartition.recordEncoding rows
  have hi := List.foldl_take_invariant rows (fun s r => next (s, r)) none
    (fun _ state => (encOption encNat state).length ≤ B + 1) (by simp)
    (fun i hi _ _ => by
      have hr := le_listMax (f := fun r => (RadixPartition.recordEncoding r).length)
        (List.getElem_mem hi)
      change (RadixPartition.recordEncoding rows[i]).length ≤ B at hr
      simp only [next, encOption_some, List.length_cons, RadixPartition.recordEncoding,
        length_encPair] at hr ⊢
      omega)
  exact hi j hj

/-- Actual one-pass grouping. Time is linear in record count times a polynomial in the maximum
record width; charged space is input/output volume plus a polynomial per-record budget.
No growing group is held in the loop state, even when all records have the same key. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run (encList RadixPartition.recordEncoding) outputEncoding
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        (rows.length + 1) * P (streamRecordLength RadixPartition.recordEncoding rows + 1))
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        P (streamRecordLength RadixPartition.recordEncoding rows + 1)) := by
  let er := RadixPartition.recordEncoding
  let es := encOption encNat
  have decode : ComputableTidilyInPolyTime (id : ℕ × ℕ → _) (encFramed er) er :=
    .of_linear (.of_unframe (fun _ => by simp))
  have arg := (ComputableTidilyInPolyTime.fst es (encFramed er)).prod
    (decode.comp (ComputableTidilyInPolyTime.snd es (encFramed er)))
  obtain ⟨tN, sN, htN, hsN, hN⟩ := next_polyTime.comp arg
  obtain ⟨tE, sE, htE, hsE, hE⟩ := emit_polyTime.comp arg
  simp only [Function.comp_def, id_eq] at hN hE
  obtain ⟨c, d, bound⟩ := (((htN.add hsN).add htE).add hsE).exists_le
  obtain ⟨tF, sF, htF, hsF, hF⟩ := close_polyTime
  obtain ⟨f, e, finishBound⟩ := (htF.add hsF).exists_le
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const
    (encIn := encList er) (encOut := es) (none : Option ℕ)
  let P : ℕ → ℕ := fun B => c * (6 * B + 6) ^ d + f * (2 * B + 3) ^ e + 10 * B + 10
  have hP : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have hm : Monotone P := by
    intro a b hab
    have hc := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega : 6*a+6 ≤ 6*b+6) d)
    have hf := Nat.mul_le_mul_left f (Nat.pow_le_pow_left (by omega : 2*a+3 ≤ 2*b+3) e)
    dsimp only [P]
    omega
  have callbacks (rows : List (ℕ × ℕ)) (j : ℕ) (hj : j < rows.length) :
      tN (streamState none next rows j, rows[j]) + sN (streamState none next rows j, rows[j]) +
        tE (streamState none next rows j, rows[j]) + sE (streamState none next rows j, rows[j]) ≤
      c * (6 * (streamRecordLength er rows + 1) + 6) ^ d := by
    have hs := state_wire rows j hj.le
    change (es (streamState none next rows j)).length ≤ streamRecordLength er rows + 1 at hs
    have hr := le_listMax (f := fun r => (er r).length) (List.getElem_mem hj)
    change (er rows[j]).length ≤ streamRecordLength er rows at hr
    apply (bound _).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_encPair, encFramed_apply, length_frame]
    omega
  have finishes (rows : List (ℕ × ℕ)) :
      tF (streamState none next rows rows.length) + sF (streamState none next rows rows.length) ≤
        f * (2 * (streamRecordLength er rows + 1) + 3) ^ e := by
    apply (finishBound _).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have hs := state_wire rows rows.length le_rfl
    change (encOption encNat (streamState none next rows rows.length)).length ≤
      streamRecordLength er rows + 1 at hs
    omega
  obtain ⟨C, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold
    (g := run) (encA := encFramed er) (encS := es)
    (encIn := encList er) (encOut := outputEncoding)
    (next := next) (finish := close)
    rawFrameReader (fun row => frame (er row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) id (fun _ => rfl)
    hI.computableTidilyInTimeAndSpace hN hE hF
    (fun rows => by simpa only [encBits_apply, id_eq, Function.const_apply] using encoded_run rows)
    (tMax := fun rows => P (streamRecordLength er rows + 1))
    (sMax := fun rows => P (streamRecordLength er rows + 1))
    (lMax := fun rows => 2 * (streamRecordLength er rows + 1) + 3)
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
    (fun rows j hj => by
      have hs := state_wire rows j hj
      change (es (streamState none next rows j)).length ≤ streamRecordLength er rows + 1 at hs
      exact hs.trans (by omega))
    (fun rows j hj => by
      have hr := le_listMax (f := fun r => (er r).length) (List.getElem_mem hj)
      change (er rows[j]).length ≤ streamRecordLength er rows at hr
      simp only [id_eq, encFramed_apply, length_frame]
      omega)
  simp only [Function.const_apply, id_eq] at hc
  let K := C * (2 * cI + 20) + 3
  refine ⟨P, hP, hm, ComputableInO.of_bounds hc.computableInTimeAndSpace K ?_ ?_ ?_⟩
  · intro rows
    have hf := finishes rows
    have ht : tF (streamState none next rows rows.length) ≤
        P (streamRecordLength er rows + 1) := by dsimp only [P]; omega
    have hp : 2 * (streamRecordLength er rows + 1) + 4 ≤
        P (streamRecordLength er rows + 1) := by dsimp only [P]; omega
    let D := (encList er rows).length + (rows.length + 1) *
      P (streamRecordLength er rows + 1) + 1
    have hn := Nat.mul_le_mul_left rows.length hp
    have hD : 1 ≤ D := by dsimp only [D]; omega
    have hinner : 2*cI+2 + tF (streamState none next rows rows.length) +
        (encList er rows).length + rows.length *
          (P (streamRecordLength er rows + 1) + (2*(streamRecordLength er rows+1)+3) + 1) +
            (2*(streamRecordLength er rows+1)+3) + 1 ≤ 2*cI+2+3*D := by
      dsimp only [D]
      nlinarith only [ht, hp, hn]
    have hscale : 2*cI+2+3*D ≤ (2*cI+20)*D := by nlinarith only [hD]
    change C * _ ≤ K * D
    have hh := Nat.mul_le_mul_left C (hinner.trans hscale)
    have hk := Nat.mul_le_mul_right D (Nat.le_add_right (C * (2*cI+20)) 3)
    exact hh.trans (by simpa only [Nat.mul_assoc] using hk)
  · intro rows
    have hf := finishes rows
    have hs : sF (streamState none next rows rows.length) ≤
        P (streamRecordLength er rows + 1) := by dsimp only [P]; omega
    have hp : 2 * (streamRecordLength er rows + 1) + 4 ≤
        P (streamRecordLength er rows + 1) := by dsimp only [P]; omega
    let D := (encList er rows).length + P (streamRecordLength er rows + 1) + 1
    have hinner : 0 + sF (streamState none next rows rows.length) +
        P (streamRecordLength er rows + 1) + (2 * (streamRecordLength er rows + 1) + 3) + 1 ≤
          3 * D := by dsimp only [D]; omega
    have hk : C * 3 ≤ K := by dsimp only [K]; nlinarith
    change C * _ ≤ K * D
    exact (Nat.mul_le_mul_left C hinner).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right D hk)
  · intro rows
    have hw := wire_le rows
    have hk : 3 ≤ K := by dsimp only [K]; omega
    exact hw.trans ((Nat.mul_le_mul_right _ hk).trans (Nat.mul_le_mul_left K (by omega)))

end Turing.MultiTapeTM.KeyGrouping
