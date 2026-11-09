/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClassJoin
public import CslibFrontier.Cryptanalysis.AddXNORClassStreaming
public import CslibFrontier.Computability.GenericRAM.Native.StreamingFold
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Mathlib.Data.List.Fold

/-!
# Generated backward classes and computed smaller-side retention

Both class populations come from actual quarter-query joins. Backward classes
use reversed suffix quarters, the complemented target as seed and complemented
projected class keys. Full-state records are reflected back before matching;
payloads encode the entire half word, retaining leading zero operators.

The computed populations determine orientation and the retained list. A count-only
streaming loop reduces their minimum into one scalar maximum before retention,
without constructing/reversing the semantic table. Actual
bit-machine certificates charge generation, grouping, consumer temporaries and
outer-state copying. Retained encoding bounds do not assert sharp auxiliary TM
workspace. The retained join now has output-sensitive bit bounds; opposite-side
access, preprocessing/control and global composition still need sharper bounds
for [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.

## Main definitions

* `count`, `records`: generated counts and full-state classes in both directions.
* `retainRight`, `retain`: computed orientation and one selected retained class.
* `balance`, `balancePrefix`: computed maximum and the actual scalar prepass prefixes.

## Main results

* `original_records`: exhaustive original half-word semantics in both directions.
* `count_eq_counter`, `balance_eq_counter`: exact agreement with original-half counters.
* `record_wire`, `records_prefix_wire`: physical widths of actual records and prefixes.
* `retained_prefix_wire`, `table_prefix_wire`: retained/count-table prefix wires.
* `balance_eq_prefix`, `balancePrefix_le`, `balancePrefix_wire`: scalar prepass correctness/width.
* `retained_join_volume`: streamed selected-class join cost uses the computed balance.
* `retainCertificate`, `balanceCertificate`: actual generated retention and count-only prepass.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.ClassBalance
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Original full-width quarter arrays and endpoints, with runtime projection depth. -/
abbrev Input := ProgramGeneration.Source

/-- Physical widths are unary; endpoints and every original operand are binary. -/
abbrev encoding := ProgramGeneration.sourceEncoding

private abbrev sideEncoding := encPair encoding encBool
private abbrev taskEncoding := encPair sideEncoding encNat
private abbrev recEncoding := encPair encNat encNat

/-- Forward quarters or genuinely reversed suffix quarters with complemented full-width target. -/
def halfInput (input : Input) (right : Bool) : SortedMeet.Input :=
  let (((width, _), (seed, target)), ((first, second), (third, fourth))) := input
  if right then ((width, 2 ^ width - 1 - target), (fourth.reverse, third.reverse))
  else ((width, seed), (first, second))

/-- Project the actual selected quarters, seed and class key. -/
def queryInput (input : Input) (right : Bool) (g : ℕ) : ClassJoin.Input :=
  let (((_, depth), _), _) := input
  let ((_, seed), (first, second)) := halfInput input right
  let modulus := 2 ^ depth
  (((depth, seed % modulus), (first.map (· % modulus), second.map (· % modulus))),
    if right then modulus - 1 - g % modulus else g % modulus)

/-- Both populations are computed from generated quarter-query groups. -/
def count (input : Input) (right : Bool) (g : ℕ) : ℕ :=
  ClassJoin.count (queryInput input right g)

/-- Full-width state and one packed complete half word. Backward payloads index reversed order,
as in the existing full-chain witness decoder. -/
def record (input : Input) (right : Bool) (uv : ℕ × ℕ) : ℕ × ℕ :=
  let half := halfInput input right
  let ((width, seed), (first, second)) := half
  let operators := SortedMeet.decodeWitness half uv
  let state := natEval width (operators.zip (first ++ second)) seed
  (if right then 2 ^ width - 1 - state else state, Native.Quarter.encode operators)

/-- Only the selected class is materialized; the two complete half spaces are not generated. -/
def records (input : Input) (right : Bool) (g : ℕ) : List (ℕ × ℕ) :=
  (ClassJoin.witnesses (queryInput input right g)).map (record input right)

/-- Generated occurrence counts are exactly the lengths of actual full-state classes. -/
theorem records_length (input : Input) (right : Bool) (g : ℕ) :
    (records input right g).length = count input right g := by
  simp only [records, List.length_map, count, ClassJoin.count_eq_length]

/-- The computed counts select the smaller retained side, breaking ties toward forward. -/
def retainRight (input : Input) (g : ℕ) : Bool :=
  decide (count input true g < count input false g)

/-- Retain one actually generated class in the computed orientation. -/
def retain (input : Input) (g : ℕ) : List (ℕ × ℕ) :=
  records input (retainRight input g) g

/-- Retention size is derived from both computed populations, rather than supplied as advice. -/
theorem retained_length (input : Input) (g : ℕ) :
    (retain input g).length = min (count input false g) (count input true g) := by
  by_cases h : count input true g < count input false g
  · simpa only [retain, records_length, retainRight, h, decide_true] using
      (Nat.min_eq_right (Nat.le_of_lt h)).symm
  · simpa only [retain, records_length, retainRight, h, decide_false] using
      (Nat.min_eq_left (show count input false g ≤ count input true g by omega)).symm

/-- Actual projection depth, already capped when the original source frontend is used. -/
def depth (input : Input) : ℕ :=
  let (((_, projected), _), _) := input
  projected

/-- One count-only round; no class record list is retained in this state. -/
def countStep (input : Input) (state : ℕ × List (ℕ × ℕ)) : ℕ × List (ℕ × ℕ) :=
  let (g, counts) := state
  (g + 1, (count input false g, count input true g) :: counts)

/-- A fixed runtime counter visits every computed class and records both populations. -/
def table (input : Input) : List (ℕ × ℕ) :=
  (((countStep input)^[2 ^ depth input] (0, [])).2).reverse

private theorem table_prefix (input : Input) (n : ℕ) :
    (countStep input)^[n] (0, []) =
      (n, ((List.range n).map (fun g => (count input false g, count input true g))).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [countStep, List.range_succ, List.map_append, List.map_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append]

/-- Exhaustive traversal is proved from the actual fixed counter program. -/
theorem table_eq (input : Input) : table input =
    (List.range (2 ^ depth input)).map (fun g => (count input false g, count input true g)) := by
  rw [table, table_prefix, List.reverse_reverse]

/-- Compute the maximum smaller population from the actual count-only prepass. -/
def balance (input : Input) : ℕ := listMax (fun counts => min counts.1 counts.2) (table input)

/-- The scalar maximum after the first `n` computed classes; no table is in this state. -/
def balancePrefix (input : Input) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun current g => max current
    (min (count input false g) (count input true g))) 0

/-- The streamed scalar prepass computes exactly the existing table-defined balance. -/
theorem balance_eq_prefix (input : Input) :
    balance input = balancePrefix input (2 ^ depth input) := by
  rw [balance, table_eq]
  simp only [listMax, List.map_map, Function.comp_def, balancePrefix,
    ← List.foldl_map, List.foldl_eq_foldr]

/-- Every computed retained size is bounded by the computed global maximum. -/
theorem class_le_balance (input : Input) (g : ℕ) (hg : g < 2 ^ depth input) :
    (retain input g).length ≤ balance input := by
  rw [retained_length]
  unfold balance
  exact le_listMax (a := (count input false g, count input true g)) (l := table input)
    (f := fun counts : ℕ × ℕ => min counts.1 counts.2)
    (by rw [table_eq]; exact List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩)

/-- The actual streamed join budget for the selected side is bounded by quarter volume and
computed balance. This bounds that machine phase, not all producer/probe temporaries. -/
theorem retained_join_volume (input : Input) (g : ℕ) (hg : g < 2 ^ depth input) :
    let query := queryInput input (retainRight input g) g
    let ((_, (first, second)), _) := query
    KeyJoinStream.volume (ClassJoin.groups query) ≤
      2 * (2 ^ first.length + 2 ^ second.length) + balance input + 1 := by
  have h := ClassJoin.groups_volume (queryInput input (retainRight input g) g)
  have hc := class_le_balance input g hg
  have hr := records_length input (retainRight input g) g
  change (retain input g).length = ClassJoin.count (queryInput input (retainRight input g) g) at hr
  rw [hr] at hc
  dsimp only at h ⊢
  omega

/-- Every prefix of every generated retained list is bounded by the actual computed balance.
This is list occupancy, not a bound on internal bit-machine callback workspace. -/
theorem retained_prefix (input : Input) (g n : ℕ) (hg : g < 2 ^ depth input) :
    ((retain input g).take n).length ≤ balance input := by
  rw [List.length_take]
  exact (Nat.min_le_right _ _).trans (class_le_balance input g hg)

private def word (a b : ℕ) (uv : ℕ × ℕ) : List Bool :=
  Native.Quarter.decode a uv.1 ++ (Native.Quarter.decode b uv.2).reverse

private theorem word_length (a b : ℕ) (uv : ℕ × ℕ) : (word a b uv).length = a + b := by
  simp only [word, List.length_append, List.length_reverse, Native.Quarter.decode_length]

private theorem word_zip {m : ℕ} (as bs : List (BitVec m)) (uv : ℕ × ℕ) :
    (word as.length bs.length uv).zip (as ++ bs) =
      ((Native.Quarter.decode as.length uv.1).zip as) ++
        (((Native.Quarter.decode bs.length uv.2).reverse).zip bs) := by
  exact List.zip_append (by simp : (Native.Quarter.decode as.length uv.1).length = as.length)

private theorem word_surjective (a b : ℕ) (xs : List Bool) (hlen : xs.length = a + b) :
    ∃ uv : ℕ × ℕ, uv.1 < 2 ^ a ∧ uv.2 < 2 ^ b ∧ word a b uv = xs := by
  have ha : (xs.take a).length = a := by rw [List.length_take, hlen]; omega
  have hb : (xs.drop a).reverse.length = b := by
    rw [List.length_reverse, List.length_drop, hlen]; omega
  refine ⟨(Native.Quarter.encode (xs.take a), Native.Quarter.encode (xs.drop a).reverse),
    ?_, ?_, ?_⟩
  · simpa only [ha] using Native.Quarter.encode_lt (xs.take a)
  · simpa only [hb] using Native.Quarter.encode_lt (xs.drop a).reverse
  · dsimp only [word]
    have haDecode : Native.Quarter.decode a (Native.Quarter.encode (xs.take a)) = xs.take a := by
      simpa only [ha] using Native.Quarter.decode_encode (xs.take a)
    have hbDecode : Native.Quarter.decode b (Native.Quarter.encode (xs.drop a).reverse) =
        (xs.drop a).reverse := by
      simpa only [hb] using Native.Quarter.decode_encode (xs.drop a).reverse
    rw [haDecode, hbDecode, List.reverse_reverse, List.take_append_drop]

private theorem projected_witnesses {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (uv : ℕ × ℕ) :
    uv ∈ ClassJoin.witnesses
      ((((p, (s.setWidth p).toNat),
        ((as.map (BitVec.setWidth p)).map BitVec.toNat,
          (bs.map (BitVec.setWidth p)).map BitVec.toNat)), g.toNat)) ↔
      uv.1 < 2 ^ as.length ∧ uv.2 < 2 ^ bs.length ∧
        (eval ((word as.length bs.length uv).zip (as ++ bs)) s).setWidth p = g := by
  rw [ClassJoin.mem_witnesses]
  simp only [List.length_map]
  have hz (xs : List Bool) (as : List (BitVec m)) :
      xs.zip (as.map (BitVec.setWidth p)) = project p (xs.zip as) := by
    rw [List.zip_map_right]; rfl
  rw [word_zip]
  have append (xs ys : List (Bool × BitVec m)) :
      project p xs ++ project p ys = project p (xs ++ ys) := by
    simp only [project, List.map_append]
  simp only [hz, append, ← eval_project hp]

/-- Actual projected-quarter witnesses in both directions. In the backward orientation the
seed and class key are complemented and the suffix quarters are reversed, before generation. -/
theorem original_witnesses {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p)
    (uv : ℕ × ℕ) :
    let (first, second, seed, key) :=
      if right then (ds.reverse, cs.reverse, ~~~t, ~~~g) else (as, bs, s, g)
    uv ∈ ClassJoin.witnesses
      (queryInput (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat) ↔
      uv.1 < 2 ^ first.length ∧ uv.2 < 2 ^ second.length ∧
        (eval ((Native.Quarter.decode first.length uv.1 ++
          (Native.Quarter.decode second.length uv.2).reverse).zip (first ++ second))
            seed).setWidth p = key := by
  cases right with
  | false =>
    have hi : queryInput (ProgramGeneration.originalSource p as bs cs ds s t) false g.toNat =
        (((p, (s.setWidth p).toNat),
          ((as.map (BitVec.setWidth p)).map BitVec.toNat,
            (bs.map (BitVec.setWidth p)).map BitVec.toNat)), g.toNat) := by
      simp only [queryInput, halfInput, ProgramGeneration.originalSource, BitInput.words,
        Bool.false_eq_true, ite_false, BitVec.toNat_setWidth, List.map_map,
        Function.comp_def, Nat.mod_eq_of_lt g.isLt]
    rw [hi]
    exact projected_witnesses hp as bs s g uv
  | true =>
    have hi : queryInput (ProgramGeneration.originalSource p as bs cs ds s t) true g.toNat =
        (((p, ((~~~t).setWidth p).toNat),
          ((ds.reverse.map (BitVec.setWidth p)).map BitVec.toNat,
            (cs.reverse.map (BitVec.setWidth p)).map BitVec.toNat)), (~~~g).toNat) := by
      simp only [queryInput, halfInput, ProgramGeneration.originalSource, BitInput.words,
        ite_true, BitVec.toNat_setWidth, BitVec.toNat_not, List.map_map,
        List.map_reverse, Function.comp_def, Nat.mod_eq_of_lt g.isLt]
    rw [hi]
    exact projected_witnesses hp ds.reverse cs.reverse (~~~t) (~~~g) uv

private theorem record_typed {m : ℕ} (input : Input) (right : Bool)
    (as bs : List (BitVec m)) (s : BitVec m) (uv : ℕ × ℕ)
    (hi : halfInput input right = ((m, s.toNat), (as.map BitVec.toNat, bs.map BitVec.toNat))) :
    record input right uv =
      ((if right then ~~~(eval ((word as.length bs.length uv).zip (as ++ bs)) s)
        else eval ((word as.length bs.length uv).zip (as ++ bs)) s).toNat,
          Native.Quarter.encode (word as.length bs.length uv)) := by
  rw [record, hi]
  dsimp only [SortedMeet.decodeWitness]
  simp only [List.length_map]
  have hz (xs : List Bool) : xs.zip (as.map BitVec.toNat ++ bs.map BitVec.toNat) =
      (xs.zip (as ++ bs)).map (fun q => (q.1, q.2.toNat)) := by
    rw [← List.map_append, List.zip_map_right]; rfl
  rw [hz, natEval_toNat]
  cases right <;> simp only [ite_false, ite_true, word, BitVec.toNat_not, Bool.false_eq_true]

/-- Full records reflect genuine backward states back to original orientation. The payload
still indexes the reversed suffix, exactly as required by the original witness decoder. -/
theorem original_record {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (right : Bool) (uv : ℕ × ℕ) :
    let (first, second, seed) := if right then (ds.reverse, cs.reverse, ~~~t) else (as, bs, s)
    let operators := Native.Quarter.decode first.length uv.1 ++
      (Native.Quarter.decode second.length uv.2).reverse
    let state := eval (operators.zip (first ++ second)) seed
    record (ProgramGeneration.originalSource p as bs cs ds s t) right uv =
      ((if right then ~~~state else state).toNat, Native.Quarter.encode operators) := by
  cases right with
  | false => exact record_typed _ false as bs s uv (by
      simp only [halfInput, ProgramGeneration.originalSource, BitInput.words,
        Bool.false_eq_true, ite_false])
  | true => exact record_typed _ true ds.reverse cs.reverse (~~~t) uv (by
      simp only [halfInput, ProgramGeneration.originalSource, BitInput.words,
        ite_true, BitVec.toNat_not, List.map_reverse])

private theorem class_reflection {m p : ℕ} (hp : p ≤ m)
    (state : BitVec m) (g : BitVec p) (right : Bool) :
    state.setWidth p = (if right then ~~~g else g) ↔
      (if right then ~~~state else state).setWidth p = g := by
  cases right with
  | false => rfl
  | true =>
    simp only [ite_true, BitVec.setWidth_not hp]
    constructor
    · intro h; rw [h, BitVec.not_not]
    · intro h; rw [← h, BitVec.not_not]

/-- Exhaustive original half-word semantics of both generated classes. In the backward case
operators and operands are in reversed suffix order and the emitted state is complemented back.
The record payload therefore has the existing reversed-suffix readback convention. -/
theorem original_records {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p)
    (r : ℕ × ℕ) :
    let first := if right then ds.reverse else as
    let second := if right then cs.reverse else bs
    let seed := if right then ~~~t else s
    r ∈ records (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat ↔
      ∃ ops : List Bool, ops.length = first.length + second.length ∧
        r = ((if right then ~~~(eval (ops.zip (first ++ second)) seed)
          else eval (ops.zip (first ++ second)) seed).toNat, Native.Quarter.encode ops) ∧
            (if right then ~~~(eval (ops.zip (first ++ second)) seed)
              else eval (ops.zip (first ++ second)) seed).setWidth p = g := by
  let input := ProgramGeneration.originalSource p as bs cs ds s t
  let first := if right then ds.reverse else as
  let second := if right then cs.reverse else bs
  let seed := if right then ~~~t else s
  have hw (uv : ℕ × ℕ) : uv ∈ ClassJoin.witnesses (queryInput input right g.toNat) ↔
      uv.1 < 2 ^ first.length ∧ uv.2 < 2 ^ second.length ∧
        (eval ((word first.length second.length uv).zip (first ++ second)) seed).setWidth p =
          (if right then ~~~g else g) := by
    cases right <;> exact original_witnesses hp as bs cs ds s t _ g uv
  have hr (uv : ℕ × ℕ) : record input right uv =
      ((if right then ~~~(eval ((word first.length second.length uv).zip (first ++ second)) seed)
        else eval ((word first.length second.length uv).zip (first ++ second)) seed).toNat,
          Native.Quarter.encode (word first.length second.length uv)) := by
    cases right <;> exact original_record as bs cs ds s t _ uv
  change r ∈ (ClassJoin.witnesses (queryInput input right g.toNat)).map (record input right) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨uv, hu, he⟩
    have hc := (hw uv).mp hu
    exact ⟨word first.length second.length uv, word_length _ _ _,
      he.symm.trans (hr uv), (class_reflection hp _ g right).mp hc.2.2⟩
  · rintro ⟨ops, hlen, he, hc⟩
    obtain ⟨uv, hu, hv, hword⟩ := word_surjective first.length second.length ops hlen
    refine ⟨uv, (hw uv).mpr ⟨hu, hv, ?_⟩, ?_⟩
    · rw [hword]
      exact (class_reflection hp _ g right).mpr hc
    · rw [hr, hword]
      exact he.symm

/-- Generated original states and complete packed half words fit their physical widths.
No address-space or native-support bound is used to establish these bit widths. -/
theorem records_fit {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p)
    (r : ℕ × ℕ) (hr : r ∈ records (ProgramGeneration.originalSource p as bs cs ds s t)
      right g.toNat) :
    let length := if right then cs.length + ds.length else as.length + bs.length
    r.1 < 2 ^ m ∧ r.2 < 2 ^ length := by
  obtain ⟨ops, hlen, rfl, _⟩ := (original_records hp as bs cs ds s t right g r).mp hr
  refine ⟨(if right then ~~~(eval (ops.zip _) _) else eval (ops.zip _) _).isLt, ?_⟩
  have h := Native.Quarter.encode_lt ops
  cases right <;> simp only [ite_true, ite_false, Bool.false_eq_true,
    List.length_reverse, Nat.add_comm] at hlen ⊢ <;> simpa only [hlen] using h

/-- Generated quarter joins and the existing original-half counter enumerate the same class.
This connects the new retained dictionary to the already proved streaming batch probe. -/
theorem records_mem_counter {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (right : Bool) (g : BitVec p)
    (r : ℕ × ℕ) :
    let halves : SortedMeet.Input := ((m, s.toNat),
      ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat))
    let task : ClassStreaming.Input := (halves, (p, g.toNat))
    r ∈ records (ProgramGeneration.originalSource p as bs cs ds s 0) right g.toNat ↔
      r ∈ ClassStreaming.records task right (ClassStreaming.limit task right) := by
  dsimp only
  let task : ClassStreaming.Input :=
    (((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)), (p, g.toNat))
  have hm := ClassStreaming.mem_records task right r
  have ha := ClassStreaming.allRecords_mem task right r
  have ho := original_records hp as bs cs ds s 0 right g r
  dsimp only at hm ha ho
  rw [hm, ha, ho]
  have decode (xs : List Bool) (n : ℕ) (hn : xs.length = n) :
      Native.Quarter.decode n (Native.Quarter.encode xs) = xs := by
    simpa only [hn] using Native.Quarter.decode_encode xs
  cases right with
  | false =>
    simp only [task, Bool.false_eq_true, ite_false]
    rw [(SortedQuarterMachine.correct (as ++ bs) s).2.2 r]
    constructor
    · rintro ⟨ops, hlen, rfl, hc⟩
      have hd := decode ops (as ++ bs).length (by simpa only [List.length_append] using hlen)
      refine ⟨⟨?_, by rw [hd]⟩, ?_⟩
      · simpa only [List.length_append, hlen] using Native.Quarter.encode_lt ops
      · simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat hc
    · rintro ⟨⟨hu, hs⟩, hc⟩
      refine ⟨Native.Quarter.decode (as ++ bs).length r.2, by simp, ?_, ?_⟩
      · exact Prod.ext hs (Native.Quarter.encode_decode hu).symm
      · apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_setWidth, ← hs] using hc
  | true =>
    simp only [task, ite_true]
    have hi := SortedMeet.mem_inverse (cs ++ ds) (0 : BitVec m) r
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] at hi
    rw [hi]
    have reflection (ops : List Bool) (hlen : ops.length = (cs ++ ds).length) :
        (~~~(eval (ops.zip (ds.reverse ++ cs.reverse)) (~~~(0 : BitVec m)))).toNat =
          (backward (ops.reverse.zip (cs ++ ds)) 0).toNat := by
      have h := SortedMeet.backward_key (cs ++ ds) 0 (Native.Quarter.encode ops)
      rw [decode ops _ hlen, List.reverse_append] at h
      simpa only [SortedMeet.reflect, BitVec.toNat_not] using h
    constructor
    · rintro ⟨ops, hlen, rfl, hc⟩
      have hl : ops.length = (cs ++ ds).length := by
        simpa only [List.length_reverse, List.length_append, Nat.add_comm] using hlen
      have hd := decode ops _ hl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [hl] using Native.Quarter.encode_lt ops
      · rw [hd]
        exact reflection ops hl
      · simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat hc
    · rintro ⟨⟨hu, hs⟩, hc⟩
      let ops := Native.Quarter.decode (cs ++ ds).length r.2
      have hl : ops.length = (cs ++ ds).length := by simp only [ops, Native.Quarter.decode_length]
      have he : r.1 =
          (~~~(eval (ops.zip (ds.reverse ++ cs.reverse)) (~~~(0 : BitVec m)))).toNat :=
        hs.trans (reflection ops hl).symm
      refine ⟨ops, by simpa only [List.length_reverse, List.length_append, Nat.add_comm] using hl,
        Prod.ext he (Native.Quarter.encode_decode hu).symm, ?_⟩
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_setWidth, ← he] using hc

private theorem word_injective (a b : ℕ) (uv xy : ℕ × ℕ)
    (hu : uv.1 < 2 ^ a ∧ uv.2 < 2 ^ b) (hx : xy.1 < 2 ^ a ∧ xy.2 < 2 ^ b)
    (he : word a b uv = word a b xy) : uv = xy := by
  have ht (u : ℕ) : (Native.Quarter.decode a u).take a = Native.Quarter.decode a u :=
    List.take_of_length_le (by simp)
  have hd (u : ℕ) : (Native.Quarter.decode a u).drop a = [] :=
    List.drop_of_length_le (by simp)
  have first := congrArg (List.take a) he
  have second := congrArg (List.drop a) he
  simp only [word, List.take_append, Native.Quarter.decode_length, ht,
    Nat.sub_self, List.take_zero, List.append_nil] at first
  simp only [word, List.drop_append, Native.Quarter.decode_length, hd,
    Nat.sub_self, List.drop_zero, List.nil_append] at second
  have hfirst := congrArg Native.Quarter.encode first
  have hsecond := congrArg (fun xs => Native.Quarter.encode xs.reverse) second
  simp only [Native.Quarter.encode_decode hu.1, Native.Quarter.encode_decode hx.1] at hfirst
  simp only [List.reverse_reverse, Native.Quarter.encode_decode hu.2,
    Native.Quarter.encode_decode hx.2] at hsecond
  exact Prod.ext hfirst hsecond

/-- Every complete packed half word occurs once. Colliding states do not duplicate witnesses. -/
theorem records_nodup {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (right : Bool) (g : BitVec p) :
    (records (ProgramGeneration.originalSource p as bs cs ds s t) right g.toNat).Nodup := by
  let input := ProgramGeneration.originalSource p as bs cs ds s t
  let first := if right then ds.reverse else as
  let second := if right then cs.reverse else bs
  have bounds (uv : ℕ × ℕ) (hu : uv ∈ ClassJoin.witnesses (queryInput input right g.toNat)) :
      uv.1 < 2 ^ first.length ∧ uv.2 < 2 ^ second.length := by
    have h := (original_witnesses hp as bs cs ds s t right g uv).mp hu
    cases right <;> exact ⟨h.1, h.2.1⟩
  have payload (uv : ℕ × ℕ) : (record input right uv).2 =
      Native.Quarter.encode (word first.length second.length uv) := by
    have h := original_record (p := p) as bs cs ds s t right uv
    cases right <;> exact congrArg Prod.snd h
  have decode (uv : ℕ × ℕ) :
      Native.Quarter.decode (first.length + second.length)
        (Native.Quarter.encode (word first.length second.length uv)) =
          word first.length second.length uv := by
    simpa only [word_length] using Native.Quarter.decode_encode (word first.length second.length uv)
  apply List.Nodup.map_on _ (ClassJoin.witnesses_nodup (queryInput input right g.toNat))
  intro uv hu xy hx he
  have h := congrArg Prod.snd he
  rw [payload, payload] at h
  have hw := congrArg (Native.Quarter.decode (first.length + second.length)) h
  rw [decode, decode] at hw
  exact word_injective _ _ uv xy (bounds uv hu) (bounds xy hx) hw

/-- Generated quarter classes preserve the exact occurrence counts of the original-half counter,
not merely membership or zero-count semantics. -/
theorem count_eq_counter {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (right : Bool) (g : BitVec p) :
    let halves : SortedMeet.Input := ((m, s.toNat),
      ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat))
    let task : ClassStreaming.Input := (halves, (p, g.toNat))
    count (ProgramGeneration.originalSource p as bs cs ds s 0) right g.toNat =
      ClassStreaming.count task right := by
  dsimp only
  let task : ClassStreaming.Input :=
    (((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)), (p, g.toNat))
  rw [← records_length, ClassStreaming.count_eq]
  have hp' := List.perm_ext_iff_of_nodup (records_nodup hp as bs cs ds s 0 right g)
    (ClassStreaming.records_nodup task right (ClassStreaming.limit task right))
  exact (hp'.mpr (fun r => records_mem_counter hp as bs cs ds s right g r)).length_eq

/-- The computed maximum is exactly the existing actual counter-based balance. This equality
is proved through unique original half words, not assumed class sizes. -/
theorem balance_eq_counter {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) :
    let halves : SortedMeet.Input := ((m, s.toNat),
      ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat))
    balance (ProgramGeneration.originalSource p as bs cs ds s 0) =
      ClassStreaming.balance (halves, p) := by
  dsimp only
  rw [ClassStreaming.balance_eq, balance, table_eq]
  have hd : depth (ProgramGeneration.originalSource p as bs cs ds s 0) = p := rfl
  rw [hd]
  simp only [listMax, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hg' := List.mem_range.mp hg
  have hleft := count_eq_counter hp as bs cs ds s false (BitVec.ofNat p g)
  have hright := count_eq_counter hp as bs cs ds s true (BitVec.ofNat p g)
  dsimp only at hleft hright
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg'] at hleft hright
  rw [hleft, hright]

private theorem count_le_half {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (right : Bool) (g : BitVec p) :
    count (ProgramGeneration.originalSource p as bs cs ds s 0) right g.toNat ≤
      2 ^ (if right then cs.length + ds.length else as.length + bs.length) := by
  rw [count_eq_counter hp]
  let task : ClassStreaming.Input :=
    (((m, s.toNat), ((as ++ bs).map BitVec.toNat, (cs ++ ds).map BitVec.toNat)), (p, g.toNat))
  have h := List.length_filter_le (ClassStreaming.accepts task right)
    (List.range (ClassStreaming.limit task right))
  have he : ClassStreaming.count task right ≤ ClassStreaming.limit task right := by
    simpa only [ClassStreaming.count_eq, ClassStreaming.records, List.length_map,
      List.length_range] using h
  cases right <;> simpa only [task, ClassStreaming.limit, ClassStreaming.sideInput,
    SortedMeet.inverseInput, ite_true, ite_false, Bool.false_eq_true, List.length_reverse,
    List.length_map, List.length_append] using he

/-- Every prefix of the count-only prepass has a derived physical table bound. It counts
binary populations and list framing, separately from internal callback workspace. -/
theorem table_prefix_wire {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (n : ℕ) (hn : n ≤ 2 ^ p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (encList (encPair encNat encNat) (((countStep input)^[n] (0, [])).2)).length ≤
      n * (4 * (as.length + bs.length) + 2 * (cs.length + ds.length) + 9) := by
  dsimp only
  rw [table_prefix, length_encList_reverse]
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let a := as.length + bs.length
  let b := cs.length + ds.length
  have wire (r : ℕ × ℕ)
      (hr : r ∈ (List.range n).map (fun g => (count input false g, count input true g))) :
      (recEncoding r).length ≤ 2 * a + b + 4 := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
    have hg' : g < 2 ^ p := (List.mem_range.mp hg).trans_le hn
    have hl := count_le_half hp as bs cs ds s false (BitVec.ofNat p g)
    have hr := count_le_half hp as bs cs ds s true (BitVec.ofNat p g)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg', ite_true, ite_false,
      Bool.false_eq_true] at hl hr
    have hleft : (encNat (count input false g)).length ≤ a + 1 := by
      have hpow : 2 ^ a < 2 ^ (a + 1) := by
        rw [pow_succ]; have h := Nat.two_pow_pos a; omega
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr (hl.trans_lt hpow)
    have hright : (encNat (count input true g)).length ≤ b + 1 := by
      have hpow : 2 ^ b < 2 ^ (b + 1) := by
        rw [pow_succ]; have h := Nat.two_pow_pos b; omega
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr (hr.trans_lt hpow)
    simp only [recEncoding, length_encPair]
    omega
  have hw := length_encList_le recEncoding
    ((List.range n).map (fun g => (count input false g, count input true g))) wire
  simp only [List.length_map, List.length_range] at hw
  exact hw.trans_eq (by dsimp only [a, b]; ring)

private theorem halfInput_polyTime : ComputableInPolyTime
    (fun q : Input × Bool => halfInput q.1 q.2) sideEncoding SortedMeet.encoding := by
  have width : ComputableInPolyTime (fun q : Input × Bool => q.1.1.1.1)
      sideEncoding encUnary := by dsimp only [sideEncoding, encoding]; fun_prop
  have seed : ComputableInPolyTime (fun q : Input × Bool => q.1.1.2.1)
      sideEncoding encNat := by dsimp only [sideEncoding, encoding]; fun_prop
  have target : ComputableInPolyTime (fun q : Input × Bool => q.1.1.2.2)
      sideEncoding encNat := by dsimp only [sideEncoding, encoding]; fun_prop
  have first : ComputableInPolyTime (fun q : Input × Bool => q.1.2.1.1)
      sideEncoding (encList encNat) := by dsimp only [sideEncoding, encoding]; fun_prop
  have second : ComputableInPolyTime (fun q : Input × Bool => q.1.2.1.2)
      sideEncoding (encList encNat) := by dsimp only [sideEncoding, encoding]; fun_prop
  have third : ComputableInPolyTime (fun q : Input × Bool => q.1.2.2.1)
      sideEncoding (encList encNat) := by dsimp only [sideEncoding, encoding]; fun_prop
  have fourth : ComputableInPolyTime (fun q : Input × Bool => q.1.2.2.2)
      sideEncoding (encList encNat) := by dsimp only [sideEncoding, encoding]; fun_prop
  have reflected := ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_pow' (.const 2) width) (.const 1)) target
  have left := (width.prod seed).prod (first.prod second)
  have reverse := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse encNat)
  have right := (width.prod reflected).prod ((reverse.comp fourth).prod (reverse.comp third))
  exact (ComputableInPolyTime.of_tidy ((ComputableTidilyInPolyTime.snd encoding encBool).cond
    right.tidy left.tidy)).of_enc_eq (fun _ => rfl)

private theorem queryInput_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × ℕ => queryInput q.1.1 q.1.2 q.2)
    taskEncoding ClassJoin.encoding := by
  have half := halfInput_polyTime.comp (ComputableInPolyTime.fst sideEncoding encNat)
  have dp : ComputableInPolyTime (fun q : (Input × Bool) × ℕ => q.1.1.1.1.2)
      taskEncoding encUnary := by dsimp only [taskEncoding, sideEncoding, encoding]; fun_prop
  have modulus := ComputableInPolyTime.binary_pow' (.const 2) dp
  have seed : ComputableInPolyTime (fun q : (Input × Bool) × ℕ => (halfInput q.1.1 q.1.2).1.2)
      taskEncoding encNat := (ComputableInPolyTime.snd _ _).comp
        ((ComputableInPolyTime.fst _ _).comp half)
  have mapped (right : Bool) : ComputableInPolyTime
      (fun q : (Input × Bool) × ℕ =>
        (if right then (halfInput q.1.1 q.1.2).2.2 else (halfInput q.1.1 q.1.2).2.1).map
          (· % 2 ^ q.1.1.1.1.2)) taskEncoding (encList encNat) := by
    have ops : ComputableInPolyTime
        (fun q : (Input × Bool) × ℕ =>
          if right then (halfInput q.1.1 q.1.2).2.2 else (halfInput q.1.1 q.1.2).2.1)
        taskEncoding (encList encNat) := by
      have select : ComputableInPolyTime
          (fun q : SortedMeet.Input => if right then q.2.2 else q.2.1)
          SortedMeet.encoding (encList encNat) := by
        cases right <;> dsimp only [SortedMeet.encoding] <;> fun_prop
      exact select.comp half
    have body := ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.snd taskEncoding encNat).prod
        (modulus.comp (ComputableInPolyTime.fst taskEncoding encNat)))
    exact .of_tidy (ops.tidy.mapWithInput body.tidy)
  have selected := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.snd sideEncoding encNat).prod modulus)
  have flipped := ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_sub'
    modulus (.const 1)) selected
  have choice : ComputableInPolyTime (fun q : (Input × Bool) × ℕ => q.1.2)
      taskEncoding encBool := by dsimp only [taskEncoding]; fun_prop
  have key := ComputableInPolyTime.of_tidy (choice.tidy.cond flipped.tidy selected.tidy)
  exact (((dp.prod (ComputableInPolyTime.binary_mod.comp (seed.prod modulus))).prod
    ((mapped false).prod (mapped true))).prod key).of_enc_eq (fun _ => rfl)

/-- Both class populations are computed by real projected-quarter joins. -/
noncomputable def countCertificate : NativeCertificate
    (fun q : (Input × Bool) × ℕ => count q.1.1 q.1.2 q.2)
    (encPair (encPair encoding encBool) encNat) encNat :=
  NativeCertificate.congr (ClassJoin.countCertificate.comp
    (NativeCertificate.ofPolyTime queryInput_polyTime)) (fun _ => rfl)

private theorem encode_eq_ofBits (bits : List Bool) : Native.Quarter.encode bits = ofBits bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp [Native.Quarter.encode, ofBits, ih, Nat.bit_val, Nat.mul_comm, Nat.add_comm]

private theorem record_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × (ℕ × ℕ) => record q.1.1 q.1.2 q.2)
    (encPair sideEncoding recEncoding) recEncoding := by
  let e := encPair sideEncoding recEncoding
  have half := halfInput_polyTime.comp (ComputableInPolyTime.fst sideEncoding recEncoding)
  have index := ComputableInPolyTime.snd sideEncoding recEncoding
  have bits := SortedMeet.decodeWitness_polyTime.comp (half.prod index)
  have encoded := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp bits.tidy)
  have params : ComputableInPolyTime
      (fun q : (Input × Bool) × (ℕ × ℕ) => (halfInput q.1.1 q.1.2).1)
      e (encPair encUnary encNat) := (ComputableInPolyTime.fst _ _).comp half
  have operands : ComputableInPolyTime
      (fun q : (Input × Bool) × (ℕ × ℕ) =>
        (halfInput q.1.1 q.1.2).2.1 ++ (halfInput q.1.1 q.1.2).2.2)
      e (encList encNat) := by
    have h : ComputableInPolyTime (fun q : SortedMeet.Input => q.2.1 ++ q.2.2)
        SortedMeet.encoding (encList encNat) := by dsimp only [SortedMeet.encoding]; fun_prop
    exact h.comp half
  have zipped := (ComputableInPolyTime.zip encBool encNat).comp
    (((bits_encList_polyTime encBool).1.comp bits).prod operands)
  have state := natEval_polyTime.comp (params.prod zipped)
  have width := (ComputableInPolyTime.fst encUnary encNat).comp params
  have reflect := ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_pow' (.const 2) width) (.const 1)) state
  have right : ComputableInPolyTime (fun q : (Input × Bool) × (ℕ × ℕ) => q.1.2) e encBool := by
    dsimp only [e]; fun_prop
  have value := ComputableInPolyTime.of_tidy (right.tidy.cond reflect.tidy state.tidy)
  exact (value.prod encoded).of_enc_eq (fun q => by
    simp only [record, encode_eq_ofBits, Function.comp_def])

private theorem emit_polyTime : ComputableInPolyTime
    (fun q : (Input × Bool) × (ℕ × ℕ) => [record q.1.1 q.1.2 q.2])
    (encPair sideEncoding recEncoding) (encList recEncoding) := by
  have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
      recEncoding (encList recEncoding) := .of_linear (.of_frame (fun _ => by simp))
  exact .of_tidy (single.comp record_polyTime.tidy)

private noncomputable def emitCertificate : NativeCertificate
    (fun q : (Input × Bool) × List (ℕ × ℕ) => q.2.map (record q.1.1 q.1.2))
    (encPair sideEncoding (encList recEncoding)) (encList recEncoding) := by
  let h := (Classical.choose_spec (ComputableInO.flatMap_stream emit_polyTime)).2.2
  exact ⟨_, _, h.of_enc_eq (fun q => by rw [List.map_eq_flatMap])⟩

/-- Generation, actual inverse queries, group joining, full-width evaluation and packed
readback form one uniform bit computation. All intermediate phase profiles are charged. -/
noncomputable def recordsCertificate : NativeCertificate
    (fun q : (Input × Bool) × ℕ => records q.1.1 q.1.2 q.2)
    (encPair (encPair encoding encBool) encNat) (encList (encPair encNat encNat)) := by
  let original : NativeCertificate (id : (Input × Bool) × ℕ → _) taskEncoding taskEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let query := NativeCertificate.ofPolyTime queryInput_polyTime
  let pairs := ClassJoin.witnessesCertificate.comp query
  exact NativeCertificate.congr (emitCertificate.comp (original.fst.prod pairs)) (fun _ => rfl)

private abbrev classEncoding := encPair encoding encNat

private noncomputable def countOn (right : Bool) : NativeCertificate
    (fun q : Input × ℕ => count q.1 right q.2) classEncoding encNat := by
  let original : NativeCertificate (id : Input × ℕ → _) classEncoding classEncoding :=
    .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (countCertificate.comp
    ((original.fst.prod (NativeCertificate.const (em := encBool) right)).prod original.snd))
      (fun _ => rfl)

private noncomputable def orientationCertificate : NativeCertificate
    (fun q : Input × ℕ => retainRight q.1 q.2) classEncoding encBool := by
  have test : ComputableInPolyTime (fun q : ℕ × ℕ => decide (q.2 < q.1)) recEncoding encBool := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.binary_lt' <;> fun_prop
  exact NativeCertificate.congr ((NativeCertificate.ofPolyTime test).comp
    ((countOn false).prod (countOn true))) (fun _ => rfl)

/-- Counts are computed before only the selected side is generated and retained. -/
noncomputable def retainCertificate : NativeCertificate
    (fun q : Input × ℕ => retain q.1 q.2) (encPair encoding encNat)
    (encList (encPair encNat encNat)) := by
  let original : NativeCertificate (id : Input × ℕ → _) classEncoding classEncoding :=
    .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (recordsCertificate.comp
    ((original.fst.prod orientationCertificate).prod original.snd)) (fun _ => rfl)

private theorem depth_polyTime : ComputableInPolyTime depth encoding encUnary := by
  have h : ComputableInPolyTime (fun q : Input => q.1.1.2) encoding encUnary := by
    dsimp only [encoding]; fun_prop
  exact h.of_enc_eq (fun _ => rfl)

private noncomputable def countStepCertificate : NativeCertificate
    (fun q : Input × (ℕ × List (ℕ × ℕ)) => countStep q.1 q.2)
    (encPair encoding (encPair encNat (encList recEncoding)))
    (encPair encNat (encList recEncoding)) := by
  let e := encPair encoding (encPair encNat (encList recEncoding))
  let original : NativeCertificate (id : Input × (ℕ × List (ℕ × ℕ)) → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let selected := original.fst.prod original.snd.fst
  let both := ((countOn false).comp selected).prod ((countOn true).comp selected)
  let counts := (both.prod original.snd.snd).post (ComputableInO.cons' (enc := recEncoding))
  have increment : ComputableInPolyTime (fun n : ℕ => n + 1) encNat encNat := by fun_prop
  let next := (NativeCertificate.ofPolyTime increment).comp original.snd.fst
  exact NativeCertificate.congr (next.prod counts) (fun _ => rfl)

/-- Actual finite-counter prepass for both directions, with table and control copying charged. -/
noncomputable def tableCertificate : NativeCertificate table encoding
    (encList (encPair encNat encNat)) := by
  have clock : ComputableInPolyTime (fun input : Input => 2 ^ depth input) encoding encNat :=
    ComputableInPolyTime.binary_pow' (.const 2) depth_polyTime
  let loop := ClassStreaming.loopCertificate encoding (encList recEncoding)
    (fun input => 2 ^ depth input) countStep [] clock countStepCertificate
  let reverse := NativeCertificate.ofPolyTime (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listReverse recEncoding))
  exact NativeCertificate.congr (reverse.comp loop) (fun _ => rfl)

private theorem minimum_polyTime : ComputableInPolyTime
    (fun q : ℕ × ℕ => min q.1 q.2) recEncoding encNat := by
  have choose : ComputableTidilyInPolyTime (fun q : ℕ × ℕ => decide (q.1 ≤ q.2))
      recEncoding encBool := by
    apply ComputableTidilyInPolyTime.binary_le' <;> fun_prop
  exact .of_tidy ((choose.cond (.fst _ _) (.snd _ _)).of_enc_eq (fun q => by
    by_cases h : q.1 ≤ q.2 <;> simp [h, Nat.min_def]))

private theorem maximum_polyTime : ComputableInPolyTime
    (fun q : ℕ × ℕ => max q.1 q.2) recEncoding encNat := by
  have choose : ComputableTidilyInPolyTime (fun q : ℕ × ℕ => decide (q.1 ≤ q.2))
      recEncoding encBool := by
    apply ComputableTidilyInPolyTime.binary_le' <;> fun_prop
  exact .of_tidy ((choose.cond (.snd _ _) (.fst _ _)).of_enc_eq (fun q => by
    by_cases h : q.1 ≤ q.2 <;> simp [h, Nat.max_def]))

/-- Count both directions and reduce their minimum directly into one scalar maximum.
The actual encoded streaming loop sums class costs and takes callback/prefix maxima;
no table construction, reversal or whole-table polynomial callback is executed. -/
noncomputable def balanceCertificate : NativeCertificate balance encoding encNat := by
  let e := encPair (encPair encoding encNat) encNat
  let original : NativeCertificate (id : (Input × ℕ) × ℕ → _) e e :=
    .linear (.of_eq (fun _ => rfl))
  let selected := original.fst.fst.prod original.snd
  let both := ((countOn false).comp selected).prod ((countOn true).comp selected)
  let smaller := (NativeCertificate.ofPolyTime minimum_polyTime).comp both
  let round := (NativeCertificate.ofPolyTime maximum_polyTime).comp (original.fst.snd.prod smaller)
  let loop := NativeCertificate.foldlStream encoding encNat encNat
    (fun input current g => max current (min (count input false g) (count input true g))) round
  let generation := (Classical.choose_spec SortedQuarterMachine.indices_computable).2.2
  let generated : NativeCertificate SortedQuarterMachine.indices encUnary (encList encNat) :=
    ⟨_, _, generation⟩
  let indices := generated.comp (NativeCertificate.ofPolyTime depth_polyTime)
  let input : NativeCertificate (id : Input → _) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  let initial : NativeCertificate (fun _ : Input => (0 : ℕ)) encoding encNat := .const 0
  exact NativeCertificate.congr (loop.comp (input.prod (initial.prod indices))) (fun input => by
    simp only [Function.comp_def, id_eq, SortedQuarterMachine.indices_eq_range]
    exact (balance_eq_prefix input).symm)

/-- Every scalar prepass prefix is bounded by the actual computed balance. This is derived
from the visited classes, rather than supplied as a loop resource invariant. -/
theorem balancePrefix_le (input : Input) (n : ℕ) (hn : n ≤ 2 ^ depth input) :
    balancePrefix input n ≤ balance input := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have old := ih (by omega)
    have current := class_le_balance input n (by omega)
    rw [retained_length] at current
    simp only [balancePrefix, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at *
    exact max_le old current

/-- The actual scalar accumulator has only half-word-count bit width at every prepass prefix.
This does not bound count callback workspace, which remains in `balanceCertificate`. -/
theorem balancePrefix_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (n : ℕ) (hn : n ≤ 2 ^ p) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    (encNat (balancePrefix input n)).length ≤ as.length + bs.length + 1 := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let a := as.length + bs.length
  have upper : balancePrefix input n ≤ 2 ^ a := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have old := ih (by omega)
      have hg : n < 2 ^ p := by omega
      have hc := count_le_half hp as bs cs ds s false (BitVec.ofNat p n)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg, Bool.false_eq_true, ite_false] at hc
      simp only [balancePrefix, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at *
      exact max_le old ((Nat.min_le_left _ _).trans hc)
  have hpow : 2 ^ a < 2 ^ (a+1) := by
    rw [pow_succ]; have h := Nat.two_pow_pos a; omega
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.size_le.mpr (upper.trans_lt hpow)

/-- One actual full-state class record has a width derived from original words and packed
half indices, even when values collide. -/
theorem record_wire {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (right : Bool) (g : BitVec p) (r : ℕ × ℕ)
    (hr : r ∈ records (ProgramGeneration.originalSource p as bs cs ds s 0) right g.toNat) :
    let q := as.length + bs.length + cs.length + ds.length
    (encPair encNat encNat r).length ≤ 2 * m + 1 + q := by
  let q := as.length + bs.length + cs.length + ds.length
  obtain ⟨hk, hv⟩ := records_fit hp as bs cs ds s 0 right g r hr
  have hkey : (encNat r.1).length ≤ m := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hk
  have hval : (encNat r.2).length ≤ q := by
    have hl : (if right then cs.length + ds.length
      else as.length + bs.length) ≤ q := by split <;> dsimp only [q] <;> omega
    have hsize := (Nat.size_le.mpr hv).trans hl
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using hsize
  simp only [length_encPair]
  omega

/-- Physical full-state/payload wire of either generated class prefix, in terms of its
actual record count. Internal producer workspace is separate. -/
theorem records_prefix_wire {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (right : Bool) (g : BitVec p) (j : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encList (encPair encNat encNat) ((records input right g.toNat).take j)).length ≤
      ((records input right g.toNat).take j).length * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  let q := as.length + bs.length + cs.length + ds.length
  have hrecord (r : ℕ × ℕ) (hr : r ∈ (records input right g.toNat).take j) :
      (recEncoding r).length ≤ 2 * m + 1 + q :=
    record_wire hp as bs cs ds s right g r (List.mem_of_mem_take hr)
  have hw := length_encList_le recEncoding ((records input right g.toNat).take j) hrecord
  exact hw.trans_eq (by ring)

/-- Full-state and packed-payload encoding of every retained prefix is bounded using the
actual computed balance. Internal producer/probe workspace is charged separately by certificates. -/
theorem retained_prefix_wire {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s : BitVec m) (g : BitVec p) (j : ℕ) :
    let input := ProgramGeneration.originalSource p as bs cs ds s 0
    let q := as.length + bs.length + cs.length + ds.length
    (encList (encPair encNat encNat) ((retain input g.toNat).take j)).length ≤
      balance input * (4 * m + 2 * q + 3) := by
  let input := ProgramGeneration.originalSource p as bs cs ds s 0
  have hw := records_prefix_wire hp as bs cs ds s (retainRight input g.toNat) g j
  have hg : g.toNat < 2 ^ depth input := g.isLt
  have hlen := retained_prefix input g.toNat j hg
  exact hw.trans (Nat.mul_le_mul_right _ hlen)

end Cslib.Cryptanalysis.AddXNOR.ClassBalance
