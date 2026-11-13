/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Table
public import CslibFrontier.Computability.PolyTime.CSP.Occurrence
public import CslibFrontier.Logics.Propositional.CSP.Edge.Defects
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Enumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Mathlib.Data.List.ProdSigma
import CslibFrontier.Logics.Propositional.CNF.Occurrence

/-!
# Finite occurrence-label buffers

Shared positional buffer operations for native edge-CSP augmentation and forest search.
The namespace is retained from the augmentation API so existing imports and public names remain
available. Constraint and port positions are unary; original variable names are binary.
Every scan uses actual lists, including global validity on arbitrary explicit tables.
-/

public section

namespace Cslib.Complexity.CSP.EdgeAugmenting

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Positional occurrence records use unary constraint and scope positions and a binary name.
Both positions are framed; the name is the last field. -/
abbrev encRecord := encOccurrenceRecord encNat

/-- Positional constraint index, scope index and original variable name. -/
abbrev Record := ℕ × ℕ × ℕ

/-- A framed explicit-table CSP followed by its framed occurrence-bit buffer. -/
abbrev encBuffer := encPair (encCSP encTable encNat) (encList encBool)

/-- Global position in the actual incidence list, with no dependence on the variable's value. -/
@[expose] def occurrenceIndex {F : CSP Table ℕ} (o : Occurrence F) : ℕ :=
  (incidenceList F).idxOf o

/-- Read a finite buffer at an actual typed occurrence's global incidence-list position.
The default makes this total even for a short buffer. -/
@[expose] def labeling (F : CSP Table ℕ) (bits : List Bool) : OccurrenceLabeling F Bool :=
  fun o => bits.getD (occurrenceIndex o) false

/-- Read a positional record, defaulting to false outside the finite buffer. -/
@[expose] def readRecord (F : CSP Table ℕ) (bits : List Bool) (o : Record) : Bool :=
  bits.getD ((CSP.occurrences F).idxOf o) false

/-- Test every constraint against the complete finite labeling buffer. -/
@[expose] def valid (F : CSP Table ℕ) (bits : List Bool) : Bool :=
  F.zipIdx.all fun ⟨⟨table, scope⟩, constraint⟩ => table.sem
    (scope.zipIdx.map fun (vertex, port) => readRecord F bits (constraint, port, vertex))

/-- Test for unequal buffer bits at two actual occurrences of the requested variable. -/
@[expose] def inconsistent (F : CSP Table ℕ) (bits : List Bool) (v : ℕ) : Bool :=
  ((CSP.occurrences F).product (CSP.occurrences F)).any
    fun ((leftConstraint, leftPort, leftVariable), (rightConstraint, rightPort, rightVariable)) =>
      decide (leftVariable = v) && decide (rightVariable = v) &&
        (readRecord F bits (leftConstraint, leftPort, leftVariable) !=
          readRecord F bits (rightConstraint, rightPort, rightVariable))

/-- Flip precisely the selected global positions, preserving the buffer width. -/
@[expose] def flip (bits : List Bool) (indices : List ℕ) : List Bool :=
  bits.zipIdx.map fun a => if indices.contains a.2 then !a.1 else a.1

theorem poly_zipIdx {α β : Type} {e : α ↪ List Bool} {eb : β ↪ List Bool}
    {f : α → List β} (hf : ComputableInPolyTime f e (encList eb)) :
    ComputableInPolyTime (fun x => (f x).zipIdx) e (encList (encPair eb encUnary)) :=
  .of_tidy ((ComputableTidilyInPolyTime.zipIdx eb).comp hf.tidy)

theorem poly_product {α β : Type} (ea : α ↪ List Bool) (eb : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.product p.2)
      (encPair (encList ea) (encList eb)) (encList (encPair ea eb)) := by
  unfold List.product
  fun_prop

theorem poly_idxOf {α β : Type} [DecidableEq β]
    {e : α ↪ List Bool} {eb : β ↪ List Bool} {list : α → List β} {value : α → β}
    (hl : ComputableInPolyTime list e (encList eb))
    (hv : ComputableInPolyTime value e eb) :
    ComputableInPolyTime (fun x => (list x).idxOf (value x)) e encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.idxOfWithInput hl.tidy hv.tidy)

attribute [local fun_prop] poly_zipIdx poly_product poly_idxOf

theorem poly_records : ComputableInPolyTime (CSP.occurrences (Rel := Table) (V := ℕ))
    (encCSP encTable encNat) (encList encRecord) :=
  computableInPolyTime_occurrences encTable encNat

attribute [local fun_prop] poly_records

theorem poly_readRecord :
    ComputableInPolyTime (fun p : (CSP Table ℕ × List Bool) × Record =>
      readRecord p.1.1 p.1.2 p.2)
      (encPair encBuffer encRecord) encBool := by
  unfold readRecord
  have hindex : ComputableInPolyTime
      (fun p : (CSP Table ℕ × List Bool) × Record => (CSP.occurrences p.1.1).idxOf p.2)
      (encPair encBuffer encRecord) encUnary :=
    poly_idxOf (poly_records.comp (by fun_prop)) (by fun_prop)
  have hlist : ComputableInPolyTime
      (fun p : (CSP Table ℕ × List Bool) × Record => p.1.2)
      (encPair encBuffer encRecord)
      (encList encBool) := by fun_prop
  -- The realizing lookup saturates its binary index at the actual buffer length.
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary false hlist.tidy
    (ComputableTidilyInPolyTime.unary_to_binary.comp hindex.tidy))

attribute [local fun_prop] poly_readRecord

theorem poly_readWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {bits : α → List Bool} {o : α → Record}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hb : ComputableInPolyTime bits e (encList encBool))
    (ho : ComputableInPolyTime o e encRecord) :
    ComputableInPolyTime (fun x => readRecord (F x) (bits x) (o x)) e encBool :=
  poly_readRecord.comp ((hF.prod hb).prod ho)

theorem poly_semWith {α : Type} {e : α ↪ List Bool}
    {table : α → Table} {bits : α → List Bool}
    (ht : ComputableInPolyTime table e encTable)
    (hb : ComputableInPolyTime bits e (encList encBool)) :
    ComputableInPolyTime (fun x => (table x).sem (bits x)) e encBool :=
  computableInPolyTime_tableSem.comp (ht.prod hb)

attribute [local fun_prop] poly_readWith poly_semWith

theorem poly_valid :
    ComputableInPolyTime (fun p : CSP Table ℕ × List Bool => valid p.1 p.2)
      encBuffer encBool := by
  unfold valid
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  fun_prop

theorem poly_inconsistent :
    ComputableInPolyTime (fun p : (CSP Table ℕ × List Bool) × ℕ =>
      inconsistent p.1.1 p.1.2 p.2)
      (encPair encBuffer encNat) encBool := by
  unfold inconsistent
  apply ComputableInPolyTime.anyWithInput
  · exact (poly_product encRecord encRecord).comp
      ((poly_records.comp (by fun_prop)).prod (poly_records.comp (by fun_prop)))
  · fun_prop

/-- Work on bounded unary indices, with binary names unchanged. -/
abbrev encFlip := encPair (encList encBool) (encList encUnary)

theorem poly_flip :
    ComputableInPolyTime (fun p : List Bool × List ℕ => flip p.1 p.2)
      encFlip (encList encBool) := by
  unfold flip
  simp only [List.contains_eq_mem]
  fun_prop

theorem poly_validWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {bits : α → List Bool}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hb : ComputableInPolyTime bits e (encList encBool)) :
    ComputableInPolyTime (fun x => valid (F x) (bits x)) e encBool :=
  poly_valid.comp (hF.prod hb)

theorem poly_inconsistentWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {bits : α → List Bool} {v : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hv : ComputableInPolyTime v e encNat) :
    ComputableInPolyTime (fun x => inconsistent (F x) (bits x) (v x)) e encBool :=
  poly_inconsistent.comp ((hF.prod hb).prod hv)

attribute [local fun_prop] poly_valid poly_inconsistent poly_flip
attribute [local fun_prop] poly_validWith poly_inconsistentWith

theorem length_flip (bits : List Bool) (indices : List ℕ) :
    (flip bits indices).length = bits.length := by simp [flip]

theorem record_index {F : CSP Table ℕ} (o : Occurrence F) :
    (CSP.occurrences F).idxOf o.record = occurrenceIndex o := by
  rw [occurrences_eq_map_incidenceList]
  simp only [List.idxOf, List.findIdx_map, occurrenceIndex]
  congr 1
  funext p
  simp [Occurrence.record_injective.eq_iff]

theorem read_record {F : CSP Table ℕ} (bits : List Bool) (o : Occurrence F) :
    readRecord F bits o.record = labeling F bits o := by
  simp only [readRecord, record_index, labeling]

/-- Encoding a labeling as a positional buffer and reading it returns that labeling. -/
theorem labeling_map (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) :
    labeling F ((incidenceList F).map f) = f := by
  funext o
  simp [labeling, occurrenceIndex, mem_incidenceList o]

/-- An exact-width occurrence buffer is recovered by materializing its positional labeling
in incidence-list order. Width is the actual number of occurrences, not a declared arity. -/
theorem buffer_eq {F : CSP Table ℕ} (bits : List Bool)
    (hlen : bits.length = (incidenceList F).length) :
    bits = (incidenceList F).map (labeling F bits) := by
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have ho : i < (incidenceList F).length := by omega
    have he := (incidenceList_nodup F).idxOf_getElem i ho
    simp only [List.getElem_map, labeling, occurrenceIndex, he,
      List.getD_eq_getElem _ _ hi]

/-- Projection of an existing walk followed by positional decoding recovers its occurrences. -/
theorem getElem?_occurrenceIndex {F : CSP Table ℕ} (o : Occurrence F) :
    (incidenceList F)[occurrenceIndex o]? = some o := by
  simp [occurrenceIndex, mem_incidenceList o]

private theorem zipIdx_eq_ofFn {α : Type} (l : List α) :
    l.zipIdx = List.ofFn (fun i : Fin l.length => (l[i], i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem valid_eq (F : CSP Table ℕ) (bits : List Bool) :
    valid F bits = decide (ValidLabeling Table.sem (labeling F bits)) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change valid F bits = true ↔ ∀ i : Fin F.length,
    F[i].rel.sem (localTuple (labeling F bits) i) = true
  simp only [valid, List.all_eq_true, zipIdx_eq_ofFn, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, List.map_ofFn, Function.comp_def]
  have htuple (i : Fin F.length) :
      (List.ofFn fun j : Fin F[i].scope.length =>
        readRecord F bits (i.val, j.val, F[i].scope[j])) = localTuple (labeling F bits) i := by
    apply congrArg List.ofFn
    funext j
    exact read_record bits ⟨i, j⟩
  simp only [htuple]

theorem inconsistent_eq (F : CSP Table ℕ) (bits : List Bool) (v : ℕ) :
    inconsistent F bits v = decide (Inconsistent (labeling F bits) v) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  change inconsistent F bits v = true ↔ ∃ o p : Occurrence F,
    o.var = v ∧ p.var = v ∧ labeling F bits o ≠ labeling F bits p
  unfold inconsistent
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, hab, ht⟩
    obtain ⟨ha, hb⟩ := List.mem_product.mp hab
    rw [occurrences_eq_map_incidenceList] at ha hb
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hb
    change (decide (o.var = v) && decide (p.var = v) &&
      (readRecord F bits o.record != readRecord F bits p.record) = true) at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, read_record] at ht
    exact ⟨o, p, ht.1.1, ht.1.2, ht.2⟩
  · rintro ⟨o, p, ho, hp, hd⟩
    refine ⟨(o.record, p.record), List.mem_product.mpr ?_, ?_⟩
    · rw [occurrences_eq_map_incidenceList]
      exact ⟨List.mem_map.mpr ⟨o, mem_incidenceList o, rfl⟩,
        List.mem_map.mpr ⟨p, mem_incidenceList p, rfl⟩⟩
    · change (decide (o.var = v) && decide (p.var = v) &&
        (readRecord F bits o.record != readRecord F bits p.record) = true)
      simpa only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, read_record] using
        (show (o.var = v ∧ p.var = v) ∧ labeling F bits o ≠ labeling F bits p from ⟨⟨ho, hp⟩, hd⟩)


theorem occurrenceIndex_lt {F : CSP Table ℕ} (o : Occurrence F) :
    occurrenceIndex o < (incidenceList F).length :=
  List.idxOf_lt_length_iff.mpr (mem_incidenceList o)

theorem occurrenceIndex_injective (F : CSP Table ℕ) :
    Function.Injective (occurrenceIndex (F := F)) := by
  intro o p he
  have h := getElem?_occurrenceIndex o
  rw [he, getElem?_occurrenceIndex p] at h
  exact Option.some.inj h.symm

theorem labeling_flip {F : CSP Table ℕ} (bits : List Bool) (s : List (Occurrence F))
    (hlen : bits.length = (incidenceList F).length) :
    labeling F (flip bits (s.map occurrenceIndex)) =
      BitString.flipOn s.toFinset (labeling F bits) := by
  funext o
  have hi : occurrenceIndex o < bits.length := by rw [hlen]; exact occurrenceIndex_lt o
  have hf : occurrenceIndex o < (flip bits (s.map occurrenceIndex)).length := by
    simpa only [length_flip] using hi
  rw [labeling, List.getD_eq_getElem _ _ hf]
  simp only [flip, List.getElem_map, List.getElem_zipIdx, BitString.flipOn_apply,
    List.mem_toFinset, labeling, List.getD_eq_getElem _ _ hi, List.contains_eq_mem,
    List.mem_map, (occurrenceIndex_injective F).eq_iff, exists_eq_right,
    decide_eq_true_eq, Nat.zero_add]


end Cslib.Complexity.CSP.EdgeAugmenting
