/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Forest.Program

/-!
# Exact chronological forest-search agreement

The finite program compiles the existing chronological forest search on every explicit-table
CSP with an exact-width occurrence buffer. No edge, validity, evenness, reachability or supplied
forest premise is used in this bridge.
-/

public section

namespace Cslib.Complexity.CSP.EdgeForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (Record encRecord labeling)

/-- Existing typed expansions represented using the shared positional record API. -/
@[expose] def workExpansion {F : CSP Table ℕ} (e : Forest.Expansion F) : WorkExpansion :=
  (e.input.record, e.outputs.map Occurrence.record)

/-- Existing newest-first logs represented without changing expansion or port order. -/
@[expose] def workLog {F : CSP Table ℕ} (es : Forest.Log F) : WorkLog :=
  es.map workExpansion

private theorem used_workLog {F : CSP Table ℕ} (es : Forest.Log F) :
    used (workLog es) = es.used.map Occurrence.record := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.input.record :: (e.outputs.map Occurrence.record ++ used (workLog es)) = _
    rw [Forest.Log.used, List.map_cons, List.map_append, ih]

private theorem children_workLog {F : CSP Table ℕ} (es : Forest.Log F) :
    children (workLog es) = es.children := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (e.outputs.map Occurrence.record).map (·.2.2) ++ children (workLog es) = _
    rw [ih, Forest.Log.children, List.map_map]
    rfl

private theorem visited_workLog {F : CSP Table ℕ} (rs : List ℕ) (es : Forest.Log F) (v : ℕ) :
    visited rs (workLog es) v = decide (es.Visited rs v) := by
  simp only [visited, children_workLog, Forest.Log.Visited]
  rfl

private theorem parentConstraint_workLog {F : CSP Table ℕ} (es : Forest.Log F) (v : ℕ) :
    parentConstraint (workLog es) v = (es.parent? v).map (fun p => p.output.1.val) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [parentConstraint, workLog] at ih
    simp only [parentConstraint, workLog, List.map_cons, List.flatMap_cons, workExpansion,
      List.find?_append, List.find?_map, Function.comp_def, Forest.Log.parent?]
    cases h : e.outputs.find? (fun o => o.var == v) with
    | none => simpa [Occurrence.record, h] using ih
    | some o => simp [Occurrence.record, h]

private theorem sameParent_workLog {F : CSP Table ℕ} (es : Forest.Log F) (v : ℕ)
    (i : Fin F.length) :
    parentConstraint (workLog es) v = some i.val ↔ es.SameParent v i := by
  rw [parentConstraint_workLog]
  unfold Forest.Log.SameParent
  cases es.parent? v <;> simp [Fin.val_inj]

private theorem root_workLog {F : CSP Table ℕ} (es : Forest.Log F) (v : ℕ) :
    root (workLog es) v = (es.ancestry v).walk.start := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih =>
    simp only [root, workLog] at ih
    simp only [root, workLog, List.map_cons, List.foldl_cons, workExpansion,
      List.find?_map, Function.comp_def, Forest.Log.ancestry]
    cases h : e.outputs.find? (fun o => o.var == v) <;>
      simp [Occurrence.record, h, ih, Walk.snoc]

/-- Finite roots agree in their full deterministic order, without semantic assumptions. -/
theorem roots_eq (input : Input) :
    roots input = Forest.roots (labeling input.body input.labels) := by
  simp only [roots, Forest.roots, occurrences_eq_map_incidenceList, List.filter_map,
    EdgeAugmenting.inconsistent_eq, List.map_map, Function.comp_def, Occurrence.record]
  rfl

/-- Global partner validity and positional scan order agree, even for invalid input labelings. -/
theorem partners_eq (input : Input) (a : Occurrence input.body)
    (hw : input.labels.length = (incidenceList input.body).length) :
    partners input a.record =
      (Forest.partners Table.sem (labeling input.body input.labels) a).map Occurrence.record := by
  unfold partners Forest.partners
  dsimp only [Occurrence.record]
  rw [occurrences_eq_map_incidenceList, List.filter_map]
  congr 2
  funext b
  have hf := EdgeAugmenting.labeling_flip input.labels [a, b] hw
  simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] at hf
  dsimp only [Function.comp_def, Occurrence.record]
  rw [← occurrences_eq_map_incidenceList]
  have haIndex := EdgeAugmenting.record_index a
  have hbIndex := EdgeAugmenting.record_index b
  simp only [Occurrence.record] at haIndex hbIndex
  simp only [haIndex, hbIndex, EdgeAugmenting.valid_eq, hf]
  by_cases hv : a.var = b.var
  · simp [hv]
  · have hab : a ≠ b := fun h => hv (congrArg Occurrence.var h)
    rw [DAG.pairFlip_eq _ hab]
    apply Bool.eq_iff_iff.mpr
    simp [Bool.and_eq_true, hv, Fin.val_inj]

private theorem scan_stopped (rs : List ℕ) (es : WorkLog) (a : Record)
    (os bs : List Record) (b : Record) :
    bs.foldl (scanStep rs es a) (os, some b) = (os, some b) := by
  induction bs with
  | nil => rfl
  | cons c bs ih => simpa only [List.foldl_cons, scanStep, Option.isSome_some, ite_true] using ih

/-- Exact first-meeting scan, including current-copy children and same-original-parent skips. -/
theorem scan_eq {F : CSP Table ℕ} (rs : List ℕ) (es : Forest.Log F) (a : Occurrence F)
    (os bs : List (Occurrence F)) :
    scan rs (workLog es) a.record (os.map Occurrence.record) (bs.map Occurrence.record) =
      match Forest.scan rs es a os bs with
      | .continued out => (out.map Occurrence.record, none)
      | .meeting out b => (out.map Occurrence.record, some b.record) := by
  induction bs generalizing os with
  | nil => rfl
  | cons b bs ih =>
    have hc : (a.record, os.map Occurrence.record) :: workLog es =
        workLog ((⟨a, os⟩ : Forest.Expansion F) :: es) := rfl
    have hvar : b.record.2.2 = b.var := rfl
    have hcon : a.record.1 = a.1.val := rfl
    by_cases hv : Forest.Log.Visited rs ((⟨a, os⟩ : Forest.Expansion F) :: es) b.var
    · by_cases hp : Forest.Log.SameParent ((⟨a, os⟩ : Forest.Expansion F) :: es) b.var a.1
      · simpa only [scan, List.map_cons, List.foldl_cons, scanStep, hc, hvar, hcon, visited_workLog,
          hv, decide_true, Bool.not_true, Bool.false_eq_true, Option.isSome_none, ite_false,
          sameParent_workLog, hp, ite_true, Forest.scan, not_true_eq_false] using ih os
      · simp only [scan, List.map_cons, List.foldl_cons, scanStep, hc, hvar, hcon, visited_workLog,
          hv, decide_true, Bool.not_true, Bool.false_eq_true, Option.isSome_none, ite_false,
          sameParent_workLog, hp, Forest.scan, not_true_eq_false]
        exact scan_stopped rs (workLog es) a.record _ _ _
    · simpa only [scan, List.map_cons, List.foldl_cons, scanStep, hc, hvar, hcon, visited_workLog,
        hv, decide_false, Bool.not_false, Option.isSome_none,
        Bool.false_eq_true, ite_false, ite_true, Forest.scan, not_false_eq_true,
        List.map_append, List.map_cons, List.map_nil] using ih (os ++ [b])

private theorem finishExpansion_workExpansion {F : CSP Table ℕ} (e : Forest.Expansion F) :
    finishExpansion F (workExpansion e) = codeExpansion e := by
  simp [finishExpansion, workExpansion, codeExpansion, List.map_map,
    EdgeAugmenting.record_index, Function.comp_def]

private theorem finishLog_workLog {F : CSP Table ℕ} (es : Forest.Log F) :
    (workLog es).map (finishExpansion F) = es.map codeExpansion := by
  simp [workLog, List.map_map, Function.comp_def, finishExpansion_workExpansion]

private theorem step_stopped (input : Input) (es : WorkLog) (rem : List Record)
    (event : Option Event) (n : ℕ) :
    (step input)^[n] (es, rem, some event) = (es, rem, some event) :=
  Function.iterate_fixed (by simp [step]) n

private theorem finish_exhausted (input : Input) (es : Forest.Log input.body)
    (rem : List Record) :
    finish input (workLog es, rem, some none) = some (code (.exhausted es)) := by
  simp [finish, finishLog_workLog, code]

private theorem finish_meeting (input : Input) (es : Forest.Log input.body)
    (rem : List Record) (a b : Occurrence input.body) (os : List (Occurrence input.body)) :
    finish input (workLog es, rem, some (some (a.record, os.map Occurrence.record, b.record))) =
      let m : Forest.Meeting input.body :=
        ⟨Forest.roots (labeling input.body input.labels), es, ⟨a, os⟩, b⟩
      some (code (if m.left.walk.start = m.right.walk.start
        then .blossom m else .augment m)) := by
  have he : (a.record, os.map Occurrence.record) = workExpansion ⟨a, os⟩ := rfl
  simp only [finish, Option.elim_some, he, finishExpansion_workExpansion,
    finishLog_workLog, EdgeAugmenting.record_index, roots_eq, root_workLog]
  simp only [Forest.Meeting.left, Forest.Meeting.right, Occurrence.record]
  by_cases h : (es.ancestry a.var).walk.start = (es.ancestry b.var).walk.start <;>
    simp only [h, ite_true, ite_false] <;> rfl

private theorem filter_remaining {F : CSP Table ℕ} (es : Forest.Log F)
    (a : Occurrence F) (os rem : List (Occurrence F)) :
    (rem.map Occurrence.record).filter
        (fun b => decide (b ∉ used (workLog ((⟨a, os⟩ : Forest.Expansion F) :: es)))) =
      (((rem.erase a).filter fun b =>
        decide (b ∉ Forest.Log.used ((⟨a, os⟩ : Forest.Expansion F) :: es))).map
          Occurrence.record) := by
  rw [used_workLog, List.filter_map]
  have hn : a ∉ rem.filter (fun b =>
      decide (b ∉ Forest.Log.used ((⟨a, os⟩ : Forest.Expansion F) :: es))) := by
    simp [Forest.Log.used]
  rw [← List.erase_filter, List.erase_of_not_mem hn]
  congr 2
  funext b
  simp only [Function.comp_def, List.mem_map, Occurrence.record_injective.eq_iff,
    exists_eq_right]

private theorem iterate_agrees (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length) (n : ℕ)
    (es : Forest.Log input.body) (rem : List (Occurrence input.body))
    (hlen : rem.length < n) :
    finish input ((step input)^[n] (workLog es, rem.map Occurrence.record, none)) =
      some (code (Forest.run Table.sem (labeling input.body input.labels)
        (Forest.roots (labeling input.body input.labels)) es rem)) := by
  induction n generalizing es rem with
  | zero => omega
  | succ n ih =>
    let rs := Forest.roots (labeling input.body input.labels)
    have hfind : (rem.map Occurrence.record).find?
        (fun a => visited (roots input) (workLog es) a.2.2) =
          (rem.find? (fun a => decide (es.Visited rs a.var))).map Occurrence.record := by
      rw [List.find?_map]
      simp only [visited_workLog, roots_eq, rs, Function.comp_def]
      rfl
    rw [Function.iterate_succ_apply]
    conv_rhs => rw [Forest.run]
    cases hn : rem.find? (fun a => decide (es.Visited rs a.var)) with
    | none =>
      have hs : step input (workLog es, rem.map Occurrence.record, none) =
          (workLog es, rem.map Occurrence.record, some none) := by
        simp only [step, Option.isSome_none, Bool.false_eq_true, ite_false, hfind, hn,
          Option.map_none, Option.elim_none]
      rw [hs, step_stopped, finish_exhausted]
    | some a =>
      have ha : a.record ∈ CSP.occurrences input.body := by
        rw [occurrences_eq_map_incidenceList]
        exact List.mem_map.mpr ⟨a, mem_incidenceList a, rfl⟩
      have hs := scan_eq rs es a []
        (Forest.partners Table.sem (labeling input.body input.labels) a)
      change scan (Forest.roots (labeling input.body input.labels)) _ _ _ _ = _ at hs
      rw [← roots_eq input] at hs
      simp only [List.map_nil] at hs
      cases hc : Forest.scan rs es a []
          (Forest.partners Table.sem (labeling input.body input.labels) a) with
      | continued os =>
        have hstep : step input (workLog es, rem.map Occurrence.record, none) =
            (workLog ((⟨a, os⟩ : Forest.Expansion input.body) :: es),
              (((rem.erase a).filter fun b => decide (b ∉ Forest.Log.used
                ((⟨a, os⟩ : Forest.Expansion input.body) :: es))).map Occurrence.record),
              none) := by
          simp only [hc] at hs
          simp only [step, Option.isSome_none, Bool.false_eq_true, ite_false, hfind, hn,
            Option.map_some, Option.elim_some, ha, ite_true, partners_eq input a hw, hs,
            Option.elim_none]
          exact congrArg (fun r =>
            (workLog ((⟨a, os⟩ : Forest.Expansion input.body) :: es), r, none))
              (filter_remaining es a os rem)
        rw [hstep]
        have hm := List.mem_of_find?_eq_some hn
        have he := List.length_erase_of_mem hm
        have hf := List.length_filter_le (fun b => decide (b ∉ Forest.Log.used
          ((⟨a, os⟩ : Forest.Expansion input.body) :: es))) (rem.erase a)
        have hp : 0 < rem.length := List.length_pos_of_mem hm
        have hlen' : ((rem.erase a).filter fun b => decide (b ∉ Forest.Log.used
            ((⟨a, os⟩ : Forest.Expansion input.body) :: es))).length < n := by omega
        have hi := ih ((⟨a, os⟩ : Forest.Expansion input.body) :: es) _ hlen'
        change Forest.scan (Forest.roots (labeling input.body input.labels)) _ _ _ _ = _ at hc
        simpa only [hn, hc] using hi
      | meeting os b =>
        have hstep : step input (workLog es, rem.map Occurrence.record, none) =
            (workLog es, rem.map Occurrence.record,
              some (some (a.record, os.map Occurrence.record, b.record))) := by
          simp only [hc] at hs
          simp only [step, Option.isSome_none, Bool.false_eq_true, ite_false, hfind, hn,
            Option.map_some, Option.elim_some, ha, ite_true, partners_eq input a hw, hs]
        rw [hstep, step_stopped, finish_meeting]
        change Forest.scan (Forest.roots (labeling input.body input.labels)) _ _ _ _ = _ at hc
        simp only [hc]

/-- Exact compilation of the existing chronological forest search on every raw explicit-table
CSP. Correct buffer width alone suffices; the finite clock never fails on such an input. -/
theorem run_eq (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length) :
    run input = some (code (Forest.search Table.sem (labeling input.body input.labels))) := by
  have ho := occurrences_eq_map_incidenceList input.body
  simp only [run, ho, List.length_map, hw, ite_true, Forest.search]
  exact iterate_agrees input hw _ [] (incidenceList input.body) (Nat.lt_succ_self _)

/-- Width mismatch is the only rejection: a correctly formed buffer never runs out of fuel. -/
theorem run_eq_none_iff (input : Input) :
    run input = none ↔ input.labels.length ≠ (incidenceList input.body).length := by
  constructor
  · intro hr hw
    rw [run_eq input hw] at hr
    cases hr
  · exact run_eq_none_of_length input

/-- Successful native output decodes to precisely the source result, with no supplied trace,
forest invariant, implementation or semantic oracle. -/
theorem decode_run (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length) :
    (run input).bind (decode input.body) =
      some (Forest.search Table.sem (labeling input.body input.labels)) := by
  rw [run_eq input hw, Option.bind_some, decode_code]

end Cslib.Complexity.CSP.EdgeForest
