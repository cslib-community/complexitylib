/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Attachment
public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Structure

/-!
# Actual blossom arms ending at an external port

These candidates are the two portions of the original incidence cycle used in Lemma 44 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 21–22. They retain repeated
original constraints. Only the boundary incidence is replaced by the actual outside port.
The cut/completion proof is an original alternative to the source's separate attachment cases;
it retains all six f-DAG invariants and the same first-input/last-output choice.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open DAG Finset

variable {F : CSP Table ℕ} {w : Walk F}

/-- The prefix arm stops at the selected input and exits through the outside port. -/
@[expose] def inputArm (w : Walk F) (j : Fin w.steps.length) (x : Occurrence F) : Walk F :=
  (w.take j.val).snoc w.steps[j.val].1 x

/-- The other arm traverses the suffix backwards, then exits at the selected output. -/
@[expose] def outputArm (w : Walk F) (j : Fin w.steps.length) (x : Occurrence F) : Walk F :=
  (w.drop (j.val + 1)).reverse.snoc w.steps[j.val].2 x

private theorem boundary_ne_external {x o : Occurrence F} (hx : x.var ∉ internal w)
    (ho : o ∈ w.edges) : o ≠ x := by
  intro he
  exact hx (List.mem_dedup.mpr (List.mem_map.mpr ⟨o, ho, congrArg Occurrence.var he⟩))

private theorem external_not_mem {x : Occurrence F} (hx : x.var ∉ internal w) :
    x ∉ w.edges := fun he => boundary_ne_external hx he rfl

/-- The prefix candidate is an actual linked trail, with unchanged base and external endpoint. -/
theorem inputArm_isWalk (hw : w.IsWalk) (j : Fin w.steps.length) (x : Occurrence F)
    (hx : x.var ∉ internal w) (hc : let (input, _) := w.steps[j.val]; input.1 = x.1) :
    (inputArm w j x).IsWalk ∧ (inputArm w j x).start = w.start ∧
      (inputArm w j x).finish = x.var := by
  have hstep : w.steps[j.val].1 ∈ w.edges := List.mem_flatMap.mpr
    ⟨w.steps[j.val], List.getElem_mem j.isLt, by simp⟩
  have hl := (hw.drop j.val).1
  change Walk.Linked (w.take j.val).finish (w.steps.drop j.val) at hl
  rw [List.drop_eq_getElem_cons j.isLt] at hl
  have hn := (hw.take (j.val + 1)).2
  change (Walk.edgesOf (w.steps.take (j.val + 1))).Nodup at hn
  rw [List.take_succ_eq_append_getElem j.isLt, Walk.edgesOf_append] at hn
  have hno : w.steps[j.val].1 ∉ (w.take j.val).edges := by
    intro he
    exact (List.nodup_append.mp hn).2.2 _ he _ (by simp [Walk.edgesOf]) rfl
  have hnx : x ∉ (w.take j.val).edges := by
    intro he
    exact external_not_mem hx ((List.take_sublist j.val w.steps).flatMap
      (fun s => [s.1, s.2]) |>.subset he)
  exact ⟨(hw.take j.val).snoc hl.1 hc (boundary_ne_external hx hstep) hno hnx, rfl, by
    simp [inputArm, Walk.snoc, Walk.finish, Walk.finishFrom_append, Walk.finishFrom]⟩

/-- The reverse-suffix candidate is an actual linked trail with the same base and endpoint. -/
theorem outputArm_isWalk (hw : w.IsWalk) (hclosed : w.finish = w.start)
    (j : Fin w.steps.length) (x : Occurrence F) (hx : x.var ∉ internal w)
    (hc : let (_, output) := w.steps[j.val]; output.1 = x.1) :
    (outputArm w j x).IsWalk ∧ (outputArm w j x).start = w.start ∧
      (outputArm w j x).finish = x.var := by
  have hstep : w.steps[j.val].2 ∈ w.edges := List.mem_flatMap.mpr
    ⟨w.steps[j.val], List.getElem_mem j.isLt, by simp⟩
  have ho : w.steps[j.val].2.var = (w.drop (j.val + 1)).reverse.finish := by
    rw [Walk.finish_reverse _ (hw.drop (j.val + 1)).1]
    exact (Walk.finish_take_succ w j.isLt).symm
  have hn := (hw.drop j.val).2
  change (Walk.edgesOf (w.steps.drop j.val)).Nodup at hn
  rw [List.drop_eq_getElem_cons j.isLt, Walk.edgesOf_cons] at hn
  have hno : w.steps[j.val].2 ∉ (w.drop (j.val + 1)).reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hnx : x ∉ (w.drop (j.val + 1)).reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    intro he
    exact external_not_mem hx ((List.drop_sublist (j.val + 1) w.steps).flatMap
      (fun s => [s.1, s.2]) |>.subset he)
  refine ⟨(hw.drop (j.val + 1)).reverse.snoc ho hc
    (boundary_ne_external hx hstep) hno hnx, ?_, ?_⟩
  · change (w.drop (j.val + 1)).finish = w.start
    rw [Walk.finish_drop, hclosed]
  · simp [outputArm, Walk.snoc, Walk.finish, Walk.finishFrom_append, Walk.finishFrom]

/-- Completing the graph cut of a prefix flips exactly the executable prefix arm. -/
theorem inputArm_flip {ts : List ℕ} {pivot : ℕ} (hw : w.IsWalk)
    (hd : w.DistinctCopies ts) (h : (blossomDAG w ts pivot).Supported)
    (j : Fin w.steps.length) (x : Occurrence F) (f : OccurrenceLabeling F Bool) :
    let a : Arc F := ⟨w.steps[j.val].1, ts[j.val]'(by have := hd.1; omega),
      decide (j.val < pivot)⟩
    (((blossomDAG w ts pivot).cutAt
      (blossomDAG (w.take j.val) (ts.take j.val) pivot).copies a).attachPort
        ⟨x, a.time, !a.incoming⟩).flip f = (inputArm w j x).flip f := by
  dsimp only
  have hp := blossomDAG_pairedCopies hw hd (pivot := pivot)
  have hq := blossomDAG_pairedCopies (hw.take j.val) (hd.take j.val) (pivot := pivot)
  have hs := blossomDAG_take_subgraph h j.val
  have ha := List.mem_toFinset.mpr (blossomArcs_get_mem hd.1 pivot j.val j.isLt).1
  change (⟨w.steps[j.val].1, ts[j.val]'(by have := hd.1; omega),
    decide (j.val < pivot)⟩ : Arc F) ∈ (blossomDAG w ts pivot).arcs at ha
  unfold DAG.flip
  simp only [attachPort]
  rw [cutAt_arcs hp hq hs (blossomDAG_supported _ _ _) ha,
    Finset.image_insert, Finset.image_insert,
    blossomDAG_occurrences _ _ pivot (hd.take j.val).1]
  apply congrArg (fun es => BitString.flipOn es f)
  change insert x (insert w.steps[j.val].1 (w.take j.val).edges.toFinset) =
    (Walk.edgesOf ((w.take j.val).steps ++ [(w.steps[j.val].1, x)])).toFinset
  rw [Walk.edgesOf_append]
  change insert x (insert w.steps[j.val].1 (w.take j.val).edges.toFinset) =
    ((w.take j.val).edges ++ [w.steps[j.val].1, x]).toFinset
  ext o
  simp only [mem_insert, List.mem_toFinset, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Completing the graph cut of a suffix flips exactly the executable reverse-suffix arm. -/
theorem outputArm_flip {ts : List ℕ} {pivot : ℕ} (hw : w.IsWalk)
    (hd : w.DistinctCopies ts) (h : (blossomDAG w ts pivot).Supported)
    (j : Fin w.steps.length) (x : Occurrence F) (f : OccurrenceLabeling F Bool) :
    let a : Arc F := ⟨w.steps[j.val].2, ts[j.val]'(by have := hd.1; omega),
      decide (pivot ≤ j.val + 1)⟩
    (((blossomDAG w ts pivot).cutAt
      (blossomDAG (w.drop (j.val + 1)) (ts.drop (j.val + 1))
        (pivot - (j.val + 1))).copies a).attachPort
          ⟨x, a.time, !a.incoming⟩).flip f = (outputArm w j x).flip f := by
  dsimp only
  have hp := blossomDAG_pairedCopies hw hd (pivot := pivot)
  have hq := blossomDAG_pairedCopies (hw.drop (j.val + 1)) (hd.drop (j.val + 1))
    (pivot := pivot - (j.val + 1))
  have hs := blossomDAG_drop_subgraph hd.1 h (j.val + 1)
  have ha := List.mem_toFinset.mpr (blossomArcs_get_mem hd.1 pivot j.val j.isLt).2
  change (⟨w.steps[j.val].2, ts[j.val]'(by have := hd.1; omega),
    decide (pivot ≤ j.val + 1)⟩ : Arc F) ∈ (blossomDAG w ts pivot).arcs at ha
  unfold DAG.flip
  simp only [attachPort]
  rw [cutAt_arcs hp hq hs (blossomDAG_supported _ _ _) ha,
    Finset.image_insert, Finset.image_insert,
    blossomDAG_occurrences _ _ (pivot - (j.val + 1)) (hd.drop (j.val + 1)).1]
  apply congrArg (fun es => BitString.flipOn es f)
  change insert x (insert w.steps[j.val].2 (w.drop (j.val + 1)).edges.toFinset) =
    (Walk.edgesOf ((w.drop (j.val + 1)).reverse.steps ++ [(w.steps[j.val].2, x)])).toFinset
  rw [Walk.edgesOf_append]
  change insert x (insert w.steps[j.val].2 (w.drop (j.val + 1)).edges.toFinset) =
    ((w.drop (j.val + 1)).reverse.edges ++ [w.steps[j.val].2, x]).toFinset
  rw [Walk.edges_reverse]
  ext o
  simp only [mem_insert, List.mem_toFinset, List.mem_append, List.mem_reverse,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Two actual arm candidates per step at the outside port's original constraint. -/
@[expose] def armCandidates (w : Walk F) (x : Occurrence F) : List (Walk F) :=
  (List.finRange w.steps.length).flatMap fun j =>
    if w.steps[j.val].1.1 = x.1 then [inputArm w j x, outputArm w j x] else []

/-- The scan retains exactly the two arms at matching original constraints. -/
theorem mem_armCandidates (x : Occurrence F) (p : Walk F) :
    p ∈ armCandidates w x ↔ ∃ j : Fin w.steps.length,
      let (input, _) := w.steps[j.val]
      input.1 = x.1 ∧ (p = inputArm w j x ∨ p = outputArm w j x) := by
  simp [armCandidates, List.mem_flatMap, List.mem_finRange]

/-- Every scanned candidate is an actual trail from the blossom base to the outside variable. -/
theorem armCandidates_isWalk (hw : w.IsWalk) (hclosed : w.finish = w.start)
    {x : Occurrence F} (hx : x.var ∉ internal w) {p : Walk F} (hp : p ∈ armCandidates w x) :
    p.IsWalk ∧ p.start = w.start ∧ p.finish = x.var := by
  obtain ⟨j, hc, rfl | rfl⟩ := (mem_armCandidates x p).mp hp
  · exact inputArm_isWalk hw j x hx hc
  · have hl := linked_constraint hw.1 (List.getElem_mem j.isLt)
    change w.steps[j.val].1.1 = w.steps[j.val].2.1 at hl
    exact outputArm_isWalk hw hclosed j x hx (hl.symm.trans hc)

/-- A feasible exchange from an outside port into the blossom always yields one valid actual
arm. The proof uses the selected copied node and the full f-DAG no-shortcut invariant. -/
theorem exists_valid_arm {f : OccurrenceLabeling F Bool} (hb : w.IsBlossom Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) (x : Occurrence F)
    (hx : x.var ∉ internal w)
    (hex : ∃ o ∈ w.edges, x.1 = o.1 ∧ ValidLabeling Table.sem (pairFlip f x o)) :
    ∃ p ∈ armCandidates w x, ValidLabeling Table.sem (p.flip f) := by
  obtain ⟨ts, pivot, hd, _, _, h0⟩ := hb.2.2.2.2.2
  have h : (blossomDAG w ts pivot).IsFDAG Table.sem f := by
    have hi : Classical.decEq ℕ = instDecidableEqNat := Subsingleton.elim _ _
    exact congrArg (fun d => @blossomDAG Table ℕ F d w ts pivot) hi ▸ h0
  have hxT : x.var ∉ (blossomDAG w ts pivot).vars := by
    rw [blossomDAG_vars w ts pivot hd.1]
    intro hm
    rcases mem_insert.mp hm with hxs | hm
    · exact hx (hxs ▸ List.mem_dedup.mpr (hb.1.start_mem_vars hb.2.2.1))
    · exact hx (List.mem_dedup.mpr (List.mem_toFinset.mp hm))
  have hacc : accessibleArcs f (blossomArcs w.steps ts pivot) x ≠ [] := by
    obtain ⟨o, ho, hxo, hv⟩ := hex
    have hom : o ∈ (blossomDAG w ts pivot).arcs.image Arc.occurrence := by
      rw [blossomDAG_occurrences _ _ _ hd.1]
      exact List.mem_toFinset.mpr ho
    obtain ⟨a, ha, he⟩ := mem_image.mp hom
    have haa : a ∈ accessibleArcs f (blossomArcs w.steps ts pivot) x :=
      List.mem_filter.mpr ⟨List.mem_toFinset.mp ha, by
        simp only [decide_eq_true_eq]
        exact he ▸ ⟨hxo, hv⟩⟩
    exact List.ne_nil_of_mem haa
  obtain ⟨a, _, ha, hac, hcuts⟩ := valid_attachment_cut rfl h
    (blossomDAG_pairedCopies hb.1 hd) hM x hxT hacc
  obtain ⟨j, hj, he⟩ := blossomArcs_mem hd.1 (List.mem_toFinset.mp ha)
  have hl := linked_constraint hb.1.1 (List.getElem_mem hj)
  change w.steps[j].1.1 = w.steps[j].2.1 at hl
  rcases he with rfl | rfl
  · let k : Fin w.steps.length := ⟨j, hj⟩
    refine ⟨inputArm w k x, (mem_armCandidates x _).mpr ⟨k, hac.symm, Or.inl rfl⟩, ?_⟩
    have hv := hcuts (blossomDAG (w.take j) (ts.take j) pivot).copies
      (blossomDAG_copy_not_take hb.1 hd pivot j hj)
    rw [← inputArm_flip (pivot := pivot) hb.1 hd h.supported k x f]
    exact hv
  · let k : Fin w.steps.length := ⟨j, hj⟩
    refine ⟨outputArm w k x,
      (mem_armCandidates x _).mpr ⟨k, hl.trans hac.symm, Or.inr rfl⟩, ?_⟩
    have hc : (⟨w.steps[j].2, ts[j]'(by have := hd.1; omega),
        decide (pivot ≤ j + 1)⟩ : Arc F).copy =
        (w.steps[j].1.1, ts[j]'(by have := hd.1; omega)) :=
      congrArg (fun i : Fin F.length => (i, ts[j]'(by have := hd.1; omega))) hl.symm
    have hv := hcuts (blossomDAG (w.drop (j + 1)) (ts.drop (j + 1))
      (pivot - (j + 1))).copies (hc ▸ blossomDAG_copy_not_drop hb.1 hd
        (pivot - (j + 1)) j hj)
    rw [← outputArm_flip (pivot := pivot) hb.1 hd h.supported k x f]
    exact hv

/-- Construct an actual valid arm by scanning at most two candidates per cycle step. -/
@[expose] def attachmentWalk (f : OccurrenceLabeling F Bool) (w : Walk F)
    (x : Occurrence F) : Option (Walk F) :=
  (armCandidates w x).find? fun p => decide (ValidLabeling Table.sem (p.flip f))

/-- The returned finite walk is valid and really runs from the old base to the outside port.
Existence follows from the six-invariant blossom proof, not a lifting oracle. -/
theorem attachmentWalk_spec {f : OccurrenceLabeling F Bool} (hb : w.IsBlossom Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) (x : Occurrence F)
    (hx : x.var ∉ internal w)
    (hex : ∃ o ∈ w.edges, x.1 = o.1 ∧ ValidLabeling Table.sem (pairFlip f x o)) :
    ∃ p, attachmentWalk f w x = some p ∧ p ∈ armCandidates w x ∧
      p.IsWalk ∧ p.start = w.start ∧ p.finish = x.var ∧
        ValidLabeling Table.sem (p.flip f) := by
  obtain ⟨q, hq, hv⟩ := exists_valid_arm hb hM x hx hex
  cases he : attachmentWalk f w x with
  | none =>
    have hn := List.find?_eq_none.mp he q hq
    exact (hn (by simpa only [decide_eq_true_eq] using hv)).elim
  | some p =>
    have hfind : (armCandidates w x).find? (fun q =>
        decide (ValidLabeling Table.sem (q.flip f))) = some p := he
    have hp := List.mem_of_find?_eq_some hfind
    have hpv := List.find?_some hfind
    obtain ⟨hw, hs, hf⟩ := armCandidates_isWalk hb.1 hb.2.1 hx hp
    exact ⟨p, rfl, hp, hw, hs, hf, of_decide_eq_true hpv⟩

/-- Every arm uses old blossom incidences and its one actual external boundary port only. -/
theorem armCandidates_edges {x : Occurrence F} {p : Walk F} (hp : p ∈ armCandidates w x)
    {o : Occurrence F} (ho : o ∈ p.edges) : o = x ∨ o ∈ w.edges := by
  obtain ⟨j, _, rfl | rfl⟩ := (mem_armCandidates x p).mp hp
  · change o ∈ Walk.edgesOf ((w.take j.val).steps ++ [(w.steps[j.val].1, x)]) at ho
    rw [Walk.edgesOf_append] at ho
    change o ∈ (w.take j.val).edges ++ [w.steps[j.val].1, x] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact Or.inr ((List.take_sublist j.val w.steps).flatMap
        (fun s => [s.1, s.2]) |>.subset ho)
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inr (List.mem_flatMap.mpr ⟨w.steps[j.val], List.getElem_mem j.isLt, by simp⟩)
      · exact Or.inl (List.mem_singleton.mp ho)
  · change o ∈ Walk.edgesOf ((w.drop (j.val + 1)).reverse.steps ++
      [(w.steps[j.val].2, x)]) at ho
    rw [Walk.edgesOf_append] at ho
    change o ∈ (w.drop (j.val + 1)).reverse.edges ++ [w.steps[j.val].2, x] at ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [Walk.edges_reverse, List.mem_reverse] at ho
      exact Or.inr ((List.drop_sublist (j.val + 1) w.steps).flatMap
        (fun s => [s.1, s.2]) |>.subset ho)
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inr (List.mem_flatMap.mpr ⟨w.steps[j.val], List.getElem_mem j.isLt, by simp⟩)
      · exact Or.inl (List.mem_singleton.mp ho)

end Cslib.Logic.PL.CSP.Blossom
