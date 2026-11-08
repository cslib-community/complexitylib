/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Contraction
public import Complexity.Logics.Propositional.CSP.Edge.DAG.External
public import Complexity.Logics.Propositional.CSP.Occurrence.Enumeration

/-!
# Choosing an actual external blossom attachment

The finite first-input/last-output selection in Lemma 44 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 21–22. The scan tests actual
two-port exchanges in the original tables. Its correctness supplies both no-shortcut guards;
no compatibility promise about an outside comparison labeling is assumed.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open DAG Finset

variable {F : CSP Table ℕ}

/-- Accessible actual arcs at the external port's original constraint. -/
@[expose] def accessibleArcs (f : OccurrenceLabeling F Bool) (arcs : List (Arc F))
    (x : Occurrence F) : List (Arc F) :=
  arcs.filter fun a => decide (x.1 = a.occurrence.1 ∧
    ValidLabeling Table.sem (pairFlip f x a.occurrence))

/-- Prefer the earliest accessible input; if none exists, use the latest accessible output.
Both folds are funded by the actual arc list, independently of binary variable names. -/
@[expose] def attachmentArc (f : OccurrenceLabeling F Bool) (arcs : List (Arc F))
    (x : Occurrence F) : Option (Arc F) :=
  let accessible := accessibleArcs f arcs x
  let inputs := accessible.filter Arc.incoming
  if h : inputs = [] then accessible.maxOn? Arc.time else some (inputs.minOn Arc.time h)

/-- The executable choice supplies exactly the local exchange and no-shortcut facts needed
to attach the outside port, in either orientation. -/
theorem attachmentArc_spec (f : OccurrenceLabeling F Bool) (arcs : List (Arc F))
    (x : Occurrence F) (hne : accessibleArcs f arcs x ≠ []) :
    ∃ a, attachmentArc f arcs x = some a ∧ a ∈ arcs ∧ x.1 = a.occurrence.1 ∧
      ValidLabeling Table.sem (pairFlip f x a.occurrence) ∧
      (∀ e ∈ arcs, e.incoming = true → e.occurrence.1 = x.1 → e.time < a.time →
        ¬ ValidLabeling Table.sem (pairFlip f e.occurrence x)) ∧
      (a.incoming = false → ∀ e ∈ arcs, x.1 = e.occurrence.1 → a.time < e.time →
        ¬ ValidLabeling Table.sem (pairFlip f x e.occurrence)) := by
  let as := accessibleArcs f arcs x
  let ins := as.filter Arc.incoming
  have hmem : ∀ a ∈ as, a ∈ arcs ∧ x.1 = a.occurrence.1 ∧
      ValidLabeling Table.sem (pairFlip f x a.occurrence) := by
    intro a ha
    exact ⟨(List.mem_filter.mp ha).1, of_decide_eq_true (List.mem_filter.mp ha).2⟩
  by_cases hi : ins = []
  · let a := as.maxOn Arc.time hne
    have ham : a ∈ as := List.maxOn_mem
    obtain ⟨ha, hxa, hv⟩ := hmem a ham
    refine ⟨a, ?_, ha, hxa, hv, ?_, ?_⟩
    · simp only [attachmentArc]
      change (if h : ins = [] then as.maxOn? Arc.time else
        some (ins.minOn Arc.time h)) = some a
      rw [dite_eq_left hi, List.maxOn?_eq_some_maxOn hne]
    · intro e he hei hex het hev
      have hm : e ∈ ins := List.mem_filter.mpr ⟨List.mem_filter.mpr
        ⟨he, by
          rw [decide_eq_true_eq]
          exact ⟨hex.symm, (pairFlip_comm f e.occurrence x) ▸ hev⟩⟩, hei⟩
      simp only [hi, List.not_mem_nil] at hm
    · intro _ e he hex het hev
      have hem : e ∈ as := List.mem_filter.mpr ⟨he, by simp [hex, hev]⟩
      have hle : e.time ≤ a.time := (List.le_apply_maxOn_iff hne).mpr ⟨e, hem, le_rfl⟩
      omega
  · let a := ins.minOn Arc.time hi
    have ham : a ∈ ins := List.minOn_mem
    obtain ⟨ha, hxa, hv⟩ := hmem a (List.mem_filter.mp ham).1
    have hai : a.incoming = true := (List.mem_filter.mp ham).2
    refine ⟨a, ?_, ha, hxa, hv, ?_, ?_⟩
    · simp only [attachmentArc]
      change (if h : ins = [] then as.maxOn? Arc.time else
        some (ins.minOn Arc.time h)) = some a
      rw [dite_eq_right hi]
    · intro e he hei hex het hev
      have hem : e ∈ ins := List.mem_filter.mpr ⟨List.mem_filter.mpr
        ⟨he, by
          rw [decide_eq_true_eq]
          exact ⟨hex.symm, (pairFlip_comm f e.occurrence x) ▸ hev⟩⟩, hei⟩
      have hle : a.time ≤ e.time := (List.apply_minOn_le_iff hi).mpr ⟨e, hem, le_rfl⟩
      omega
    · simp [hai]

/-- Every successful finite attachment scan permits completion of any cut ending at its
selected copy. All forbidden exchanges follow from the scan; they are not extra premises. -/
theorem valid_attachment_cut {f : OccurrenceLabeling F Bool} {arcs : List (Arc F)}
    {T : DAG F} (harcs : T.arcs = arcs.toFinset) (h : T.IsFDAG Table.sem f)
    (hp : T.PairedCopies) (hM : EdgeInstance.EvenConstraints Table.sem F)
    (x : Occurrence F) (hx : x.var ∉ T.vars)
    (hne : accessibleArcs f arcs x ≠ []) :
    ∃ a, attachmentArc f arcs x = some a ∧ a ∈ T.arcs ∧ x.1 = a.occurrence.1 ∧
      ∀ cs : Finset (Copy F), a.copy ∉ cs →
        ValidLabeling Table.sem (((T.cutAt cs a).attachPort
          ⟨x, a.time, !a.incoming⟩).flip f) := by
  obtain ⟨a, he, ha, hxa, hv, hbefore, hafter⟩ := attachmentArc_spec f arcs x hne
  have hat : a ∈ T.arcs := harcs ▸ List.mem_toFinset.mpr ha
  refine ⟨a, he, hat, hxa,
    fun cs hc => h.valid_complete_cut hp hM cs hat hc x hx hxa hv ?_ ?_⟩
  · intro e he hei hex het
    exact hbefore e (List.mem_toFinset.mp (harcs ▸ he)) hei hex het
  · intro hai e he hex het
    exact hafter hai e (List.mem_toFinset.mp (harcs ▸ he)) hex het

end Cslib.Logic.PL.CSP.Blossom
