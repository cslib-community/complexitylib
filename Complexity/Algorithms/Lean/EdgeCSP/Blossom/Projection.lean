/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Transport
import Mathlib.Data.List.GetD

/-!
# Projecting unchanged or singly changed internal labels

The two forward constructions in Lemma 42 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed p. 20, use either zero changed internal ports or one changed
internal port. The central row is respectively the reference one-hot row or the exact
touched-constraint indicator of that port. These are executable projections of actual labels.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset

variable {F : CSP Table ℕ}

/-- Internal agreement gives zero local deviations at every actual constraint. -/
theorem deviations_zero_of_agree (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (h : ∀ o : Occurrence F, o.var ∈ vs → g o = f o) (i : Fin F.length) :
    deviations (localTuple f i) (localTuple g i) (positions vs F[i.val].2) = 0 := by
  apply (deviations_eq_zero_iff _ _ _).mpr
  intro j hj
  have hjb := List.mem_range.mp (List.mem_filter.mp hj).1
  have hv := (mem_positions vs i ⟨j, hjb⟩).mp hj
  simpa [localTuple, hjb] using h ⟨i, ⟨j, hjb⟩⟩ hv

/-- One changed internal occurrence contributes one deviation at its original constraint and
zero at all other original constraints, regardless of repeated copied visits or table arity. -/
theorem deviations_of_one_flip (f g : OccurrenceLabeling F Bool) (vs : List ℕ)
    (e : Occurrence F) (hev : e.var ∈ vs)
    (h : ∀ o : Occurrence F, o.var ∈ vs → g o = if o = e then !(f o) else f o)
    (i : Fin F.length) :
    deviations (localTuple f i) (localTuple g i) (positions vs F[i.val].2) =
      if i = e.1 then 1 else 0 := by
  cases e with | mk ei ej =>
  by_cases hi : i = ei
  · subst i
    rw [ite_eq_left rfl]
    calc
      _ = (positions vs F[ei.val].2).count ej.val := by
        rw [List.count_eq_countP]
        apply List.countP_congr
        intro j hj
        have hjb := List.mem_range.mp (List.mem_filter.mp hj).1
        have hv := (mem_positions vs ei ⟨j, hjb⟩).mp hj
        have hh := h ⟨ei, ⟨j, hjb⟩⟩ hv
        have hgj : (localTuple g ei).getD j false = g ⟨ei, ⟨j, hjb⟩⟩ := by
          simp [localTuple, hjb]
        have hfj : (localTuple f ei).getD j false = f ⟨ei, ⟨j, hjb⟩⟩ := by
          simp [localTuple, hjb]
        rw [hgj, hfj, hh]
        by_cases hj0 : j = ej.val
        · simp [hj0]
        · have hne : (⟨ei, ⟨j, hjb⟩⟩ : Occurrence F) ≠ ⟨ei, ej⟩ := by
            intro heq
            exact hj0 (congrArg (fun o : Occurrence F => o.2.val) heq)
          simp [hne, hj0]
      _ = 1 := List.count_eq_one_of_mem
        (validPositions_eq_true.mp (validPositions_positions vs F[ei.val].2)).1
        ((mem_positions vs ei ej).mpr hev)
  · rw [ite_eq_right hi]
    apply (deviations_eq_zero_iff _ _ _).mpr
    intro j hj
    have hjb := List.mem_range.mp (List.mem_filter.mp hj).1
    have hov := (mem_positions vs i ⟨j, hjb⟩).mp hj
    have hne : (⟨i, ⟨j, hjb⟩⟩ : Occurrence F) ≠ ⟨ei, ej⟩ := by
      intro heq
      exact hi (congrArg Sigma.fst heq)
    simpa [localTuple, hjb, hne] using h ⟨i, ⟨j, hjb⟩⟩ hov

/-- Projection with the honest reference connector row. -/
@[expose] def projectZero (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling F Bool) : OccurrenceLabeling (contract f vs) Bool :=
  transport f vs g (fun _ => false) (oneHot (connectors F vs).length 0)

/-- Projection retaining exactly the touched constraint that owns one internal changed port. -/
@[expose] def projectOne (f : OccurrenceLabeling F Bool) (vs : List ℕ)
    (g : OccurrenceLabeling F Bool) (i : Fin F.length) : OccurrenceLabeling (contract f vs) Bool :=
  transport f vs g (fun j => decide (j = i)) ((touched F vs).map fun j => decide (j = i))

/-- Matching endpoint rows create no new connector defects. -/
theorem connectorDefects_matches (vs : List ℕ) (bits : Fin F.length → Bool) :
    connectorDefects F vs bits ((touched F vs).map bits) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨k, hk, _⟩ := List.mem_map.mp hv
  have hh := (List.mem_filter.mp hk).2
  have hread : ((touched F vs).map bits).getD k.val false = bits (touched F vs)[k.val] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using k.isLt), List.getElem_map]
  rw [hread] at hh
  simp at hh

/-- The indicated touched constraint supplies an actual accepted central exactly-one row. -/
theorem sem_touched_indicator (vs : List ℕ) (i : Fin F.length) (hi : i ∈ touched F vs) :
    (exactlyOne (connectors F vs)).sem
      ((touched F vs).map fun j => decide (j = i)) = true := by
  apply (sem_exactlyOne_eq_true _ _).mpr
  refine ⟨by simp, ?_⟩
  have he : ((touched F vs).map fun j => decide (j = i)).count true = (touched F vs).count i := by
    simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
    apply List.countP_congr
    intro j _
    by_cases hj : j = i <;> simp [hj]
  rw [he]
  exact List.count_eq_one_of_mem (nodup_touched F vs) hi

/-- Zero internal changes project to a valid actual contracted labeling. -/
theorem valid_projectZero {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hg : ValidLabeling sem g) (vs : List ℕ) (hne : touched F vs ≠ [])
    (h : ∀ o : Occurrence F, o.var ∈ vs → g o = f o) :
    ValidLabeling sem (projectZero f vs g) := by
  apply valid_transport hf hg vs (fun _ => false)
  · apply (sem_exactlyOne_eq_true _ _).mpr
    exact ⟨by simp [oneHot], count_true_oneHot (by
      simpa only [length_connectors] using List.length_pos_iff.mpr hne)⟩
  · intro i _
    rw [deviations_zero_of_agree f g vs h i]
    omega
  · intro i _
    simp [deviations_zero_of_agree f g vs h i]

/-- A single changed internal port projects to a valid contracted labeling whose fresh
connector endpoints all agree. The original outside labels may be arbitrary. -/
theorem valid_projectOne {f g : OccurrenceLabeling F Bool} (hf : ValidLabeling sem f)
    (hg : ValidLabeling sem g) (vs : List ℕ) (e : Occurrence F) (hev : e.var ∈ vs)
    (h : ∀ o : Occurrence F, o.var ∈ vs → g o = if o = e then !(f o) else f o) :
    ValidLabeling sem (projectOne f vs g e.1) := by
  have ht : e.1 ∈ touched F vs := (mem_touched vs e.1).mpr (by
    intro hn
    have hm := (mem_positions vs e.1 e.2).mpr hev
    simp only [hn, List.not_mem_nil] at hm)
  apply valid_transport hf hg vs (fun i => decide (i = e.1)) (sem_touched_indicator vs e.1 ht)
  · intro i _
    rw [deviations_of_one_flip f g vs e hev h i]
    split <;> omega
  · intro i _
    rw [deviations_of_one_flip f g vs e hev h i]
    by_cases hi : i = e.1 <;> simp [hi]

/-- The single-port projection creates no fresh defects; all surviving old defect values
are taken from the changed original labeling. -/
theorem defects_projectOne (hF : EdgeInstance F) (f g : OccurrenceLabeling F Bool)
    (vs : List ℕ) (i : Fin F.length) :
    defects (projectOne f vs g i) = defects g \ vs.toFinset := by
  rw [projectOne, defects_transport hF, connectorDefects_matches]
  simp

end Cslib.Logic.PL.CSP.Blossom
