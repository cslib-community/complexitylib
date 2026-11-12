/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Defects
public import CslibFrontier.Logics.Propositional.CSP.Edge.Size
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting true endpoints in edge labelings

Each edge variable has two endpoint bits. It contributes two true endpoints when both bits
are true, one precisely when it is a defect, and zero otherwise. This elementary accounting
connects minimum-defect optimization to maximum-cardinality graph matching.
-/

public section

namespace Cslib.Logic.PL.CSP

open Finset

variable {Rel V : Type*} [DecidableEq V] {F : CSP Rel V}

omit [DecidableEq V] in
/-- Counting true incidences constraint by constraint preserves their total count. -/
theorem card_true_eq_sum_count (f : OccurrenceLabeling F Bool) :
    ((univ : Finset (Occurrence F)).filter fun o => f o = true).card =
      ∑ i : Fin F.length, (localTuple f i).count true := by
  classical
  simp only [card_eq_sum_ones, sum_filter, Fintype.sum_sigma, Occurrence, localTuple,
    List.count_eq_countP, List.countP_ofFn, beq_true]

/-- Actual occurring variables whose every endpoint is labeled true. -/
@[expose] def selectedVariables (f : OccurrenceLabeling F Bool) : Finset V :=
  F.vars.toFinset.filter fun v => ∀ o : Occurrence F, o.var = v → f o = true

@[simp] theorem mem_selectedVariables {f : OccurrenceLabeling F Bool} {v : V} :
    v ∈ selectedVariables f ↔ v ∈ F.vars ∧ ∀ o : Occurrence F, o.var = v → f o = true := by
  simp [selectedVariables]

/-- An edge is mutually selected iff both its endpoint labels are true. -/
theorem EdgeInstance.mem_selectedVariables_iff (hF : EdgeInstance F)
    (f : OccurrenceLabeling F Bool) (o : Occurrence F) :
    o.var ∈ selectedVariables f ↔ f o = true ∧ f (hF.partner o) = true := by
  rw [mem_selectedVariables, and_iff_right o.var_mem]
  constructor
  · intro h
    exact ⟨h o rfl, h _ (hF.partner_variable o).symm⟩
  · intro h p hp
    rcases hF.eq_or_eq_partner hp with rfl | rfl
    · exact h.1
    · exact h.2

/-- True endpoints split into twice the mutually selected edges and the defective edges. -/
theorem EdgeInstance.card_true_eq (hF : EdgeInstance F) (f : OccurrenceLabeling F Bool) :
    ((univ : Finset (Occurrence F)).filter fun o => f o = true).card =
      2 * (selectedVariables f).card + (defects f).card := by
  classical
  let T := (univ : Finset (Occurrence F)).filter fun o => f o = true
  have hfiber (v : V) (hv : v ∈ F.vars.toFinset) :
      (T.filter fun o => o.var = v).card =
        (if v ∈ selectedVariables f then 2 else 0) +
          (if v ∈ defects f then 1 else 0) := by
    obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hv)
    have he : T.filter (fun p => p.var = o.var) =
        ({o, hF.partner o} : Finset (Occurrence F)).filter fun p => f p = true := by
      ext p
      simp only [T, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · exact fun ⟨hp, hv⟩ => ⟨hF.eq_or_eq_partner hv, hp⟩
      · rintro ⟨rfl | rfl, hp⟩
        · exact ⟨hp, rfl⟩
        · exact ⟨hp, (hF.partner_variable o).symm⟩
    rw [he]
    simp only [hF.mem_selectedVariables_iff, mem_defects, hF.inconsistent_iff]
    have hn := hF.partner_ne o
    cases h₁ : f o <;> cases h₂ : f (hF.partner o) <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h₁, h₂, hn]
  have hsum : T.card = ∑ v ∈ F.vars.toFinset, (T.filter fun o => o.var = v).card :=
    card_eq_sum_card_fiberwise fun o _ => List.mem_toFinset.mpr o.var_mem
  rw [hsum, sum_congr rfl hfiber, sum_add_distrib]
  have hs : selectedVariables f ⊆ F.vars.toFinset := fun v hv =>
    List.mem_toFinset.mpr (mem_selectedVariables.mp hv).1
  have hd : defects f ⊆ F.vars.toFinset := by
    intro v hv
    obtain ⟨o, _, ho, _, _⟩ := mem_defects.mp hv
    exact List.mem_toFinset.mpr (ho ▸ o.var_mem)
  simp only [sum_ite_mem, inter_eq_right.mpr hs, inter_eq_right.mpr hd, sum_const,
    smul_eq_mul, mul_comm, Nat.one_mul]

end Cslib.Logic.PL.CSP
