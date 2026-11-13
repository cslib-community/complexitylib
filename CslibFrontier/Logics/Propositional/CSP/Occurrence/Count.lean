/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence
import Mathlib.Data.List.Basic

/-!
# Counted criterion for edge instances

A duplicate-free scope and exactly two global occurrences per occurring variable imply the
existing positional `EdgeInstance` condition. Constraint records may repeat: constraint indices,
rather than record equality, distinguish their two endpoints.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

omit [DecidableEq V] in
/-- A duplicate-free scope identifies an occurrence from its constraint and variable. -/
theorem Occurrence.eq_of_scope_nodup (hscope : ∀ c ∈ F, c.scope.Nodup)
    {o p : F.Occurrence} (hi : o.1 = p.1) (hv : o.var = p.var) : o = p := by
  rcases o with ⟨i, j⟩
  rcases p with ⟨k, l⟩
  change i = k at hi
  subst k
  have hn := hscope F[i.val] (List.getElem_mem i.isLt)
  have he : j = l := Fin.ext (hn.getElem_inj_iff.mp hv)
  subst l
  rfl

/-- Two total occurrences, with no repetition inside a scope, are exactly an edge's endpoints.
Only the actual variable list is counted; no finite universe or maximum name is required. -/
theorem edgeInstance_of_count_eq_two (hscope : ∀ c ∈ F, c.scope.Nodup)
    (hcount : ∀ v ∈ F.vars, F.vars.count v = 2) : EdgeInstance F := by
  intro o
  let records := F.occurrences.filter fun r => r.2.2 == o.var
  have hlen : records.length = 2 := by
    rw [← List.countP_eq_length_filter]
    have hc := hcount o.var o.var_mem
    rw [← map_occurrences F, List.count_eq_countP, List.countP_map] at hc
    simpa only [Function.comp_def] using hc
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a ∈ records := by rw [hab]; simp
  have hb : b ∈ records := by rw [hab]; simp
  have hne : a ≠ b := by
    have hn := F.occurrences_nodup.filter (fun r => r.2.2 == o.var)
    change records.Nodup at hn
    rw [hab] at hn
    simpa using hn
  obtain ⟨oa, hoa⟩ := mem_occurrences.mp (List.mem_filter.mp ha).1
  obtain ⟨ob, hob⟩ := mem_occurrences.mp (List.mem_filter.mp hb).1
  have hva : oa.var = o.var := by
    have hv : a.2.2 = o.var := by simpa only [beq_iff_eq] using (List.mem_filter.mp ha).2
    simpa only [← hoa, Occurrence.record] using hv
  have hvb : ob.var = o.var := by
    have hv : b.2.2 = o.var := by simpa only [beq_iff_eq] using (List.mem_filter.mp hb).2
    simpa only [← hob, Occurrence.record] using hv
  have honly (q : F.Occurrence) (hv : q.var = o.var) : q = oa ∨ q = ob := by
    have hq : q.record ∈ records :=
      List.mem_filter.mpr ⟨mem_occurrences.mpr ⟨q, rfl⟩, by simp [Occurrence.record, hv]⟩
    rw [hab] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq
    · exact .inl (Occurrence.record_injective (hq.trans hoa.symm))
    · exact .inr (Occurrence.record_injective (hq.trans hob.symm))
  have hneq : oa ≠ ob := fun he => hne (hoa.symm.trans ((congrArg Occurrence.record he).trans hob))
  rcases honly o rfl with rfl | rfl
  · refine ⟨ob, ?_, hvb.symm, honly⟩
    intro hi
    exact hneq (Occurrence.eq_of_scope_nodup hscope hi (hva.trans hvb.symm))
  · refine ⟨oa, ?_, hva.symm, ?_⟩
    · intro hi
      exact hneq (Occurrence.eq_of_scope_nodup hscope hi.symm (hva.trans hvb.symm))
    · intro q hv
      exact (honly q hv).symm

end Cslib.Logic.PL.CSP
