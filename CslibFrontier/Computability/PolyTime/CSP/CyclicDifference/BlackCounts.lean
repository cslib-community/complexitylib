/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.FaceParity
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Count
import Mathlib.Data.List.Sigma

/-!
# Exact black-side occurrence accounting

Black scopes partition original argument positions once, retaining the original constraint
positions and cyclic argument order. No source well-formedness premise is needed for this fact.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table

variable {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (F : CSP Rel ℕ)

/-- Every original edge position occurs on the black side and no other name is introduced. -/
theorem mem_vars_blackConstraints (v : ℕ) :
    v ∈ (blackConstraints arity sem F).vars ↔ v < F.occurrences.length := by
  simp only [CSP.vars, blackConstraints, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨constraint, ⟨entry, he, rfl⟩, hv⟩
    obtain ⟨hi, hr⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp he).1)
    have hb := (blackScope_bounds (F := F) ⟨entry.2, hi⟩).2
    apply hb v
    simpa only [hr] using hv
  · intro hv
    obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) v (by
      simpa only [incidenceGraph_edges, List.length_map] using hv)
    refine ⟨(differenceTable arity sem F[o.1.val].1,
      blackScope F o.1 F[o.1.val].2), ?_, ?_⟩
    · refine ⟨(F[o.1.val], o.1.val), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem o.1.isLt)
      · have hp := Nat.zero_lt_of_lt o.2.isLt
        simpa using (List.ne_nil_of_length_pos hp)
    · rw [blackScope_eq_ofFn]
      exact List.mem_ofFn.mpr ⟨o.2, ho⟩

/-- Each actual black constraint has a duplicate-free scope. -/
theorem blackConstraints_scopes_nodup (constraint : Constraint Table ℕ)
    (hc : constraint ∈ blackConstraints arity sem F) : constraint.2.Nodup := by
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hi, hr⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp he).1)
  simpa only [hr] using (blackScope_bounds (F := F) ⟨entry.2, hi⟩).1

/-- Different original constraint positions have disjoint black scopes. -/
theorem nodup_vars_blackConstraints : (blackConstraints arity sem F).vars.Nodup := by
  let entries := F.zipIdx.filter fun entry => !entry.1.2.isEmpty
  have hz : F.zipIdx.Nodup := (List.nodup_zipIdx_map_snd F).of_map
  have hnd : entries.Nodup := hz.filter _
  simp only [blackConstraints, CSP.vars, List.flatMap_map]
  change (entries.flatMap (fun entry => blackScope F entry.2 entry.1.2)).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro entry he
    obtain ⟨hi, hr⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp he).1)
    simpa only [hr] using (blackScope_bounds (F := F) ⟨entry.2, hi⟩).1
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hei := List.mem_filter.mp (List.getElem_mem hi : entries[i] ∈ entries)
    have hej := List.mem_filter.mp (List.getElem_mem hj : entries[j] ∈ entries)
    obtain ⟨hci, hri⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp hei.1)
    obtain ⟨hcj, hrj⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp hej.1)
    apply List.disjoint_left.mpr
    intro v hvi hvj
    have hvi' : v ∈ blackScope F (entries[i]).2 F[(entries[i]).2].2 := by
      simpa only [hri] using hvi
    have hvj' : v ∈ blackScope F (entries[j]).2 F[(entries[j]).2].2 := by
      simpa only [hrj] using hvj
    rw [blackScope_eq_ofFn (⟨_, hci⟩ : Fin F.length)] at hvi'
    rw [blackScope_eq_ofFn (⟨_, hcj⟩ : Fin F.length)] at hvj'
    obtain ⟨a, ha⟩ := List.mem_ofFn.mp hvi'
    obtain ⟨b, hb⟩ := List.mem_ofFn.mp hvj'
    have he := incidenceEdgeIndex_injective (ha.trans hb.symm)
    have hindex := congrArg (fun o => o.1.val) he
    change (entries[i]).2 = (entries[j]).2 at hindex
    have hcEq : F[(entries[i]).2] = F[(entries[j]).2] :=
      congrArg F.get (Fin.ext hindex)
    have hrecord : entries[i] = entries[j] :=
      Prod.ext (hri.symm.trans (hcEq.trans hrj)) hindex
    have := hnd.getElem_inj_iff.mp hrecord
    omega

/-- Each old edge position occurs exactly once on the black side, including malformed sources. -/
theorem count_vars_blackConstraints (v : ℕ) :
    (blackConstraints arity sem F).vars.count v = if v < F.occurrences.length then 1 else 0 := by
  by_cases hv : v < F.occurrences.length
  · rw [ite_eq_left hv]
    exact List.count_eq_one_of_mem (nodup_vars_blackConstraints arity sem F)
      ((mem_vars_blackConstraints arity sem F v).mpr hv)
  · rw [ite_eq_right hv]
    exact List.count_eq_zero.mpr (fun hm => hv ((mem_vars_blackConstraints arity sem F v).mp hm))

end Cslib.Complexity.CSP.CyclicCompiler
