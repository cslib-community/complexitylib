/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VariableCycleWords
import CslibFrontier.Logics.Propositional.CNF.ModelCount

/-!
# The occurrence partition of the actual variable cycle words

An accepted raw rotation partitions its variable-side darts into the exact cycle words
rooted at the first occurrence of each appearing name. Repeated names and duplicate rows keep
all their indexed positions. Empty instances produce an empty partition, independently of
the ambient variable type and the magnitude of any represented name.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V} {c : RotationCertificate}

/-- The bounded first-occurrence scans have exactly one occurrence of each variable dart. -/
theorem nodup_flatten_variableCycleWords
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    (F.distinctVars.flatMap fun v => RotationCertificate.cycleWord c
      (2 * F.vars.idxOf v)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun v hv => nodup_first_variable_cycleWord hc v (CSP.mem_distinctVars.mp hv), ?_⟩
  have hn : F.distinctVars.Nodup := by
    rw [← CSP.distinctVars_varCNF]
    exact CNF.nodup_distinctVars _
  apply hn.imp_of_mem
  intro v u hv hu hne
  apply List.disjoint_left.mpr
  intro index hv' hu'
  obtain ⟨o, ho, hov⟩ :=
    (mem_first_variable_cycleWord_iff hc v (CSP.mem_distinctVars.mp hv) index).mp hv'
  obtain ⟨p, hp, hpu⟩ :=
    (mem_first_variable_cycleWord_iff hc u (CSP.mem_distinctVars.mp hu) index).mp hu'
  have he : o = p := incidenceEdgeIndex_injective (by omega)
  exact hne (hov.symm.trans (he ▸ hpu))

/-- The complete variable-word partition covers exactly the even indices of actual source
occurrences. It neither discards repetitions nor scans a numeric range of variable names. -/
theorem mem_flatten_variableCycleWords_iff
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) (index : ℕ) :
    index ∈ (F.distinctVars.flatMap fun v => RotationCertificate.cycleWord c
      (2 * F.vars.idxOf v)) ↔ ∃ i < F.occurrences.length, index = 2 * i := by
  constructor
  · intro hm
    obtain ⟨v, hv, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨o, ho, _⟩ :=
      (mem_first_variable_cycleWord_iff hc v (CSP.mem_distinctVars.mp hv) index).mp hm
    refine ⟨incidenceEdgeIndex o, ?_, ho⟩
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨o, ho⟩ := exists_incidenceEdgeIndex (F := F) i
      (by simpa only [incidenceGraph_edges, List.length_map] using hi)
    apply List.mem_flatMap.mpr
    refine ⟨o.var, CSP.mem_distinctVars.mpr o.var_mem, ?_⟩
    exact (mem_first_variable_cycleWord_iff hc o.var o.var_mem _).mpr ⟨o, by rw [ho], rfl⟩

/-- Splicing blocks through the source's supplied clockwise cycles only reorders the actual
indexed source incidences. This includes singleton cycles and the empty source body. -/
theorem flatten_variableCycleWords_perm
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    (F.distinctVars.flatMap fun v => RotationCertificate.cycleWord c
      (2 * F.vars.idxOf v)).Perm ((List.range F.occurrences.length).map (2 * ·)) := by
  apply (List.perm_ext_iff_of_nodup (nodup_flatten_variableCycleWords hc)
    (List.nodup_range.map (fun _ _ he => by omega))).mpr
  intro index
  simp only [mem_flatten_variableCycleWords_iff hc, List.mem_map, List.mem_range, eq_comm]

end Cslib.Complexity.CSP
