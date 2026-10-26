/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Incidence
public import Complexity.Computability.Complexity.Problems.Graph.Ports
import Mathlib.Data.List.GetD

/-!
# Degrees of CNF incidence vertices

Degrees count listed literal incidences, including repeated literals within one clause.
This is the degree convention required by the canonical three-port drawing construction.

## Main results

* `Cslib.Complexity.SAT.count_incidenceGraph_variable`: variable degree is its literal count.
* `Cslib.Complexity.SAT.count_incidenceGraph_clause`: clause degree is its length.
* `Cslib.Complexity.SAT.incidenceGraph_degree_le`: width and occurrence bounds bound all degrees.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL

variable {V : Type} [DecidableEq V]

private theorem count_variable_endpoints (φ : CNF V) (v : V) (hv : v ∈ φ.vars)
    (os : List (Cslib.Logic.PL.Occurrence V)) :
    (os.flatMap fun o =>
      [φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1]).count
        (φ.distinctVars.idxOf v) = (os.map fun o => o.2.2.1).count v := by
  have hv' := CNF.mem_distinctVars.mpr hv
  have hi := List.idxOf_lt_length_of_mem hv'
  have heq (w : V) : (φ.distinctVars.idxOf w = φ.distinctVars.idxOf v) ↔ w = v := by
    rw [eq_comm, List.idxOf_inj hv', eq_comm]
  induction os with
  | nil => rfl
  | cons o os ih =>
    have hne : φ.distinctVars.length + o.1 ≠ φ.distinctVars.idxOf v := by omega
    simp [List.flatMap_cons, List.count_cons, heq, hne, ih, beq_iff_eq]

/-- A variable's graph degree counts every occurrence, including repetitions within one clause. -/
theorem count_incidenceGraph_variable (φ : CNF V) {v : V} (hv : v ∈ φ.vars) :
    (incidenceGraph φ).incidenceVertices.count (φ.distinctVars.idxOf v) = φ.vars.count v := by
  simp only [Graph.incidenceVertices, incidenceGraph, List.flatMap_map]
  rw [count_variable_endpoints φ v hv, Cslib.Logic.PL.map_occurrences]

omit [DecidableEq V] in
private theorem count_indexed_blocks (φ : CNF V) (i : ℕ) : ∀ start,
    ((φ.zipIdx start).flatMap fun c => List.replicate c.1.length c.2).count i =
      if start ≤ i then (φ.getD (i - start) []).length else 0 := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    intro start
    rw [List.zipIdx_cons, List.flatMap_cons, List.count_append, ih]
    by_cases hlo : i < start
    · simp [List.count_replicate, Nat.not_le_of_lt hlo, show ¬start + 1 ≤ i by omega,
        show start ≠ i by omega]
    · by_cases he : i = start
      · subst i
        simp
      · have hsi : start + 1 ≤ i := by omega
        have hsub : i - start = (i - (start + 1)) + 1 := by omega
        simp [List.count_replicate, hsi, show start ≤ i by omega, Ne.symm he, hsub]

omit [DecidableEq V] in
private theorem map_clause_indices (φ : CNF V) :
    (Cslib.Logic.PL.occurrences φ).map Prod.fst =
      φ.zipIdx.flatMap fun c => List.replicate c.1.length c.2 := by
  simp [Cslib.Logic.PL.occurrences, List.map_flatMap, List.map_map,
    Function.comp_def, List.map_const']

private theorem count_clause_endpoints (φ : CNF V) (i : ℕ)
    (os : List (Cslib.Logic.PL.Occurrence V))
    (hvalid : ∀ o ∈ os, o.2.2.1 ∈ φ.vars) :
    (os.flatMap fun o =>
      [φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1]).count
        (φ.distinctVars.length + i) = (os.map Prod.fst).count i := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    have hi := List.idxOf_lt_length_of_mem
      (CNF.mem_distinctVars.mpr (hvalid o List.mem_cons_self))
    have hne : φ.distinctVars.idxOf o.2.2.1 ≠ φ.distinctVars.length + i := by omega
    have ht := ih fun a ha => hvalid a (List.mem_cons_of_mem _ ha)
    simp [List.flatMap_cons, List.count_cons, hne,
      ht, beq_iff_eq]

/-- A clause vertex has one incidence for every literal position; an out-of-range clause has
no incidences. -/
theorem count_incidenceGraph_clause (φ : CNF V) (i : ℕ) :
    (incidenceGraph φ).incidenceVertices.count (φ.distinctVars.length + i) =
      (φ.getD i []).length := by
  simp only [Graph.incidenceVertices, incidenceGraph, List.flatMap_map]
  rw [count_clause_endpoints φ i]
  · rw [map_clause_indices, count_indexed_blocks]
    simp
  · intro o ho
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho

/-- Width and literal-occurrence bounds give the actual listed-incidence degree bound needed
by canonical ports. Parallel edge records are counted separately. -/
theorem incidenceGraph_degree_le {φ : CNF V} {k : ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ k) (hv : ∀ v, φ.vars.count v ≤ k) :
    ∀ v, (incidenceGraph φ).incidenceVertices.count v ≤ k := by
  intro v
  by_cases hmem : v ∈ (incidenceGraph φ).incidenceVertices
  · obtain ⟨e, he, hve⟩ := List.mem_flatMap.mp hmem
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hve
    rcases hve with rfl | rfl
    · rw [count_incidenceGraph_variable]
      · exact hv _
      · rw [← Cslib.Logic.PL.map_occurrences]
        exact List.mem_map_of_mem ho
    · rw [count_incidenceGraph_clause]
      obtain ⟨hi, _, _⟩ := Cslib.Logic.PL.mem_occurrences.mp ho
      rw [List.getD_eq_getElem _ _ hi]
      exact hw _ (List.getElem_mem hi)
  · simp [List.count_eq_zero.mpr hmem]

end Cslib.Complexity.SAT
