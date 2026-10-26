/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathData
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath
public import Complexity.Logics.Propositional.CNF.Occurrence
import Complexity.Foundations.Data.List.Range
import Mathlib.Data.List.GetD

/-!
# Canonical paths of the actual planarization compiler

The executable compiler uses the canonical unit paths of the existing CNF incidence graph.
These shared certificates serve both continuous geometry and logical wire correctness.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.paths_eq_unitPaths`, `.occurrencePath_eq_unitPath`:
  exact agreement with the canonical graph layout.
* `Cslib.Complexity.SAT.PlanarCompile.occurrence_index_lt`: valid literal-incidence indices.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_endpoints`, `.occurrencePath_nodup`:
  actual endpoints and uniqueness of all listed points.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_unit`, `.occurrencePath_last_unit`:
  unit adjacency, including the final-literal lookups.
* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_ne_nil`, `.occurrencePath_length_ge_two`:
  paths contain a genuine unit step before the original clause center.

* `Cslib.Complexity.SAT.PlanarCompile.occurrencePaths_eq_paths`: indexed source occurrences
  select exactly the emitted canonical paths in their original order.

## References

These certificates refer to the original canonical path construction in the imported compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The executable compiler uses exactly the canonical unit paths certified by the layout API. -/
theorem paths_eq_unitPaths (φ : CNF ℕ) : paths φ = (SAT.incidenceGraph φ).unitPaths := rfl

/-- Literal-occurrence indexing selects the same path in the compiler and canonical layout. -/
theorem occurrencePath_eq_unitPath (φ : CNF ℕ) (o : Occurrence ℕ) :
    occurrencePath φ o =
      (SAT.incidenceGraph φ).unitPath ((Cslib.Logic.PL.occurrences φ).idxOf o) := rfl

/-- Every actual occurrence indexes an existing incidence edge. -/
theorem occurrence_index_lt {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (Cslib.Logic.PL.occurrences φ).idxOf o < (SAT.incidenceGraph φ).2.length := by
  simpa only [SAT.incidenceGraph, List.length_map] using List.idxOf_lt_length_of_mem ho

/-- Every actual occurrence path is duplicate-free, without an extra supplied path witness. -/
theorem occurrencePath_nodup {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : (occurrencePath φ o).Nodup := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_nodup _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

/-- Every consecutive step in the actual compiler path is a unit grid displacement. -/
theorem occurrencePath_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
  rw [occurrencePath_eq_unitPath] at he
  exact Graph.unitPath_unit _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho) he

/-- Every actual selected path contains at least one point. -/
theorem occurrencePath_ne_nil {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ≠ [] := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_ne_nil _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

/-- Actual occurrence paths start at the variable's source-grid center and end at their clause. -/
theorem occurrencePath_endpoints {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (occurrencePath φ o).head? = some (Layout.center (φ.distinctVars.idxOf o.2.2.1)) ∧
      (occurrencePath φ o).getLast? = some (Layout.center (φ.distinctVars.length + o.1)) := by
  have hi := occurrence_index_lt ho
  have h := Graph.unitPath_endpoints (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi
  have he : (SAT.incidenceGraph φ).2[(Cslib.Logic.PL.occurrences φ).idxOf o] =
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]
  have hb := SAT.incidenceGraph_bipartite (List.getElem_mem hi)
  rw [he] at hb
  simp only [Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte] at h
  simp only [List.getD_eq_getElem _ _ hi, he] at h
  change (occurrencePath φ o).head? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.idxOf o.2.2.1))) ∧
    (occurrencePath φ o).getLast? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.length + o.1))) at h
  rw [List.idxOf_range_of_lt (by omega), List.idxOf_range_of_lt hb.2.2] at h
  exact h

/-- Actual literal paths contain at least one unit step, so final-literal lookups are in range. -/
theorem occurrencePath_length_ge_two {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : 2 ≤ (occurrencePath φ o).length := by
  have hne := occurrencePath_ne_nil ho
  have hend := occurrencePath_endpoints ho
  have hi : φ.distinctVars.idxOf o.2.2.1 < φ.distinctVars.length := by
    apply List.idxOf_lt_length_of_mem
    apply CNF.mem_distinctVars.mpr
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho
  have hcenters : Layout.center (φ.distinctVars.idxOf o.2.2.1) ≠
      Layout.center (φ.distinctVars.length + o.1) := by
    intro heq
    have hx := congrArg Prod.fst heq
    simp only [Layout.center] at hx
    omega
  cases hr : occurrencePath φ o with
  | nil => exact False.elim (hne hr)
  | cons p r =>
    cases r with
    | nil =>
      simp only [hr, List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hend
      exact False.elim (hcenters (hend.1.symm.trans hend.2))
    | cons q r => simp

/-- The last two actual unit-path points are adjacent, including with the compiler's defaults. -/
theorem occurrencePath_last_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    let r := occurrencePath φ o
    Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1 := by
  have hlen := occurrencePath_length_ge_two ho
  dsimp only
  apply occurrencePath_unit ho (e :=
    ((occurrencePath φ o).getD ((occurrencePath φ o).length - 2) (0, 0),
      (occurrencePath φ o).getLastD (0, 0)))
  rw [List.consecutivePairs]
  let r := occurrencePath φ o
  have hrlen : 2 ≤ r.length := hlen
  have hk : r.length - 2 < (r.zip r.tail).length := by
    simp only [List.length_zip, List.length_tail]
    dsimp only [r]
    omega
  have heq : (r.zip r.tail)[r.length - 2] =
      (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0)) := by
    rw [List.getElem_zip]
    apply Prod.ext
    · rw [List.getD_eq_getElem _ _ (by dsimp only [r]; omega)]
    · rw [List.getElem_tail]
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      change r[r.length - 2 + 1] = r[r.length - 1]
      congr 1
      omega
  rw [← heq]
  exact List.getElem_mem hk

/-- Enumerating source occurrences selects all actual paths in their original order. -/
theorem occurrencePaths_eq_paths (φ : CNF ℕ) :
    (Cslib.Logic.PL.occurrences φ).map (occurrencePath φ) = paths φ := by
  have hlen : (Cslib.Logic.PL.occurrences φ).length = (paths φ).length := by
    simp [paths, SAT.incidenceGraph]
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    rw [List.getElem_map]
    unfold occurrencePath
    rw [(Cslib.Logic.PL.occurrences_nodup φ).idxOf_getElem i (by simpa using hi),
      List.getD_eq_getElem _ _ hj]

end Cslib.Complexity.SAT.PlanarCompile
