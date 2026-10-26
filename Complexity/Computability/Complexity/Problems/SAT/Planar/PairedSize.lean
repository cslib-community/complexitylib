/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathBounds
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Exact sizes of the paired-port compiler

The actual output contains eight clauses and sixteen literal positions per ordinary ring,
78 clauses and 162 literal positions per paired crossover, and two binary clauses per retained
path gap. Source literal repetitions are counted with multiplicity. These bounds apply to all
inputs, without a geometric validity assumption.

## Main results

* `ordinaryCells_length_le_retained`, `ordinaryCells_length_le`: occupied ordinary-cell bounds.
* `length_formula`, `length_vars_formula`: exact clause and literal accounting.
* `width_formula`: width-three inputs produce width-three outputs.
* `length_formula_le`, `length_vars_formula_le`: explicit quadratic output bounds.

## References

The unchanged path estimates are reused from `Planar.Size`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Selected crossings reuse the canonical quadratic cover. -/
theorem crossingSites_length_le (φ : CNF ℕ) :
    (crossingSites φ).length ≤ 2 * φ.vars.length ^ 2 :=
  PlanarCompile.crossingSites_length_le φ

/-- Filtering and deduplication do not increase the number of retained path points. -/
theorem ordinaryCells_length_le_retained (φ : CNF ℕ) :
    (ordinaryCells φ).length ≤ ((paths φ).map fun r => r.dropLast.length).sum := by
  unfold ordinaryCells
  rw [length_selectDistinct_replicate]
  exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans_eq
    List.length_flatMap)

/-- The ordinary-cell count is bounded by the canonical total path budget. -/
theorem ordinaryCells_length_le (φ : CNF ℕ) :
    (ordinaryCells φ).length ≤ φ.vars.length * (5 * PlanarCompile.budget φ + 1) := by
  calc
    _ ≤ ((paths φ).map fun r => r.dropLast.length).sum := ordinaryCells_length_le_retained φ
    _ ≤ ((paths φ).map fun _ => 5 * PlanarCompile.budget φ + 1).sum :=
      List.sum_le_sum fun r hr => (by simp only [List.length_dropLast]; omega :
        r.dropLast.length ≤ r.length).trans (PlanarCompile.path_length_le hr)
    _ = _ := by simp [PlanarCompile.paths_length, Nat.mul_comm]

/-- Original clauses keep their count. -/
theorem length_originalClauses (φ : CNF ℕ) (sites : List Point) :
    (originalClauses φ sites).length = φ.length := by simp [originalClauses]

/-- One ordinary cell contributes eight clauses. -/
theorem length_ordinaryClauses (p : Point) : (ordinaryClauses p).length = 8 := by
  simp [ordinaryClauses, OrdinaryRing.formula_sizes.1]

/-- One crossing contributes 78 clauses. -/
theorem length_crossingClauses (p : Point) : (crossingClauses p).length = 78 := by
  simp [crossingClauses, PairedCrossover.length_formula]

/-- Each retained path gap contributes two clauses. -/
theorem length_links (sites : List Point) (r : Route) :
    (links sites r).length = 2 * (r.length - 2) := by
  have hsum : (links sites r).length = 2 * r.dropLast.consecutivePairs.length := by
    simp [links, List.length_flatMap, Nat.mul_comm]
  rw [hsum]
  simp only [List.consecutivePairs, List.length_zip, List.length_dropLast, List.length_tail]
  omega

/-- Exact clause count of the emitted structured formula. -/
theorem length_rawFormula (φ : CNF ℕ) :
    (rawFormula φ).length = φ.length + 8 * (ordinaryCells φ).length +
      78 * (crossingSites φ).length + 2 * PlanarCompile.linkCount φ := by
  simp [rawFormula, placedClauses, List.length_flatMap, length_originalClauses,
    length_ordinaryClauses, length_crossingClauses, length_links, PlanarCompile.linkCount,
    List.sum_map_mul_left, Nat.mul_comm, Nat.add_assoc]

/-- Compaction preserves the exact output clause count. -/
theorem length_formula (φ : CNF ℕ) :
    (formula φ).length = φ.length + 8 * (ordinaryCells φ).length +
      78 * (crossingSites φ).length + 2 * PlanarCompile.linkCount φ := by
  simpa only [formula, CNF.length_compact] using length_rawFormula φ

/-- Original clause records preserve their widths. -/
theorem width_originalClauses {φ : CNF ℕ} {k : ℕ}
    (h : ∀ c ∈ φ, c.length ≤ k) (sites : List Point) :
    ∀ c ∈ originalClauses φ sites, c.1.length ≤ k := by
  intro c hc
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  simpa using h d (List.fst_mem_of_mem_zipIdx hd)

/-- Every ordinary ring clause is binary. -/
theorem width_ordinaryClauses (p : Point) :
    ∀ c ∈ ordinaryClauses p, c.1.length = 2 := by
  intro c hc
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  simpa [Clause.relabel] using OrdinaryRing.formula_sizes.2 d
    (List.fst_mem_of_mem_zipIdx hd)

/-- Every crossover clause has width at most three. -/
theorem width_crossingClauses (p : Point) :
    ∀ c ∈ crossingClauses p, c.1.length ≤ 3 := by
  intro c hc
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  simpa [Clause.relabel] using PairedCrossover.width_formula d
    (List.fst_mem_of_mem_zipIdx hd)

/-- Every seam clause is binary. -/
theorem width_links (sites : List Point) (r : Route) :
    ∀ c ∈ links sites r, c.1.length = 2 := by
  intro c hc
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- Width-three inputs produce structured formulas of width at most three. -/
theorem width_rawFormula {φ : CNF ℕ} (h : ∀ c ∈ φ, c.length ≤ 3) :
    ∀ c ∈ rawFormula φ, c.length ≤ 3 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hd
  rcases hd with ((hd | ⟨p, _, hd⟩) | ⟨p, _, hd⟩) | ⟨o, _, hd⟩
  · exact width_originalClauses h _ d hd
  · exact (width_ordinaryClauses p d hd).le.trans (by decide)
  · exact width_crossingClauses p d hd
  · exact (width_links _ _ d hd).le.trans (by decide)

/-- Compaction preserves the width-three guarantee. -/
theorem width_formula {φ : CNF ℕ} (h : ∀ c ∈ φ, c.length ≤ 3) :
    ∀ c ∈ formula φ, c.length ≤ 3 := by
  intro c hc
  have hm : c.length ∈ (formula φ).map List.length := List.mem_map_of_mem hc
  rw [formula, CNF.map_length_compact] at hm
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact width_rawFormula h d hd

private theorem original_literal_count (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun c => c.1.length).sum = φ.vars.length := by
  rw [CNF.length_vars]
  simp only [originalClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]
  change ((φ.zipIdx).map (List.length ∘ Prod.fst)).sum = (φ.map List.length).sum
  rw [← List.map_map, List.zipIdx_map_fst]

private theorem ordinary_literal_count (p : Point) :
    ((ordinaryClauses p).map fun c => c.1.length).sum = 16 := by
  simp only [ordinaryClauses, List.map_map, Function.comp_def, Clause.relabel, List.length_map]
  decide +kernel

private theorem crossing_literal_count (p : Point) :
    ((crossingClauses p).map fun c => c.1.length).sum = 162 := by
  simp only [crossingClauses, List.map_map, Function.comp_def, Clause.relabel, List.length_map]
  decide +kernel

private theorem links_literal_count (sites : List Point) (r : Route) :
    ((links sites r).map fun c => c.1.length).sum = 4 * (r.length - 2) := by
  have hmap : (links sites r).map (fun c => c.1.length) = (links sites r).map (fun _ => 2) :=
    List.map_congr_left fun c hc => width_links sites r c hc
  rw [hmap]
  have hsum : ((links sites r).map fun _ => 2).sum = 2 * (links sites r).length := by
    simp [Nat.mul_comm]
  rw [hsum, length_links]
  omega

/-- Exact literal count, including repetitions and all ordinary ring ports. -/
theorem length_vars_rawFormula (φ : CNF ℕ) :
    (rawFormula φ).vars.length = φ.vars.length + 16 * (ordinaryCells φ).length +
      162 * (crossingSites φ).length + 4 * PlanarCompile.linkCount φ := by
  rw [CNF.length_vars]
  simp only [rawFormula, List.map_map]
  change ((placedClauses φ).map fun c => c.1.length).sum = _
  simp only [placedClauses, List.map_append, List.sum_append, List.flatMap,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  simp_rw [original_literal_count, ordinary_literal_count, crossing_literal_count,
    links_literal_count]
  simp [PlanarCompile.linkCount, List.sum_map_mul_left, Nat.mul_comm, Nat.add_assoc]

/-- Compaction preserves the exact number of output literal occurrences. -/
theorem length_vars_formula (φ : CNF ℕ) :
    (formula φ).vars.length = φ.vars.length + 16 * (ordinaryCells φ).length +
      162 * (crossingSites φ).length + 4 * PlanarCompile.linkCount φ := by
  simpa only [formula, CNF.length_vars, CNF.map_length_compact] using length_vars_rawFormula φ

/-- A generous explicit quadratic clause bound in the source incidence size. -/
theorem length_formula_le (φ : CNF ℕ) :
    (formula φ).length ≤ 5000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have ho := ordinaryCells_length_le φ
  have hc := crossingSites_length_le φ
  have hl := PlanarCompile.linkCount_le φ
  rw [length_formula]
  have hb : PlanarCompile.budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [PlanarCompile.budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at ho hl
  nlinarith

/-- A generous explicit quadratic bound on output literal occurrences. -/
theorem length_vars_formula_le (φ : CNF ℕ) :
    (formula φ).vars.length ≤ 10000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have ho := ordinaryCells_length_le φ
  have hc := crossingSites_length_le φ
  have hl := PlanarCompile.linkCount_le φ
  rw [length_vars_formula]
  have hb : PlanarCompile.budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [PlanarCompile.budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at ho hl
  nlinarith

end Cslib.Complexity.SAT.ParsimoniousPlanar
