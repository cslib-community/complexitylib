/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathBounds
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Size accounting for the finite planarization compiler

These bounds concern the actual output lists. In particular, crossing sites are selected from
the canonical quadratic cover, rather than supplied as an unbounded certificate.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.linkCount`: the number of emitted binary implications.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.crossingSites_length_le`: at most twice the squared
  number of input literal incidences.
* `Cslib.Complexity.SAT.PlanarCompile.length_formula`: exact clause accounting.
* `Cslib.Complexity.SAT.PlanarCompile.width_formula`: clause widths are preserved up to three.

## References

The accounting is for the original finite construction in `Compile`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Original clauses keep their count. -/
theorem length_originalClauses (φ : CNF ℕ) (sites : List Point) :
    (originalClauses φ sites).length = φ.length := by simp [originalClauses]

/-- One crossing contributes the fixed 74 clauses. -/
theorem length_crossingClauses (p : Point) : (crossingClauses p).length = 74 := by
  simp [crossingClauses, Crossover.length_splitFormula]

/-- Every external gap contributes exactly one binary clause. -/
theorem length_links (sites : List Point) (positive : Bool) (r : Route) :
    (links sites positive r).length = r.length - 2 := by
  simp only [links, List.length_map, List.consecutivePairs, List.length_zip,
    List.length_tail, List.length_dropLast]
  omega

/-- Exact clause count: original clauses, fixed templates, and external links. -/
theorem length_rawFormula (φ : CNF ℕ) :
    (rawFormula φ).length = φ.length + 74 * (crossingSites φ).length + linkCount φ := by
  simp [rawFormula, placedClauses, List.length_flatMap, length_originalClauses,
    length_crossingClauses, length_links, linkCount, Nat.mul_comm, Nat.add_assoc]

/-- Compaction keeps the exact output clause count. -/
theorem length_formula (φ : CNF ℕ) :
    (formula φ).length = φ.length + 74 * (crossingSites φ).length + linkCount φ := by
  simpa only [formula, CNF.length_compact] using length_rawFormula φ

/-- The original clause records keep their individual widths. -/
theorem width_originalClauses {φ : CNF ℕ} {k : ℕ}
    (h : ∀ c ∈ φ, c.length ≤ k) (sites : List Point) :
    ∀ c ∈ originalClauses φ sites, c.1.length ≤ k := by
  intro c hc
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  have hd' : d ∈ φ := List.fst_mem_of_mem_zipIdx hd
  simpa using h d hd'

/-- The fixed crossing clauses have width at most three. -/
theorem width_crossingClauses (p : Point) :
    ∀ c ∈ crossingClauses p, c.1.length ≤ 3 := by
  intro c hc
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  have hd' : d ∈ Crossover.splitFormula := List.fst_mem_of_mem_zipIdx hd
  simpa [Clause.relabel] using Crossover.width_splitFormula d hd'

/-- Every link clause is binary, independent of input validity. -/
theorem width_links (sites : List Point) (positive : Bool) (r : Route) :
    ∀ c ∈ links sites positive r, c.1.length = 2 := by
  intro c hc
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
  cases positive <;> rfl

/-- Width-three inputs produce width-three output formulas. -/
theorem width_rawFormula {φ : CNF ℕ} (h : ∀ c ∈ φ, c.length ≤ 3) :
    ∀ c ∈ rawFormula φ, c.length ≤ 3 := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · exact width_originalClauses h _ d hd
    · obtain ⟨p, _, hd⟩ := List.mem_flatMap.mp hd
      exact width_crossingClauses p d hd
  · obtain ⟨o, _, hd⟩ := List.mem_flatMap.mp hd
    exact (width_links _ _ _ d hd).le.trans (by decide)

/-- Compaction preserves the width-three guarantee. -/
theorem width_formula {φ : CNF ℕ} (h : ∀ c ∈ φ, c.length ≤ 3) :
    ∀ c ∈ formula φ, c.length ≤ 3 := by
  intro c hc
  have hm : c.length ∈ (formula φ).map List.length := List.mem_map_of_mem hc
  rw [formula, CNF.map_length_compact] at hm
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact width_rawFormula h d hd

/-- An explicit quadratic clause bound in the source incidence graph's combinatorial size. -/
theorem length_formula_le (φ : CNF ℕ) :
    (formula φ).length ≤ 600 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have hc := crossingSites_length_le φ
  have hl := linkCount_le φ
  rw [length_formula]
  have hb : budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at hl
  nlinarith [sq_nonneg (φ.numVars : ℤ), sq_nonneg (φ.length : ℤ),
    sq_nonneg (φ.vars.length : ℤ)]

private theorem original_literal_count (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun c => c.1.length).sum = φ.vars.length := by
  rw [CNF.length_vars]
  simp only [originalClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]
  change ((φ.zipIdx).map (List.length ∘ Prod.fst)).sum = (φ.map List.length).sum
  rw [← List.map_map, List.zipIdx_map_fst]

private theorem crossing_literal_count (p : Point) :
    ((crossingClauses p).map fun c => c.1.length).sum = 154 := by
  simp only [crossingClauses, List.map_map, Function.comp_def, Clause.relabel, List.length_map]
  change ((Crossover.splitFormula.zipIdx.map Prod.fst).map List.length).sum = 154
  decide +kernel

private theorem links_literal_count (sites : List Point) (positive : Bool) (r : Route) :
    ((links sites positive r).map fun c => c.1.length).sum = 2 * (r.length - 2) := by
  have hmap : (links sites positive r).map (fun c => c.1.length) =
      (links sites positive r).map (fun _ => 2) :=
    List.map_congr_left fun c hc => width_links sites positive r c hc
  rw [hmap]
  simp [length_links, Nat.mul_comm]

/-- Exact literal count, counting repetitions: one original literal, 154 per crossover,
and two per external implication. -/
theorem length_vars_rawFormula (φ : CNF ℕ) :
    (rawFormula φ).vars.length =
      φ.vars.length + 154 * (crossingSites φ).length + 2 * linkCount φ := by
  rw [CNF.length_vars]
  simp only [rawFormula, List.map_map]
  change ((placedClauses φ).map fun c => c.1.length).sum = _
  simp only [placedClauses, List.map_append, List.sum_append, List.map_flatMap]
  rw [original_literal_count]
  have hc : (((crossingSites φ).flatMap fun p =>
      (crossingClauses p).map fun c => c.1.length)).sum = 154 * (crossingSites φ).length := by
    induction crossingSites φ with
    | nil => simp
    | cons p ps ih => simp [crossing_literal_count, ih, Nat.mul_add, Nat.add_comm]
  rw [hc]
  have hl : (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      (links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun c => c.1.length)).sum =
      2 * linkCount φ := by
    unfold linkCount
    induction Cslib.Logic.PL.occurrences φ with
    | nil => simp
    | cons o os ih => simp [links_literal_count, ih, Nat.mul_add]
  rw [hl]

/-- Compaction keeps the exact literal count. -/
theorem length_vars_formula (φ : CNF ℕ) :
    (formula φ).vars.length =
      φ.vars.length + 154 * (crossingSites φ).length + 2 * linkCount φ := by
  simpa only [formula, CNF.length_vars, CNF.map_length_compact] using length_vars_rawFormula φ

/-- An explicit quadratic bound on the number of output literal incidences. -/
theorem length_vars_formula_le (φ : CNF ℕ) :
    (formula φ).vars.length ≤ 1210 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have hc := crossingSites_length_le φ
  have hl := linkCount_le φ
  rw [length_vars_formula]
  have hb : budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at hl
  nlinarith

end Cslib.Complexity.SAT.PlanarCompile
