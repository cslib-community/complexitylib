/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Correctness
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Compatible assignments for the actual planar compiler

An ordinary occupied cell carries its source variable's value. At a selected crossing the
horizontal and vertical source values independently extend through the fixed crossover.

## Main definitions

Compiler data and CNF semantics are reused unchanged.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.exists_compatible_assignment`: compatible actual wires
  and independent satisfying crossover blocks for every source assignment.
* `Cslib.Complexity.SAT.PlanarCompile.satisfiable_formula_iff`: actual satisfiability equivalence
  under source width and literal-occurrence bounds of three.

## References

These are original logical composition proofs for the finite compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- An actual raw compiler output has a satisfying extension of every source model. -/
theorem satisfiable_rawFormula_of_source {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (h : φ.Satisfiable) : (rawFormula φ).Satisfiable := by
  obtain ⟨τ, hτ⟩ := h
  obtain ⟨σ, hcompat, hcross⟩ := exists_compatible_assignment hw hv τ
  exact ⟨σ, eval_rawFormula_complete_of_compatible φ τ σ
    (fun _ ho => occurrencePath_length_ge_two ho) hcompat hcross hτ⟩

/-- The actual compact compiler preserves satisfiability under source width and literal-count
bounds of three. Geometry, degree bounds, and running time are separate compiler properties. -/
theorem satisfiable_formula_iff {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (formula φ).Satisfiable ↔ φ.Satisfiable :=
  ⟨satisfiable_source_of_formula hw hv, fun h =>
    (CNF.satisfiable_compact (rawFormula φ)).2 (satisfiable_rawFormula_of_source hw hv h)⟩

end Cslib.Complexity.SAT.PlanarCompile
