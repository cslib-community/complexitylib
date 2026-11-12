/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Agreement
import CslibFrontier.Foundations.Data.List.EraseDups

/-!
# Correctness of the finite explicit-table solver

The list-funded stack and outer optimization loop agree exactly with the mathematical
one-improvement solver. The complete guard is internal to the decision program. Acceptance
means satisfiability under the existing `Table.sem` and the actual edge/even-delta-matroid
model; raw malformed inputs and nonmodel relations are rejected.

This is the edge-layer algorithm of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
Section 5 and Algorithm 1 (printed pp. 8–13). It supplies no planar embedding, hardness or
dichotomy endpoint. Native bit-complexity certification is a separate obligation.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP

private theorem iterate_stopped (F : CSP Table ℕ) (bits : List Bool) (n : ℕ) :
    (optimizeStep F)^[n] (bits, true) = (bits, true) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- The finite outer loop has exactly the mathematical solver's output at every round count.
The stopped bit only avoids repeated fresh searches after an exhausted optimum. -/
theorem iterate_eq (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) (rounds : ℕ) :
    ((optimizeStep F)^[rounds] (buffer f, false)).1 =
      buffer (Solver.optimizeAux F rounds f) := by
  induction rounds generalizing f with
  | zero => rfl
  | succ rounds ih =>
    rw [Function.iterate_succ_apply]
    have hi := Solver.improve_spec (F.contractionMeasure + 1) F f (by omega) hF hf hM
    cases he : Solver.improve (F.contractionMeasure + 1) F f with
    | none =>
      simp only [optimizeStep, Bool.false_eq_true, ↓reduceIte,
        improve_eq_source F f hF hf hM, he, Option.map_none, iterate_stopped,
        Solver.optimizeAux]
    | some g =>
      rw [he] at hi
      simp only [optimizeStep, Bool.false_eq_true, ↓reduceIte,
        improve_eq_source F f hF hf hM, he, Option.map_some, Solver.optimizeAux]
      exact ih g hi.1

/-- Exact agreement of the guarded finite optimizer with the proved mathematical optimizer.
This equation holds on all raw explicit-table inputs; the model guard is inside both sides. -/
theorem optimize_eq (F : CSP Table ℕ) : optimize F = EdgeSolver.optimize F := by
  by_cases hm : checkModel F = true
  · have hmodel := checkModel_sound F hm
    simp only [optimize, EdgeSolver.optimize, hm, ↓reduceIte]
    rw [iterate_eq F (initial F) hmodel.1 (initial_valid F hm) hmodel.2]
    simp only [List.length_eraseDups, numVars, Solver.optimize, buffer]
  · simp [optimize, EdgeSolver.optimize, hm]

/-- The native-search stack returns an actual minimum-defect finite occurrence buffer. -/
theorem optimize_spec (F : CSP Table ℕ) (h : checkModel F = true) :
    ∃ bits, optimize F = some bits ∧ bits.length = (incidenceList F).length ∧
      IsOptimalLabeling Table.sem (EdgeAugmenting.labeling F bits) := by
  obtain ⟨bits, hb, ho⟩ := EdgeSolver.optimize_spec F h
  exact ⟨bits, (optimize_eq F).trans hb, EdgeSolver.optimize_width F hb, ho⟩

/-- Exact decision agreement on every raw input, including false or malformed nullaries. -/
theorem decideSAT_eq (F : CSP Table ℕ) : decideSAT F = EdgeSolver.decideSAT F := by
  unfold decideSAT EdgeSolver.decideSAT EdgeSolver.solve
  rw [optimize_eq]
  cases EdgeSolver.optimize F with
  | none => rfl
  | some bits =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.any_some]
    cases F.vars.any (EdgeAugmenting.inconsistent F bits) <;> rfl

/-- Complete guarded SAT correctness in the actual edge model. Every model check and every
optimization step is executed internally; there is no validity premise on this endpoint. -/
theorem decideSAT_eq_true (F : CSP Table ℕ) : decideSAT F = true ↔
    EdgeInstance F ∧ EdgeInstance.EvenConstraints Table.sem F ∧ F.Satisfiable Table.sem := by
  rw [decideSAT_eq, EdgeSolver.decideSAT_eq_true, checkModel_eq_true, and_assoc]

end Cslib.Complexity.CSP.EdgeSolver.Program
