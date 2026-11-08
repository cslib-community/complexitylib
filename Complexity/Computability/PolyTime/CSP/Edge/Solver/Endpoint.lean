/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.PolyTime
public import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.PolyTime.CSP.Vars

/-!
# Complete explicit-table even edge-CSP native P endpoint

For every raw `CSP Table ℕ`, the native decision routine accepts exactly the satisfiable actual
edge instances with canonical nonempty even delta-matroid local relations. Model membership is
checked internally by explicit stored-row pairs and coordinates. The runtime certificate has no
input-validity hypothesis and uses the complete framed `encCSP encTable encNat` input, with
binary arities/names, actual stored rows and every frame. The optimizer returns an actual
minimum-defect occurrence labeling; the solver returns a satisfying occurrence buffer.

This is the explicit-table edge layer of Theorem 21 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed p. 8, implemented by Algorithm 1, Theorem 24 (printed p. 11),
Section 5.3 and Lemmas 31, 34–35, 37, 40–45. Constraint scopes are positional lists without
repetitions, each actual name occurs twice in distinct constraints, and duplicate constraints
and rows are retained. Empty and true nullary instances are included; false/empty relations
and malformed raw inputs are rejected by the decision problem's model guard. This is a
guarded total decision problem rather than a promise endpoint. The Lean representation,
framed-bit accounting and list-funded native compiler bookkeeping are original.

The planar reductions, hardness and dichotomy conclusions are separate endpoints.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- The ordinary guarded decision problem on complete raw explicit-table CSP inputs. -/
@[expose] def evenEdgeSAT : Set (CSP Table ℕ) :=
  {F | EdgeInstance F ∧ EdgeInstance.EvenConstraints Table.sem F ∧ F.Satisfiable Table.sem}

/-- The actual semantic optimizer is implemented by the certified native finite stack. -/
theorem computableInPolyTime_optimize : ComputableInPolyTime optimize
    (encCSP encTable encNat) (encOption (encList encBool)) := by
  apply Program.computableInPolyTime_optimize.of_enc_eq
  intro F
  rw [Program.optimize_eq]

attribute [local fun_prop] EdgeAugmenting.poly_inconsistentWith

/-- The actual solver, including every model and consistency guard, is ordinary native
polynomial-time on every complete raw framed input. -/
theorem computableInPolyTime_solve : ComputableInPolyTime solve
    (encCSP encTable encNat) (encOption (encList encBool)) := by
  have ho := computableInPolyTime_optimize
  have hv := computableInPolyTime_vars encTable encNat
  have hbody : ComputableInPolyTime
      (fun p : CSP Table ℕ × List Bool =>
        if p.1.vars.any (EdgeAugmenting.inconsistent p.1 p.2) then none else some p.2)
      (encPair (encCSP encTable encNat) (encList encBool)) (encOption (encList encBool)) := by
    fun_prop
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun F bits =>
      if F.vars.any (EdgeAugmenting.inconsistent F bits) then none else some bits)
    ho (ComputableInPolyTime.const none) hbody
  apply h.of_enc_eq
  intro F
  unfold solve
  cases optimize F <;> rfl

/-- The actual semantic decision routine is ordinary native polynomial-time on all raw input. -/
theorem computableInPolyTime_decideSAT : ComputableInPolyTime decideSAT
    (encCSP encTable encNat) encBool := by
  unfold decideSAT
  exact computableInPolyTime_solve.optionIsSome

/-- Every returned solver buffer is an actual valid optimal zero-defect labeling, of exact
original occurrence width. The successful call supplies every model and consistency check. -/
theorem solve_spec (F : CSP Table ℕ) {bits : List Bool} (h : solve F = some bits) :
    checkModel F = true ∧ bits.length = (incidenceList F).length ∧
      IsOptimalLabeling Table.sem (EdgeAugmenting.labeling F bits) ∧
        (defects (EdgeAugmenting.labeling F bits)).card = 0 := by
  unfold solve at h
  cases ho : optimize F with
  | none =>
    simp only [ho, Option.bind_eq_bind, Option.bind_none] at h
    contradiction
  | some out =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    next => contradiction
    next hc =>
      cases Option.some.inj h
      have hs := optimize_result_spec F ho
      exact ⟨hs.1, hs.2.1, hs.2.2,
        (no_inconsistent_iff F bits).mp (Bool.eq_false_iff.mpr hc)⟩

/-- SAT iff the total native full-model decision routine accepts, on every raw input. -/
theorem decideSAT_eq_true_full (F : CSP Table ℕ) : decideSAT F = true ↔ F ∈ evenEdgeSAT := by
  rw [← Program.decideSAT_eq, Program.decideSAT_eq_true]
  rfl

/-- Ordinary native polynomial-time decidability of the actual complete guarded edge problem.
No model, comparison labeling, optimizer, lifter, rank or runtime certificate is input. -/
theorem evenEdgeSAT_mem_P : evenEdgeSAT ∈ P (encCSP encTable encNat) :=
  ⟨Program.decideSAT, Program.computableInPolyTime_decideSAT,
    fun F => (Program.decideSAT_eq_true F).symm⟩

end Cslib.Complexity.CSP.EdgeSolver
