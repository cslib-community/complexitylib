/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Solver.Improve

/-!
# Optimization by successive two-defect improvements

Repeat the one-improvement routine at most one more than the number of occurring variables.
Each successful call removes exactly two defects. The final labeling minimizes defects among
all valid occurrence labelings, and it has zero defects exactly when the original CSP is
satisfiable. There is no comparison input, optimizer provider or assumed lifting operation.

This is the optimization organization of Section 5 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed pp. 8–13. The finite recursion bookkeeping is original.
-/

public section

namespace Cslib.Logic.PL.CSP.Solver

open Table

/-- Run at most `rounds` improvements, stopping immediately when fresh search certifies
optimality. Each improvement has its own fresh contraction-depth allowance. -/
@[expose] def optimizeAux (F : CSP Table ℕ) :
    ℕ → OccurrenceLabeling F Bool → OccurrenceLabeling F Bool
  | 0, f => f
  | rounds + 1, f =>
    match improve (F.contractionMeasure + 1) F f with
    | none => f
    | some g => optimizeAux F rounds g

/-- Enough outer rounds give an actual optimum. The premise is a finite defect count,
not a promised optimizer or runtime certificate. -/
theorem optimizeAux_spec (F : CSP Table ℕ) (rounds : ℕ) (f : OccurrenceLabeling F Bool)
    (hr : (defects f).card < rounds) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F) :
    IsOptimalLabeling sem (optimizeAux F rounds f) := by
  induction rounds generalizing f with
  | zero => omega
  | succ rounds ih =>
    have hi := improve_spec (F.contractionMeasure + 1) F f (by omega) hF hf hM
    cases he : improve (F.contractionMeasure + 1) F f with
    | none => simpa only [optimizeAux, he] using hi
    | some g =>
      rw [he] at hi
      simpa only [optimizeAux, he] using ih g (by omega) hi.1

/-- Compute a minimum-defect labeling using the original whole-instance contraction.
Variable names are never used as loop bounds. -/
@[expose] def optimize (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) :
    OccurrenceLabeling F Bool := optimizeAux F (F.numVars + 1) f

/-- Every defect is an occurring variable; no edge or validity hypothesis is needed. -/
theorem card_defects_le_numVars (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) :
    (defects f).card ≤ F.numVars := by
  apply Finset.card_le_card
  intro v hv
  obtain ⟨o, _, ho, _, _⟩ := mem_defects.mp hv
  exact List.mem_toFinset.mpr (ho ▸ o.var_mem)

/-- The executable optimizer attains the minimum over all valid occurrence labelings.
Its model is the actual ordered positional `CSP Table ℕ`; disconnected instances and
duplicate constraints and rows are permitted. -/
theorem optimize_spec (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) : IsOptimalLabeling sem (optimize F f) :=
  optimizeAux_spec F (F.numVars + 1) f
    (Nat.lt_succ_of_le (card_defects_le_numVars F f)) hF hf hM

/-- SAT correctness for the actual optimizer, including unsatisfiable edge instances with
odd local parities. A zero-defect labeling is exactly a global satisfying assignment. -/
theorem optimize_zero_iff (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) :
    (defects (optimize F f)).card = 0 ↔ F.Satisfiable sem := by
  have ho := optimize_spec F f hF hf hM
  rw [satisfiable_iff_exists_zero_defects sem]
  constructor
  · exact fun hz => ⟨_, ho.1, hz⟩
  · rintro ⟨g, hg, hz⟩
    have hn := ho.2 g hg
    omega

end Cslib.Logic.PL.CSP.Solver
