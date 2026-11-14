/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Complete
public import CslibFrontier.Computability.Complexity.Problems.Tautology
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Reduction.Turing

/-!
# NP = coNP exactly when 3SAT and TAUTOLOGY reduce to each other

Exercise 7, Chapter 2 of the 2007 draft [AroraBarak07] (printed page 62 / PDF page 78): `NP = coNP`
if and only if `3SAT ≤ₚ TAUTOLOGY` and `TAUTOLOGY ≤ₚ 3SAT`. `ThreeSAT` is the set of satisfiable
CNFs with clauses of width at most three, encoded by `encCNF`. `TAUTOLOGY` is the set of
quantifier-free formulas of `Cslib.Logic.PL.QBF ℕ` that are true under every assignment,
encoded by `encQBF` (`CslibFrontier.Computability.Complexity.Problems.Tautology`). The
reductions are native polynomial-time many-one reductions. As in
`Cslib.Complexity.NP_eq_coNP_iff_coNP_subset_NP`, `NP = coNP` is quantified over every explicit
encoding of instances. The proof applies `Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible` to
`Cslib.Complexity.ThreeSAT_npComplete` and `Cslib.Complexity.TAUTOLOGY_coNPComplete`.

Under polynomial-time Turing (Cook) reductions (`Cslib.Complexity.PolyTimeTuringReducible`),
complement queries are unconditionally available (`PolyTimeTuringReducible.compl_left`), so
`TAUTOLOGY` is `NP`-hard (`Cslib.Complexity.TAUTOLOGY_npTuringHard`), `ThreeSAT` is `coNP`-hard
(`Cslib.Complexity.ThreeSAT_coNPTuringHard`), and `3SAT` and `TAUTOLOGY` Cook-reduce to each other
unconditionally (`Cslib.Complexity.polyTimeTuringReducible_ThreeSAT_TAUTOLOGY`,
`Cslib.Complexity.polyTimeTuringReducible_TAUTOLOGY_ThreeSAT`, Exercise 12, Chapter 2 of
[AroraBarak07]).
-/

public section

namespace Cslib.Complexity

/-- **Arora–Barak 2007, Chapter 2, Exercise 7:** `NP = coNP` exactly when 3SAT and TAUTOLOGY
reduce to each other in polynomial time. -/
theorem NP_eq_coNP_iff_ThreeSAT_reducible_TAUTOLOGY :
    (∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) ↔
      PolyTimeReducible encCNF encQBF ThreeSAT TAUTOLOGY ∧
        PolyTimeReducible encQBF encCNF TAUTOLOGY ThreeSAT :=
  ThreeSAT_npComplete.NP_eq_coNP_iff_reducible TAUTOLOGY_coNPComplete

/-- `TAUTOLOGY` is `NP`-hard under polynomial-time Turing (Cook) reductions. -/
theorem TAUTOLOGY_npTuringHard : NPTuringHard encQBF TAUTOLOGY :=
  TAUTOLOGY_coNPHard.npTuringHard

/-- `ThreeSAT` is `coNP`-hard under polynomial-time Turing (Cook) reductions. -/
theorem ThreeSAT_coNPTuringHard : coNPTuringHard encCNF ThreeSAT :=
  ThreeSAT_npHard.coNPTuringHard

/-- **Arora–Barak 2007, Chapter 2, Exercise 12:** `3SAT` is polynomial-time Turing (Cook) reducible
to `TAUTOLOGY`. -/
theorem polyTimeTuringReducible_ThreeSAT_TAUTOLOGY :
    PolyTimeTuringReducible encCNF encQBF ThreeSAT TAUTOLOGY :=
  TAUTOLOGY_npTuringHard encCNF ThreeSAT ThreeSAT.mem_NP

/-- `TAUTOLOGY` is polynomial-time Turing (Cook) reducible to `3SAT`. -/
theorem polyTimeTuringReducible_TAUTOLOGY_ThreeSAT :
    PolyTimeTuringReducible encQBF encCNF TAUTOLOGY ThreeSAT :=
  ThreeSAT_coNPTuringHard encQBF TAUTOLOGY TAUTOLOGY_mem_coNP

end Cslib.Complexity
