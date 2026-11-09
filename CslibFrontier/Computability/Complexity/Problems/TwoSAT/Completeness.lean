/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.Membership
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.Reduction

/-!
# 2SAT is NL-complete

The satisfiable formulas in conjunctive normal form with at most two literals per clause
(`Cslib.Complexity.TwoSAT`, encoded by `Cslib.Complexity.encCNF`) are complete for
nondeterministic logarithmic space under logspace many-one reductions
[Papadimitriou, Theorem 16.3][Papadimitriou94] (`Cslib.Complexity.TwoSAT.logSpaceComplete`).
The classes are the library's native ones, as for directed connectivity
(`Cslib.Complexity.STCON.logSpaceComplete`).

* **Membership** (`Cslib.Complexity.TwoSAT.mem_NL`): the complement of `TwoSAT` is in `NL`
  (`Cslib.Complexity.TwoSAT.compl_mem_NL`), by a nondeterministic counter program looking for a
  clause that is empty or too wide, or for a variable `x` with a path from `x` to `¬x` and one
  back in the implication graph (`Cslib.Complexity.TwoSAT.accepts_decider_iff`). Then `TwoSAT`
  is in `NL` by the Immerman–Szelepcsényi theorem `Cslib.Complexity.NL_eq_coNL`
  [Sipser, Section 8.6][Sipser2013], proved for these native classes by Erik Demaine's
  inductive-counting construction.
* **Hardness** (`Cslib.Complexity.TwoSAT.logSpaceHard`): the complement of directed connectivity
  reduces to `TwoSAT` (`Cslib.Complexity.TwoSAT.logSpaceReducible_compl_STCON`) by a formula
  whose variables are the vertices (`Cslib.Complexity.TwoSAT.reachabilityFormula`), and the
  complement of directed connectivity is `NL`-complete
  (`Cslib.Complexity.STCON.compl_logSpaceComplete`), again by `NL = coNL`.

## Main results

* `Cslib.Complexity.TwoSAT.compl_mem_NL`: the complement of `TwoSAT` is in `NL`.
* `Cslib.Complexity.TwoSAT.mem_NL`: `TwoSAT ∈ NL`.
* `Cslib.Complexity.TwoSAT.logSpaceReducible_compl_STCON`: the complement of directed
  connectivity reduces to `TwoSAT` in logarithmic space.
* `Cslib.Complexity.TwoSAT.logSpaceHard`: every problem in `NL` reduces to `TwoSAT` in
  logarithmic space.
* `Cslib.Complexity.TwoSAT.logSpaceComplete`: `TwoSAT` is `NL`-complete.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Theorem 16.3][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
-/

@[expose] public section

namespace Cslib.Complexity

namespace TwoSAT

/-- **The complement of `TwoSAT` is in `NL`**: a nondeterministic machine looks for a clause that
is empty or has more than two literals, or for a variable `x` with a path from `x` to `¬x` and
one back in the implication graph. -/
theorem compl_mem_NL : TwoSATᶜ ∈ NL encCNF :=
  exists_decidesInLogSpace_compl

/-- **`TwoSAT` is in `NL`**, from its complement by the Immerman–Szelepcsényi theorem
`NL = coNL` [Sipser, Section 8.6][Sipser2013]. -/
theorem mem_NL : TwoSAT ∈ NL encCNF :=
  compl_mem_NL_iff.mp compl_mem_NL

/-- **The complement of directed `s`–`t` connectivity reduces to `TwoSAT` in logarithmic
space** [Papadimitriou, Theorem 16.3][Papadimitriou94]. -/
theorem logSpaceReducible_compl_STCON : LogSpaceReducible encSTCON encCNF STCONᶜ TwoSAT :=
  ⟨reachabilityFormula, computableInLogSpace_reachabilityFormula,
    fun I => (reachabilityFormula_mem_TwoSAT_iff I).symm⟩

/-- **`TwoSAT` is `NL`-hard** under logspace many-one reductions: every problem in `NL` reduces
to the complement of directed connectivity, which reduces to `TwoSAT`. -/
theorem logSpaceHard : LogSpaceHard NL encCNF TwoSAT :=
  fun _ enc A hA => (STCON.compl_logSpaceComplete.2 enc A hA).trans logSpaceReducible_compl_STCON

/-- **`TwoSAT` is `NL`-complete** under logspace many-one reductions
[Papadimitriou, Theorem 16.3][Papadimitriou94]. -/
theorem logSpaceComplete : LogSpaceComplete NL encCNF TwoSAT :=
  ⟨mem_NL, logSpaceHard⟩

end TwoSAT

end Cslib.Complexity
