/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Reduction
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Search

/-!
# Strongly connected digraphs are NL-complete

The strongly connected digraphs (`Cslib.Complexity.StronglyConnected`, encoded by their adjacency
matrices as `Cslib.Complexity.encDigraph`) are complete for nondeterministic logarithmic space
under logspace many-one reductions [Arora and Barak, Exercise 4.4][AroraBarak09]
(`Cslib.Complexity.StronglyConnected.logSpaceComplete`). The classes are the library's native
ones, as for directed connectivity (`Cslib.Complexity.STCON.logSpaceComplete`).

* **Membership** (`Cslib.Complexity.StronglyConnected.mem_NL`): a nondeterministic counter
  program runs through all pairs of vertices and guesses a path for each
  (`Cslib.Complexity.StronglyConnected.searchProgram`).
* **Hardness** (`Cslib.Complexity.StronglyConnected.logSpaceHard`): directed connectivity reduces
  to strong connectivity by adding an arc from every vertex to `s` and from `t` to every vertex
  (`Cslib.Complexity.StronglyConnected.ofSTCON`), and directed connectivity is `NL`-hard.

## Main results

* `Cslib.Complexity.StronglyConnected.mem_NL`: `StronglyConnected ∈ NL`.
* `Cslib.Complexity.StronglyConnected.logSpaceReducible_STCON`: directed connectivity reduces to
  strong connectivity in logarithmic space.
* `Cslib.Complexity.StronglyConnected.logSpaceHard`: every problem in `NL` reduces to strong
  connectivity in logarithmic space.
* `Cslib.Complexity.StronglyConnected.logSpaceComplete`: strong connectivity is `NL`-complete.
* `Cslib.Complexity.StronglyConnected.mem_L_iff_forall_NL_eq_L`: strong connectivity is in `L`
  exactly when `NL = L`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Exercise 4.4][AroraBarak09]
-/

public section

namespace Cslib.Complexity

namespace StronglyConnected

/-- **Strong connectivity is in `NL`.** -/
theorem mem_NL : StronglyConnected ∈ NL encDigraph :=
  exists_decidesInLogSpace

/-- **Directed `s`–`t` connectivity reduces to strong connectivity in logarithmic space**, by
adding an arc from every vertex to `s` and from `t` to every vertex. -/
theorem logSpaceReducible_STCON :
    LogSpaceReducible encSTCON encDigraph STCON StronglyConnected :=
  ⟨ofSTCON, computableInLogSpace_ofSTCON, fun I => (ofSTCON_mem_iff I).symm⟩

/-- **Strong connectivity is `NL`-hard** under logspace many-one reductions: every problem in `NL`
reduces to directed connectivity, which reduces to strong connectivity. -/
theorem logSpaceHard : LogSpaceHard NL encDigraph StronglyConnected :=
  fun _ enc A hA => (STCON.logSpaceComplete.2 enc A hA).trans logSpaceReducible_STCON

/-- **Strong connectivity is `NL`-complete** under logspace many-one reductions
[Arora and Barak, Exercise 4.4][AroraBarak09]. -/
theorem logSpaceComplete : LogSpaceComplete NL encDigraph StronglyConnected :=
  ⟨mem_NL, logSpaceHard⟩

/-- **Strong connectivity is in `L` exactly when `NL = L`**, for every encoding of instances. -/
theorem mem_L_iff_forall_NL_eq_L :
    StronglyConnected ∈ L encDigraph ↔ ∀ {α : Type} (enc : α ↪ List Bool), NL enc = L enc :=
  logSpaceComplete.mem_L_iff fun _ => L_subset_NL

end StronglyConnected

end Cslib.Complexity
