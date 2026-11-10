/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness

/-!
# SAT, UNSAT and 3SAT in P

Since `SAT` is `NP`-complete (`Cslib.Complexity.CookLevin.SAT_npComplete`), `SAT ∈ P` holds exactly
when `P = NP` for every encoding of instances (`Cslib.Complexity.SAT_mem_P_iff`, a case of
`Cslib.Complexity.NPComplete.mem_P_iff`). Closure of `P` under complement
(`Cslib.Complexity.compl_mem_P`) gives the same for `UNSAT`, and `NP`-completeness of `ThreeSAT`
(`Cslib.Complexity.ThreeSAT_npComplete`) gives it for `ThreeSAT`
[Arora and Barak, Chapter 2][AroraBarak09].

## Main results

* `Cslib.Complexity.SAT_mem_P_iff`: `SAT ∈ P` exactly when `P = NP` for every encoding.
* `Cslib.Complexity.UNSAT_mem_P_iff_SAT_mem_P`, `Cslib.Complexity.ThreeSAT_mem_P_iff_SAT_mem_P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **`SAT ∈ P` exactly when `P = NP`**, for every encoding of instances: `SAT` is
`NP`-complete. -/
theorem SAT_mem_P_iff : SAT ∈ P encCNF ↔ ∀ {β : Type} (e : β ↪ List Bool), P e = NP e :=
  CookLevin.SAT_npComplete.mem_P_iff

/-- `UNSAT ∈ P` exactly when `SAT ∈ P`: `UNSAT` is the complement of `SAT`. -/
theorem UNSAT_mem_P_iff_SAT_mem_P : UNSAT ∈ P encCNF ↔ SAT ∈ P encCNF := by
  rw [← compl_SAT]
  exact ⟨fun h => by simpa using compl_mem_P h, compl_mem_P⟩

/-- `ThreeSAT ∈ P` exactly when `SAT ∈ P`: both are `NP`-complete. -/
theorem ThreeSAT_mem_P_iff_SAT_mem_P : ThreeSAT ∈ P encCNF ↔ SAT ∈ P encCNF :=
  ThreeSAT_npComplete.mem_P_iff_mem_P CookLevin.SAT_npComplete

end Cslib.Complexity
