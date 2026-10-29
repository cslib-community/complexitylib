/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.CookLevin.PolyTime
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# The Cook–Levin theorem

The complete tableau reduction is correct and polynomial-time. Together with the certified SAT
verifier, this proves that SAT is NP-complete under polynomial-time many-one reductions.
Complementation gives coNP-completeness of UNSAT. No reduction-efficiency hypothesis remains in
these statements.

## Main results

* `Cslib.Complexity.CookLevin.SAT_npHard`.
* `Cslib.Complexity.CookLevin.SAT_npComplete`.
* `Cslib.Complexity.CookLevin.UNSAT_coNPComplete`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.2.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

/-- Every NP problem reduces to SAT in polynomial time through its verifier's tableau. -/
theorem SAT_npHard : NPHard encCNF SAT := by
  intro α enc A hA
  obtain ⟨p, V, ⟨t, _, ht, -, k, State, hfin, tm, htm⟩, hV⟩ := mem_NP.mp hA
  obtain ⟨c, d, ht⟩ := polynomiallyBounded_iff_le.mp ht
  have := Fintype.ofFinite State
  classical
  exact ⟨reduce tm p c d enc, computableInPolyTime_reduce tm p c d enc, fun a =>
    (reduce_mem_SAT_iff hV a fun w _ => (htm (a, w)).runFrom_of_le (ht _)).symm⟩

/-- **Cook–Levin:** SAT is NP-complete. -/
theorem SAT_npComplete : NPComplete encCNF SAT :=
  ⟨SAT.mem_NP, SAT_npHard⟩

/-- UNSAT is coNP-complete under polynomial-time many-one reductions. -/
theorem UNSAT_coNPComplete : coNPComplete encCNF UNSAT :=
  compl_SAT ▸ SAT_npComplete.compl

end Cslib.Complexity.CookLevin
