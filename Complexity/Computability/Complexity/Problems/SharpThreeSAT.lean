/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting
public import Complexity.Logics.Propositional.CNF.ThreeCNF.Exact
import Complexity.Computability.Complexity.CookLevin.Counting
import Complexity.Computability.Complexity.FineGrained.BruteForce
import Complexity.Computability.Complexity.Problems.ThreeSATThree.Syntax
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Logics.Propositional.CNF.ThreeCNF.Exact.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# #3SAT and #3SAT-3 are #P-complete

Counting the satisfying assignments of a formula of width at most three (`SharpThreeSAT`) is
`#P`-complete under parsimonious reductions, and so is counting them under the additional bound of
three occurrences per variable (`SharpThreeSATThree`) [Valiant][Valiant1979],
[Arora and Barak, Section 17.3][AroraBarak09].

Hardness: `#SAT` is `#P`-hard (`Cslib.Complexity.CookLevin.SharpSAT_sharpPHard`), and the
count-preserving split into OR gates (`Cslib.Logic.PL.CNF.toExact3CNF`), with the variables
renumbered by `Cslib.Complexity.splitVarToNat`, is a parsimonious reduction from `#SAT` to `#3SAT`.
The existing occurrence compiler `Cslib.Complexity.toThreeSATThree` then reduces `#3SAT` to
`#3SAT-3`. Membership: on inputs passing their syntactic guard both counts equal `#SAT`, and
otherwise they are zero, which is the count of the formula `[[]]`; guarding the input is a
parsimonious reduction to `#SAT ∈ #P`.

## Main definitions

* `Cslib.Complexity.toSharpThreeSAT`: the parsimonious reduction from `#SAT` to `#3SAT`.

## Main results

* `Cslib.Complexity.sharpThreeSAT_toSharpThreeSAT`: the reduction preserves counts.
* `Cslib.Complexity.computableInPolyTime_toSharpThreeSAT`: it is polynomial-time.
* `Cslib.Complexity.parsimoniousReducible_SharpSAT_SharpThreeSAT`: `#SAT` reduces
  parsimoniously to `#3SAT`.
* `Cslib.Complexity.SharpThreeSAT_sharpPComplete`: `#3SAT` is `#P`-complete.
* `Cslib.Complexity.SharpThreeSATThree_sharpPComplete`: `#3SAT-3` is `#P`-complete.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The count-preserving reduction from `#SAT` to `#3SAT`: split every clause into OR gates and
number the original and gate variables injectively. -/
def toSharpThreeSAT (φ : CNF ℕ) : CNF ℕ := φ.toExact3CNF.relabel splitVarToNat

/-- `toSharpThreeSAT` has width at most three and the same number of satisfying assignments. -/
theorem sharpThreeSAT_toSharpThreeSAT (φ : CNF ℕ) :
    SharpThreeSAT (toSharpThreeSAT φ) = SharpSAT φ := by
  have hw : ((toSharpThreeSAT φ).all fun c => decide (c.length ≤ 3)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, toSharpThreeSAT, CNF.relabel, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    simpa using CNF.length_le_three_of_mem_toExact3CNF hc
  simp only [SharpThreeSAT, hw, ↓reduceIte]
  simp only [SharpSAT, toSharpThreeSAT, CNF.modelCount_relabel splitVarToNat_injective,
    CNF.modelCount_toExact3CNF]

/-- The reduction `toSharpThreeSAT` is computable in polynomial time under `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_toSharpThreeSAT :
    ComputableInPolyTime toSharpThreeSAT encCNF encCNF :=
  (CNF.computableInPolyTime_relabel computableInPolyTime_splitVarToNat).comp
    (CNF.isPolyTime_toExact3CNF encNat)

/-- **`#SAT` reduces parsimoniously to `#3SAT`.** -/
theorem parsimoniousReducible_SharpSAT_SharpThreeSAT :
    ParsimoniousReducible encCNF encCNF SharpSAT SharpThreeSAT :=
  ⟨toSharpThreeSAT, computableInPolyTime_toSharpThreeSAT,
    fun φ => (sharpThreeSAT_toSharpThreeSAT φ).symm⟩

/-- A guarded count reduces parsimoniously to `#SAT`: replace a rejected input by the
unsatisfiable formula `[[]]`. -/
private theorem parsimoniousReducible_guard {g : CNF ℕ → Bool}
    (hg : ComputableInPolyTime g encCNF encBool) :
    ParsimoniousReducible encCNF encCNF (fun φ => if g φ then SharpSAT φ else 0) SharpSAT := by
  refine ⟨fun φ => if g φ then φ else [[]], hg.ite (by fun_prop) (by fun_prop), fun φ => ?_⟩
  by_cases h : g φ = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    decide

/-- **`#3SAT` is `#P`-complete** [Valiant][Valiant1979]. -/
theorem SharpThreeSAT_sharpPComplete : SharpPComplete encCNF SharpThreeSAT :=
  ⟨(parsimoniousReducible_guard (computableInPolyTime_all_length_le 3)).mem_SharpP
      SharpSAT.mem_SharpP,
    CookLevin.SharpSAT_sharpPHard.trans parsimoniousReducible_SharpSAT_SharpThreeSAT⟩

/-- **`#3SAT-3` is `#P`-complete**: counting stays `#P`-complete when every variable occurs at
most three times. -/
theorem SharpThreeSATThree_sharpPComplete : SharpPComplete encCNF SharpThreeSATThree :=
  ⟨(parsimoniousReducible_guard ThreeSATThree.computableInPolyTime_syntaxCheck).mem_SharpP
      SharpSAT.mem_SharpP,
    SharpThreeSAT_sharpPComplete.2.trans parsimoniousReducible_SharpThreeSAT_SharpThreeSATThree⟩

end Cslib.Complexity
