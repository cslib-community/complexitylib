/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Ladner.Basic
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Problems decided stage by stage

Delayed diagonalizations decide the `n`-th word (`Cslib.Complexity.Ladner.word`) at stage `n`,
from a table of the earlier stages that is polynomial-time in `n` in unary. The `P`-bi-immune
problem of `CslibFrontier.Computability.Complexity.Classes.Immune.Construction` and the recursive
complexity cores of `CslibFrontier.Computability.Complexity.Classes.Immune.RecursiveCore` are built
this way. Such a problem is in `E`
(`Cslib.Complexity.Ladner.setOf_index_mem_E_of_computableInPolyTime`): the word `y` has index below
`2 ^ (|y| + 1)`, so the stage of `y` is found by searching the first `2 * 2 ^ |y|` words, in time
polynomial in `|y|` and the padding `2 ^ |y|`
(`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`).

## Main results

* `Cslib.Complexity.Ladner.setOf_index_mem_E_of_computableInPolyTime`: a problem decided at the
  stage of each word, by a decision polynomial-time in the stage in unary, is in `E`.
-/

public section

namespace Cslib.Complexity.Ladner

open Turing.MultiTapeTM

/-- The decision `sel` at the stage of `y`, found among the first `2 * N` stages. -/
private def stageSearch (sel : ℕ → Bool) (p : List Bool × ℕ) : Bool :=
  ((List.range (2 * p.2)).find? fun j => decide (word j = p.1)).elim false sel

/-- Searching the first `2 * N` words for `y` finds its index, when the index is below `2 * N`. -/
private theorem find?_word_eq {y : List Bool} {N : ℕ} (hN : index y < 2 * N) :
    (List.range (2 * N)).find? (fun j => decide (word j = y)) = some (index y) := by
  rw [List.find?_range_eq_some]
  refine ⟨by simp [word_index], List.mem_range.mpr hN, fun j hj => ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  rintro rfl
  rw [index_word] at hj
  exact lt_irrefl _ hj

/-- **Problems decided stage by stage are in `E`.** If the decision `sel n` at stage `n` is
polynomial-time in `n` in unary, then the words `y` with `sel (index y)` form a problem in `E`. -/
theorem setOf_index_mem_E_of_computableInPolyTime {sel : ℕ → Bool}
    (hsel : ComputableInPolyTime sel encUnary encBool) :
    {y : List Bool | sel (index y) = true} ∈ E encBits := by
  have hS : ComputableInPolyTime (stageSearch sel) (encPair encBits encUnary) encBool := by
    unfold stageSearch
    fun_prop
  convert setOf_mem_E_of_computableInPolyTime_pad hS using 1
  ext y
  have hy : index y < 2 * 2 ^ y.length := by
    have := index_add_two_le y
    rw [pow_succ] at this
    omega
  simp only [Set.mem_ofPred_eq, stageSearch, find?_word_eq hy, Option.elim_some]

end Cslib.Complexity.Ladner
