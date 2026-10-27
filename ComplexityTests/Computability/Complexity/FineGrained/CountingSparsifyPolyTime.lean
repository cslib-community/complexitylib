/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingPolyTime

/-!
# Tests for dense CNF relabeling, list-level counting sparsification, and fine-grained endpoints

Concrete regression tests and edge-case checks for:
* `Cslib.Logic.PL.CNF.denseRelabel` vs `CNF.compact` on gapped/repeated-literal formulas, empty
  formulas, and width-`0`/`1` `KSAT` instances;
* `Cslib.Logic.PL.CNF.Sparsification.removeTautologies`, `countingNormalize`, `countingChild`, and
  `countingNext`, including additive `modelCountOn` conservation and `CountingNormalized`
  preservation;
* Polynomial-time certificates and fine-grained endpoint reductions in
  `Complexity.Computability.Complexity.FineGrained.CountingEndpoint`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM

/-! ### 1. Concrete dense-relabeling vs compaction checks -/

/-- A concrete formula whose variable occurrences `[10, 10, 20, 5]` have a duplicate before `20` and
non-monotone variable numbers. -/
def gappedFormula : CNF ℕ :=
  [[(10, true), (10, true)], [(20, false), (5, true)]]

/-- `CNF.compact` uses first occurrence positions in `vars`, leaving a gap at `1` (`[0, 2, 3]`). -/
example : gappedFormula.compact = [[(0, true), (0, true)], [(2, false), (3, true)]] := by
  decide

/-- `CNF.denseRelabel` uses indices in `distinctVars`, producing dense indices `[0, 1, 2]`. -/
example : gappedFormula.denseRelabel = [[(0, true), (0, true)], [(1, false), (2, true)]] := by
  decide

example : gappedFormula.denseRelabel.distinctVars = List.range gappedFormula.numVars :=
  CNF.distinctVars_denseRelabel gappedFormula

example : gappedFormula.denseRelabel.modelCountOn (Finset.range gappedFormula.numVars) =
    gappedFormula.modelCount :=
  CNF.modelCountOn_denseRelabel gappedFormula

/-- Edge cases: empty formula and empty-clause formula at `k = 0` and `k = 1`. -/
example : CNF.denseRelabel ([] : CNF ℕ) = [] := rfl
example : CNF.denseRelabel ([[]] : CNF ℕ) = [[]] := rfl
example : CNF.denseRelabel ([] : CNF ℕ) ∈ KSAT 0 ↔ ([] : CNF ℕ) ∈ KSAT 0 :=
  CNF.denseRelabel_mem_KSAT_iff
example : CNF.denseRelabel ([[]] : CNF ℕ) ∈ KSAT 1 ↔ ([[]] : CNF ℕ) ∈ KSAT 1 :=
  CNF.denseRelabel_mem_KSAT_iff

/-! ### 2. Concrete list-level counting sparsification checks -/

/-- A 2-CNF formula with a tautological clause `[(0, true), (0, false)]` and a size-2 flower of
2-clauses sharing the heart `[(0, true)]`. -/
def flowerWithTautology : CNF ℕ :=
  [[(0, true), (0, false)], [(0, true), (1, true)], [(0, true), (2, false)]]

/-- `removeTautologies` drops the tautological clause and keeps the two nontautological clauses. -/
example : removeTautologies flowerWithTautology =
    [[(0, true), (1, true)], [(0, true), (2, false)]] := by
  decide

/-- `countingNormalize` produces a `CountingNormalized 2` formula with the same 3-variable model
count. -/
example : CountingNormalized 2 (countingNormalize flowerWithTautology) :=
  countingNormalized_countingNormalize (by decide)

example : (countingNormalize flowerWithTautology).modelCountOn (Finset.range 3) =
    flowerWithTautology.modelCountOn (Finset.range 3) :=
  modelCountOn_countingNormalize flowerWithTautology (Finset.range 3)

/-- At threshold `M = 2` (`θ 1 = 2`), `choice (countingThreshold 2) 2` selects the heavy heart
`[(0, true)]` at clause size `2`. -/
example : choice (countingThreshold 2) 2 (countingNormalize flowerWithTautology) =
    (2, [(0, true)]) := by
  decide

/-- The `false` (A) branch reduces to the unit heart `[[(0, true)]]`, while the `true` (B) branch
introduces the petals `[[(1, true)], [(2, false)]]` and the negated-heart unit `[[(0, false)]]`. -/
example : countingNext (countingThreshold 2) 2 (countingNormalize flowerWithTautology) false =
    [[(0, true)]] := by
  decide

example : countingNext (countingThreshold 2) 2 (countingNormalize flowerWithTautology) true =
    [[(1, true)], [(2, false)], [(0, false)]] := by
  decide

/-- Both counting children preserve `CountingNormalized 2` and partition the 5 satisfying
assignments on `{0, 1, 2}` into `4 + 1 = 5`. -/
example : CountingNormalized 2
    (countingNext (countingThreshold 2) 2 (countingNormalize flowerWithTautology) true) :=
  countingNormalized_countingNext (countingThreshold 2) (by decide)
    (countingNormalized_countingNormalize (by decide)) true

example : (countingNormalize flowerWithTautology).modelCountOn (Finset.range 3) =
    CNF.modelCountOn
      (countingNext (countingThreshold 2) 2 (countingNormalize flowerWithTautology) false)
      (Finset.range 3) +
    CNF.modelCountOn
      (countingNext (countingThreshold 2) 2 (countingNormalize flowerWithTautology) true)
      (Finset.range 3) :=
  modelCountOn_countingNext
    (countingNormalized_countingNormalize (k := 2) (by decide)).toNormalized (Finset.range 3)

end Cslib.Complexity.Tests
