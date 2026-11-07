/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.Submodular.LowerBound
import Mathlib.Tactic.NormNum

/-!
# Tests for Submodular Greedy Maximization and Value-Oracle Bounds

Concrete checks covering:
1. Positive and negative instances of `IsSubmodular` (`weightedCoverage` vs quadratic cardinality).
2. Executable `#guard` evaluation and query counting of `submodularGreedy` and
   `submodularGreedyQuery` on a weighted Max-`k`-Cover instance, including duplicate candidates.
3. Exact rational tightness (`1`, `3/4`, `19/27` at `k = 1, 2, 3`) of the Nemhauser–Wolsey family.
4. Non-vacuity and composition of `IsSubmodularCardMaxAlg`, `UpperBound`, and `LowerBound` on `ℕ`.
-/

namespace ComplexityTests.SubmodularGreedy

open Cslib Cslib.Query Cslib.Algorithms.Lean.Submodular

/-! ## Positive and negative examples of `IsSubmodular` -/

/-- Quadratic set-size `|S|^2` on `Fin 2` is strictly supermodular, hence not `IsSubmodular`. -/
theorem not_isSubmodular_sq_card :
    ¬ IsSubmodular (fun S : Finset (Fin 2) => S.card * S.card) := by
  intro h
  have h01 := h {0} {1}
  dsimp only at h01
  have hu : (({0} : Finset (Fin 2)) ∪ {1}).card = 2 := by decide
  have hi : (({0} : Finset (Fin 2)) ∩ {1}).card = 0 := by decide
  have h0 : ({0} : Finset (Fin 2)).card = 1 := by decide
  have h1 : ({1} : Finset (Fin 2)).card = 1 := by decide
  rw [hu, hi, h0, h1] at h01
  omega

/-- Concrete weighted set-coverage instance over universe `Fin 5` and 4 candidate sets `Fin 4`. -/
def demoCover : Fin 4 → Finset (Fin 5)
  | 0 => {0, 1, 2}
  | 1 => {2, 3}
  | 2 => {3, 4}
  | 3 => {0, 4}

def demoWeight : Fin 5 → ℕ
  | 0 => 4
  | 1 => 3
  | 2 => 3
  | 3 => 5
  | 4 => 4

def demoObj : Finset (Fin 4) → ℕ :=
  weightedCoverage demoCover demoWeight

theorem demoObj_isSubmodular : IsSubmodular demoObj :=
  isSubmodular_weightedCoverage demoCover fun u => Nat.zero_le (demoWeight u)

theorem demoObj_monotone : Monotone demoObj :=
  monotone_weightedCoverage demoCover fun u => Nat.zero_le (demoWeight u)

section ExecutableChecks

set_option linter.hashCommand false

def demoOracle : {ι : Type} → ValueQuery (Fin 4) ℕ ι → ι :=
  ValueQuery.oracleOf demoObj

-- Greedy step 1 picks set 0 (weight 4 + 3 + 3 = 10); step 2 picks set 2 (adds 5 + 4 = 9, total 19).
#guard submodularGreedy demoObj [0, 1, 2, 3] 2 == ({0, 2} : Finset (Fin 4))
#guard demoObj (submodularGreedy demoObj [0, 1, 2, 3] 2) == 19

-- `submodularGreedyQuery` evaluates to the exact same subset.
#guard (submodularGreedyQuery [0, 1, 2, 3] 2).eval demoOracle == ({0, 2} : Finset (Fin 4))

-- Round 1 queries 4 candidates; round 2 queries 3 remaining candidates (total 7 ≤ 2 * 4 = 8).
#guard (submodularGreedyQuery [0, 1, 2, 3] 2).countQueries demoOracle == 7

-- Duplicate candidates in `xs` are deduplicated upfront, keeping the exact query count at 7.
#guard (submodularGreedyQuery [0, 1, 0, 2, 3, 2, 1] 2).countQueries demoOracle == 7

-- At budget k = 1, `submodularGreedyQuery` makes exact query count `xs.toFinset.card = 4`.
#guard (submodularGreedyQuery [0, 1, 0, 2, 3] 1).countQueries demoOracle == 4

-- When k exceeds the number of distinct candidates, exhausted rounds issue 0 extra queries
-- (4 + 3 + 2 + 1 + 0 + 0 = 10).
#guard (submodularGreedyQuery [0, 1, 2, 3] 6).countQueries demoOracle == 10

end ExecutableChecks

/-! ## Exact rational tightness at `k = 1, 2, 3` -/

example :
    tightObjective (β := ℚ) 1
        (submodularGreedy (tightObjective (β := ℚ) 1) (tightCandidates 1) 1) = 1 := by
  rw [submodularGreedy_tightObjective_eq (by decide)]
  norm_num

example :
    tightObjective (β := ℚ) 2
        (submodularGreedy (tightObjective (β := ℚ) 2) (tightCandidates 2) 2) = 3 / 4 := by
  rw [submodularGreedy_tightObjective_eq (by decide)]
  norm_num

example :
    tightObjective (β := ℚ) 3
        (submodularGreedy (tightObjective (β := ℚ) 3) (tightCandidates 3) 3) = 19 / 27 := by
  rw [submodularGreedy_tightObjective_eq (by decide)]
  norm_num

/-! ## Real `(1 - 1/e)` guarantee and non-vacuous query upper/lower bounds on `ℕ` -/

example (xs : List ℕ) (k : ℕ) {f : Finset ℕ → ℝ}
    (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    {OPT : Finset ℕ} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * f OPT ≤
      f ((submodularGreedyQuery xs k).eval (ValueQuery.oracleOf f)) :=
  one_sub_exp_neg_one_mul_le_eval_submodularGreedyQuery hf hmono hf0 xs k hOPT_sub hOPT_card

-- Exact multi-round query count formula `∑ t ∈ Finset.range k, (xs.toFinset.card - t)`.
example (oracle : {ι : Type} → ValueQuery ℕ ℝ ι → ι) (xs : List ℕ) (k : ℕ) :
    (submodularGreedyQuery xs k).countQueries oracle =
      ∑ t ∈ Finset.range k, (xs.toFinset.card - t) :=
  countQueries_submodularGreedyQuery_eq oracle xs k

-- Non-vacuity of `IsSubmodularCardMaxAlg` on `ℕ` at ratio `1 - Real.exp (-1)`.
example : IsSubmodularCardMaxAlg (submodularGreedyQuery (α := ℕ) (β := ℝ)) (1 - Real.exp (-1)) :=
  submodularGreedyQuery_isSubmodularCardMaxAlg

-- Composing the `k = 1` lower bound with the `k = 1` upper bound on `ℕ`.
example (n : ℕ) : (if n ≤ 1 then 0 else n) ≤ 1 * n :=
  (submodularGreedyQuery_lowerBound_one (α := ℕ)).le_upperBound
    (submodularGreedyQuery_upperBound 1) n

end ComplexityTests.SubmodularGreedy
