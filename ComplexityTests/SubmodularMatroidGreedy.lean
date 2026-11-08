/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.Submodular.MatroidGreedy
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.Fintype.Fin

/-!
# Tests for Greedy Submodular Maximization over Matroids and `p`-Systems

Checks covering:
1. The tight partition-matroid instance: executable `#guard` runs of `submodularMatroidGreedy`
   and `submodularMatroidGreedyQuery`, exact value- and independence-query counts (also with
   duplicate ground elements and an empty ground list), and the `1/2` bound applied to it.
2. Matchings of the path `a - b - c - d` (edges `0 = ab`, `1 = bc`, `2 = cd`): a `2`-system, as
   the intersection of two partition matroids, that is not a `1`-system, hence not a matroid.
   Greedy is exactly `1/2`-optimal on a modular objective there, so the Jenkyns bound
   `∑ O w ≤ p • ∑ G w` is attained at `p = 2`; the submodular `1/(p+1)` bound is applied as well.
3. A hereditary family that is a `p`-system for no `p`, since `∅` is not independent.
4. Non-vacuous applications of the general bounds on `ℕ` and `ℝ`, and the uniform query bound.
-/

namespace ComplexityTests.SubmodularMatroidGreedy

open Cslib Cslib.Query Cslib.Algorithms.Lean.Submodular Cslib.Algorithms.Lean.Matroid

/-! ## 1. The tight partition-matroid instance -/

/-- Value and independence oracle of the tight instance. -/
private def tightOracle : {ι : Type} → ValueIndepQuery (Fin 3) ℤ ι → ι :=
  SumQuery.combine (ValueQuery.oracleOf matroidTightObjective)
    (IndepQuery.oracleOf matroidTightIndep)

section TightChecks
set_option linter.hashCommand false

-- Greedy picks `0`, then `2` (`1` is blocked by `0`), with value `1` against the optimum `2`.
#guard submodularMatroidGreedy matroidTightObjective matroidTightIndep [0, 1, 2] == {0, 2}
#guard matroidTightObjective {0, 2} == 1
#guard matroidTightObjective {1, 2} == 2
#guard (submodularMatroidGreedyQuery [0, 1, 2]).eval tightOracle == ({0, 2} : Finset (Fin 3))

-- Rounds `t = 0, 1, 2` test `3 + 2 + 1 = 6` independence queries; the feasible candidates are
-- `{0, 1, 2}`, then `{2}`, then none, so `3 + 1 = 4` value queries.
#guard SumQuery.countInr tightOracle (submodularMatroidGreedyQuery [0, 1, 2]) == 6
#guard SumQuery.countInl tightOracle (submodularMatroidGreedyQuery [0, 1, 2]) == 4
#guard (submodularMatroidGreedyQuery [0, 1, 2]).countQueries tightOracle == 10

-- Duplicate ground elements are removed first, so output and counts are unchanged.
#guard (submodularMatroidGreedyQuery [0, 1, 0, 2, 1]).eval tightOracle == ({0, 2} : Finset (Fin 3))
#guard SumQuery.countInr tightOracle (submodularMatroidGreedyQuery [0, 1, 0, 2, 1]) == 6
#guard SumQuery.countInl tightOracle (submodularMatroidGreedyQuery [0, 1, 0, 2, 1]) == 4

-- An empty ground list makes no query of either kind.
#guard (submodularMatroidGreedyQuery ([] : List (Fin 3))).countQueries tightOracle == 0

end TightChecks

/-- The exact independence-query formula `∑ t ∈ range (|G| + 1), (n - t)` evaluates to `6`. -/
example : SumQuery.countInr tightOracle (submodularMatroidGreedyQuery [0, 1, 2]) = 6 := by
  rw [countInr_submodularMatroidGreedyQuery]
  decide

/-- The tight instance meets every hypothesis of the `1/2` bound, which holds with equality:
`f O + f ∅ = 2 = 2 • f G`. -/
example : matroidTightObjective {1, 2} + matroidTightObjective ∅ ≤
    2 • matroidTightObjective
      (submodularMatroidGreedy matroidTightObjective matroidTightIndep [0, 1, 2]) :=
  add_le_two_nsmul_submodularMatroidGreedy_of_matroid isSubmodular_matroidTightObjective
    monotone_matroidTightObjective matroidTightIndep_iff
    ((matroidTightIndep_iff _).mp (by decide)) (by decide)

/-! ## 2. Matchings of a path: a `2`-system that is not a matroid -/

/-- Matchings of the path `a - b - c - d` with edges `0 = ab`, `1 = bc`, `2 = cd`: the middle edge
conflicts with both others. -/
private def pathIndep (S : Finset (Fin 3)) : Bool :=
  !(decide ((1 : Fin 3) ∈ S) && (decide ((0 : Fin 3) ∈ S) || decide ((2 : Fin 3) ∈ S)))

/-- Path matchings are not a `1`-system: `{1}` blocks both edges of the matching `{0, 2}`. -/
private theorem pathIndep_not_isPSystem_one : ¬ IsPSystem (fun S => pathIndep S = true) 1 := by
  intro h
  have := h.card_le_mul_card_of_blocked (S := {1}) (T := {0, 2}) (by decide) (by decide)
    (by decide)
  exact absurd this (by decide)

/-- Hence path matchings are not the finite independent sets of any matroid. -/
example : ¬ ∃ M : Matroid (Fin 3), ∀ S : Finset (Fin 3), pathIndep S = true ↔ M.Indep (S : Set _) :=
  fun ⟨M, hM⟩ => pathIndep_not_isPSystem_one ((isPSystem_matroid M).of_iff hM)

/-- Second partition matroid of the bipartition `{a, c} ∪ {b, d}`: edges `1 = bc` and `2 = cd` share
the vertex `c`, edge `0 = ab` is alone. (The first one, edges `0` and `1` sharing `b`, is
`matroidTightIndep`.) -/
private def rightIndep (S : Finset (Fin 3)) : Bool :=
  !(decide ((1 : Fin 3) ∈ S) && decide ((2 : Fin 3) ∈ S))

private noncomputable def rightMatroid : Matroid (Fin 3) :=
  (IndepMatroid.ofFinset Set.univ (fun S => rightIndep S = true) (by decide) (by decide)
    (by decide) (fun _ _ => Set.subset_univ _)).matroid

private theorem rightIndep_iff (S : Finset (Fin 3)) :
    rightIndep S = true ↔ rightMatroid.Indep (S : Set (Fin 3)) := by
  simp [rightMatroid]

/-- The two partition matroids, indexed by `Fin 2`. -/
private noncomputable def pathMatroids : Fin 2 → Matroid (Fin 3)
  | 0 => matroidTightMatroid
  | 1 => rightMatroid

/-- Path matchings are exactly the sets independent in both partition matroids. -/
private theorem pathIndep_iff (S : Finset (Fin 3)) :
    pathIndep S = true ↔ ∀ i, (pathMatroids i).Indep (S : Set (Fin 3)) := by
  have h : pathIndep S = true ↔ matroidTightIndep S = true ∧ rightIndep S = true := by
    revert S
    decide
  rw [h, matroidTightIndep_iff, rightIndep_iff, Fin.forall_fin_two]
  rfl

/-- Path matchings form a `2`-system, as the intersection of two matroids. -/
private theorem pathIndep_isPSystem_two : IsPSystem (fun S => pathIndep S = true) 2 :=
  (isPSystem_iInter_matroid pathMatroids).of_iff pathIndep_iff

/-- The blocking form of the `2`-system bound on a concrete pair: `{0, 2}` is blocked by `{1}`, so
`|{0, 2}| ≤ 2 * |{1}|`. -/
example : ({0, 2} : Finset (Fin 3)).card ≤ 2 * ({1} : Finset (Fin 3)).card :=
  pathIndep_isPSystem_two.card_le_mul_card_of_blocked (by decide) (by decide) (by decide)

/-- Unit weights on the edges. -/
private def unitWeight : Fin 3 → ℤ := fun _ => 1

section PathChecks
set_option linter.hashCommand false

-- With unit weights and ground order `[1, 0, 2]`, greedy picks the middle edge first and stops.
#guard submodularMatroidGreedy (modularSum unitWeight) pathIndep [1, 0, 2] == {1}

end PathChecks

/-- **Jenkyns's `1/p` bound is attained at `p = 2`**: on path matchings with unit weights, greedy
returns `{1}` of weight `1`, the matching `{0, 2}` has weight `2`, and `∑ O w ≤ 2 • ∑ G w` is an
equality. -/
example : ∑ x ∈ ({0, 2} : Finset (Fin 3)), unitWeight x =
    2 • ∑ x ∈ submodularMatroidGreedy (modularSum unitWeight) pathIndep [1, 0, 2],
      unitWeight x := by
  decide

example : ∑ x ∈ ({0, 2} : Finset (Fin 3)), unitWeight x ≤
    2 • ∑ x ∈ submodularMatroidGreedy (modularSum unitWeight) pathIndep [1, 0, 2],
      unitWeight x :=
  sum_le_nsmul_sum_submodularMatroidGreedy (fun _ => zero_le_one) pathIndep_isPSystem_two
    (by decide) (by decide)

/-- The `1/(p+1)` bound for the path `2`-system, applied to the coverage objective of the tight
instance and the matching `{0, 2}`: `f O + 2 • f ∅ ≤ 3 • f G`. -/
example : matroidTightObjective {0, 2} + 2 • matroidTightObjective ∅ ≤
    (2 + 1) • matroidTightObjective
      (submodularMatroidGreedy matroidTightObjective pathIndep [1, 0, 2]) :=
  add_nsmul_le_succ_nsmul_submodularMatroidGreedy isSubmodular_matroidTightObjective
    monotone_matroidTightObjective pathIndep_isPSystem_two (by decide) (by decide)

/-! ## 3. A hereditary family that is a `p`-system for no `p` -/

/-- Without the empty set, the never-independent family is not a `p`-system for any `p`. -/
example (p : ℕ) : ¬ IsPSystem (fun _ : Finset (Fin 3) => False) p :=
  fun h => h.indep_empty

/-! ## 4. General bounds on infinite ground types -/

/-- The `1/2` bound for any matroid on `ℕ` and any monotone submodular real objective. -/
example {f : Finset ℕ → ℝ} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    (M : Matroid ℕ) {xs : List ℕ} {O : Finset ℕ} (hO : M.Indep (O : Set ℕ))
    (hOxs : O ⊆ xs.toFinset) :
    f O / 2 ≤ f ((submodularMatroidGreedyQuery xs).eval
      (SumQuery.combine (ValueQuery.oracleOf f) (IndepQuery.matroidOracle M))) :=
  half_le_eval_submodularMatroidGreedyQuery hf hmono hf0
    (IndepQuery.implementsMatroid_matroidOracle M) hO hOxs

/-- The uniform query bound `m (m + 1)` on ground lists of length at most `m`. -/
example : UpperBound (fun xs : List ℕ => submodularMatroidGreedyQuery (β := ℝ) xs)
    List.length (fun m => m * (m + 1)) :=
  submodularMatroidGreedyQuery_upperBound

end ComplexityTests.SubmodularMatroidGreedy
