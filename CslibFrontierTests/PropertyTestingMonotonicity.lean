/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PropertyTesting.Monotonicity.EdgeTester

/-! Concrete instances of monotonicity testing on small cubes: a monotone function (the `AND` of
two bits) with no violated edges, accepted with probability one; the anti-dictator `x ↦ ¬ x 0` on
three bits, with an explicit violated edge, its exact distance to monotone and exact acceptance
probability; a nonvacuous instance of the soundness bound with explicit parameters; one trial
being too few; and the degenerate cube of dimension `0`. -/

namespace CslibFrontierTests.PropertyTestingMonotonicity

open Cslib Cslib.BitString Cslib.PCP Finset Function

/-- The `AND` of two bits. -/
def and2 (x : Fin 2 → Bool) : Bool := x 0 && x 1

/-- The anti-dictator on three bits. -/
def antiDictator (x : Fin 3 → Bool) : Bool := !x 0

/-! ### A monotone function -/

theorem violatedEdges_and2 (i : Fin 2) : violatedEdges and2 i = ∅ := by
  revert i
  decide

theorem monotone_and2 : Monotone and2 :=
  monotone_iff_forall_violatedEdges_eq_empty.2 violatedEdges_and2

-- Any number of trials accepts a monotone function with probability one.
example (k : ℕ) : ((edgeTest (Fin 2)).repeatAll k).acceptProb and2 = 1 :=
  acceptProb_repeatAll_edgeTest_of_monotone k monotone_and2

example : distMonotone and2 = 0 := distMonotone_eq_zero_iff.2 monotone_and2

-- `k` trials make at most `2 k` queries.
example (r : Fin 5 → Fin 2 × (Fin 2 → Bool)) :
    (((edgeTest (Fin 2)).repeatAll 5).decisionTree r).depth ≤ 10 :=
  depth_decisionTree_repeatAll_edgeTest_le 5 r

/-! ### A function far from monotone -/

-- The edge from `000` to `100` is violated: the anti-dictator falls from `true` to `false`.
example : ![false, false, false] ∈ violatedEdges antiDictator 0 := by decide

example : ¬ (edgeTest (Fin 3)).Passes antiDictator (0, ![false, false, false]) := by decide

-- All four edges in direction `0` are violated, and none in the other directions.
theorem card_violatedEdges_antiDictator_zero : #(violatedEdges antiDictator 0) = 4 := by decide

theorem violatedEdges_antiDictator_of_ne_zero (i : Fin 3) (hi : i ≠ 0) :
    violatedEdges antiDictator i = ∅ := by
  revert i
  decide

theorem sum_card_violatedEdges_antiDictator : ∑ i, #(violatedEdges antiDictator i) = 4 := by
  decide

example : ¬ Monotone antiDictator := fun h => by
  have := (monotone_iff_forall_violatedEdges_eq_empty.1 h) 0
  have h4 := card_violatedEdges_antiDictator_zero
  rw [this, card_empty] at h4
  exact absurd h4 (by decide)

-- The distance to monotone is exactly `4`: at least the four disjoint violated edges in direction
-- `0`, and at most the distance `4` to the constant function `true`.
theorem distMonotone_antiDictator : distMonotone antiDictator = 4 := by
  refine le_antisymm ?_ ?_
  · calc distMonotone antiDictator ≤ hammingDist antiDictator (fun _ => true) :=
          distMonotone_le monotone_const
      _ = 4 := by decide
  · calc 4 = #(violatedEdges antiDictator 0) := card_violatedEdges_antiDictator_zero.symm
      _ ≤ distMonotone antiDictator := card_violatedEdges_le_distMonotone antiDictator 0

theorem relDistMonotone_antiDictator : relDistMonotone antiDictator = 1 / 2 := by
  rw [relDistMonotone_eq, distMonotone_antiDictator, Fintype.card_fin]
  norm_num

-- Sorting along direction `0` changes the anti-dictator at all eight points and makes it the
-- dictator `x ↦ x 0`.
example : hammingDist antiDictator (sortAlong 0 antiDictator) = 8 := by
  rw [hammingDist_sortAlong, card_violatedEdges_antiDictator_zero]

example : sortAlong 0 antiDictator = fun x => x 0 := by decide

-- One trial accepts the anti-dictator with probability exactly `2 / 3`: a third of the edges of
-- the cube are violated.
theorem acceptProb_edgeTest_antiDictator : (edgeTest (Fin 3)).acceptProb antiDictator = 2 / 3 := by
  have h := one_sub_acceptProb_edgeTest antiDictator
  rw [violatedEdgeFraction_eq, ← Nat.cast_sum, sum_card_violatedEdges_antiDictator,
    Fintype.card_fin] at h
  push_cast at h
  linarith

/-! ### Soundness with explicit parameters -/

-- The hypotheses of the soundness bound are satisfiable: the anti-dictator is `1/2`-far from
-- monotone, and with `n = 3` twelve trials suffice (`2 · 3 ≤ 1/2 · 12`). They make at most `24`
-- queries and accept with probability at most `1 / 3`.
example : ((edgeTest (Fin 3)).repeatAll 12).acceptProb antiDictator ≤ 1 / 3 :=
  acceptProb_repeatAll_edgeTest_le_one_third (ε := 1 / 2) (by norm_num)
    relDistMonotone_antiDictator.ge (by norm_num)

example : ((edgeTest (Fin 3)).repeatAll ⌈2 * 3 / (1 / 2 : ℝ)⌉₊).acceptProb antiDictator ≤ 1 / 3 :=
  acceptProb_repeatAll_edgeTest_ceil_le_one_third (by norm_num) relDistMonotone_antiDictator.ge

-- The exact acceptance probability of twelve trials is `(2/3)^12`, consistent with the bound
-- `(1 - ε / n) ^ k = (5/6)^12`.
example : ((edgeTest (Fin 3)).repeatAll 12).acceptProb antiDictator = (2 / 3) ^ 12 := by
  rw [LocalTest.acceptProb_repeatAll, acceptProb_edgeTest_antiDictator]

-- One trial is too few: it accepts the `1/2`-far anti-dictator with probability `2 / 3 > 1 / 3`.
example : ¬ (edgeTest (Fin 3)).acceptProb antiDictator ≤ 1 / 3 := by
  rw [acceptProb_edgeTest_antiDictator]
  norm_num

/-! ### The cube of dimension `0` -/

-- Every function on the one-point cube is monotone, but there are no edges, so the test, with no
-- random strings, accepts with probability `0`: completeness needs a nonempty index type.
example (f : (Fin 0 → Bool) → Bool) : relDistMonotone f = 0 :=
  relDistMonotone_of_monotone (Subsingleton.monotone f)

example (f : (Fin 0 → Bool) → Bool) : (edgeTest (Fin 0)).acceptProb f = 0 := by
  rw [LocalTest.acceptProb_eq_card_div]
  simp

end CslibFrontierTests.PropertyTestingMonotonicity
