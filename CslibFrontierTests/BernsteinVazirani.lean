/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.BernsteinVazirani

/-! The classical query complexity of Bernstein–Vazirani on concrete instances, and the sharpness of
the error threshold `1/2` in the randomized lower bound. -/

namespace CslibFrontierTests.BernsteinVazirani

open Cslib Cslib.QueryComplexity Cslib.BitString Convexity

/-- The positions `Fin 4` identified with `{0,1}^2`. -/
noncomputable def e4 : Fin 4 ≃ (Fin 2 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The hidden string `s = 10`. -/
def s10 : Fin 2 → Bool := ![true, false]

-- Querying the unit vectors recovers the hidden string.
example : linearDecode e4 (linearTable e4 s10) = s10 := linearDecode_linearTable e4 s10

-- The unit-vector tree computes the decoder with two queries.
example : (linearDecodeTree e4).Computes (linearDecode e4) := linearDecodeTree_computes e4

example : (linearDecodeTree e4).depth ≤ 2 := depth_linearDecodeTree_le e4

-- The deterministic and bounded-error randomized complexities are exactly `n = 2`.
example : DecisionTree.complexity (linearDecode e4) = 2 := by
  rw [complexity_linearDecode, Fintype.card_fin]

example : randomizedComplexity (1 / 3) (linearDecode e4) = 2 := by
  rw [randomizedComplexity_linearDecode e4 (by norm_num) (by norm_num), Fintype.card_fin]

-- A single query does not suffice: no tree of depth `1` recovers `s`.
example (t : DecisionTree (Fin 4) (Fin 2 → Bool)) (ht : ∀ s, t.eval (linearTable e4 s) = s) :
    2 ≤ t.depth := by
  simpa using card_le_depth_of_linearTable e4 t ht

/-! ### The threshold `1/2` is sharp

With `n = 1` and `N = 2`, guessing `s` uniformly without querying errs with probability exactly
`1/2` on every input and has depth `0 < n`. So the hypothesis `ε < 1/2` of
`card_le_depth_of_linearTable_randomized` cannot be relaxed to `ε ≤ 1/2`, and the inequality
`2^n (1 - ε) ≤ 2^q` of `linearTable_randomized_lower_bound` is attained. -/

/-- The positions `Fin 2` identified with `{0,1}^1`. -/
noncomputable def e2 : Fin 2 ≃ (Fin 1 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The randomized decision tree that outputs a uniformly random string of `{0,1}^1` without
querying. -/
noncomputable def guess : RandomizedDecisionTree (Fin 2) (Fin 1 → Bool) :=
  .duple (.leaf fun _ => true) (.leaf fun _ => false) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem weights_guess : guess.weights = Finsupp.single (.leaf fun _ => true) (1 / 2) +
    Finsupp.single (.leaf fun _ => false) (1 / 2) := rfl

theorem depth_guess : guess.depth = 0 := by
  classical
  refine Nat.le_zero.mp (RandomizedDecisionTree.depth_le_iff.mpr fun t ht => ?_)
  rw [weights_guess] at ht
  have h := Finsupp.support_add ht
  simp only [Finset.mem_union] at h
  rcases h with h | h <;> rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)] <;> rfl

theorem errorProb_guess (s : Fin 1 → Bool) :
    guess.errorProb (linearDecode e2) (linearTable e2 s) = 1 / 2 := by
  classical
  rw [RandomizedDecisionTree.errorProb_eq_sum, linearDecode_linearTable]
  rw [weights_guess, Finsupp.sum_add_index' (by simp) (by intros; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  have hs : s = (fun _ => true) ∨ s = (fun _ => false) := by
    cases h : s 0
    · exact Or.inr (funext fun i => by rw [Subsingleton.elim i 0, h])
    · exact Or.inl (funext fun i => by rw [Subsingleton.elim i 0, h])
  rcases hs with rfl | rfl
  · simp only [DecisionTree.eval_leaf]
    norm_num [funext_iff]
  · simp only [DecisionTree.eval_leaf]
    norm_num [funext_iff]

-- Error exactly `1/2` with depth `0 < n = 1`: the threshold `ε < 1/2` cannot be relaxed.
example : guess.depth < Fintype.card (Fin 1) ∧
    ∀ s, guess.errorProb (linearDecode e2) (linearTable e2 s) ≤ 1 / 2 :=
  ⟨by rw [depth_guess]; simp, fun s => (errorProb_guess s).le⟩

-- The counting inequality `2^n (1 - ε) ≤ 2^q` holds with equality for `guess`.
example : (2 : ℝ) ^ Fintype.card (Fin 1) * (1 - 1 / 2) = 2 ^ guess.depth := by
  rw [depth_guess]
  norm_num

end CslibFrontierTests.BernsteinVazirani
