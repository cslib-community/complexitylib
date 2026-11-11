/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson.BestOf
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Carmosino–Impagliazzo–Kabanets–Kolokolova Theorem 2.11 in library form, on the design of two
disjoint singletons: a dense test that avoids the generator of the constant function `false`
yields, with `8` runs and `1000` sample points, a learner with error `1 / 2 - 3 / 32` and
confidence `1 / 2`. -/

namespace CslibFrontierTests.NisanWigdersonBestOf

open Cslib Cslib.Crypto.PRG.NisanWigderson Cslib.MachineLearning.UniformLearning Cslib.Probability
  Finset

/-- The design of two disjoint singletons on two seed bits. -/
def D : Design 2 1 0 2 where
  block := ![{0}, {1}]
  card_block := by decide
  card_inter_le := by decide

/-- A test accepting the strings with a `true` bit. -/
def test (y : Fin 2 → Bool) : Bool := y 0 || y 1

/-- `8` runs and `1000` sample points make at most `8 · 2 + 1000` queries. -/
example : (QueryLearner.bestOf (nwLearner D fun y => !test y) 8 1000).QueriesAtMost
    (8 * (2 * 2 ^ 0) + 1000) :=
  bestOf_nwLearner_queriesAtMost D _

/-- The test accepts three quarters of all strings and no output of the generator of the constant
function `false`. Selecting the best of `8` runs on `1000` sample points learns the class
`{fun _ => false}` with error `1 / 2 - 3 / 32` and confidence `1 / 2`. -/
example : (QueryLearner.bestOf (nwLearner D fun y => !test y) 8 1000).Learns
    (QueryLearner.bestOfSeed (PMF.uniformOfFintype (Trial 2 2)) 8 1000) {fun _ => false}
    (1 / 2 - 3 / 4 / (4 * 2)) (1 / 2) := by
  have hcard : #{y : Fin 2 → Bool | test y = true} = 3 := by decide
  have h2 := Real.log_two_lt_d9
  refine bestOf_nwLearner_learns_of_dens D test (C := {fun _ => false}) (δ := 3 / 4)
    (by norm_num) (by rw [Finset.nnratCast_dens, hcard]; simp) (by rintro f rfl z; rfl)
    (by norm_num) ?_ ?_
  · -- `log 4 = 2 log 2 ≤ 3/2`
    have h4 : Real.log (2 / (1 / 2)) = 2 * Real.log 2 := by
      rw [show (2 : ℝ) / (1 / 2) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    norm_num at h2 ⊢
    linarith
  · -- `8 log 64 = 48 log 2 ≤ 1000 (3/16)²`
    have h64 : Real.log (4 * (8 : ℕ) / (1 / 2)) = 6 * Real.log 2 := by
      rw [show (4 : ℝ) * (8 : ℕ) / (1 / 2) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    rw [h64]
    norm_num at h2 ⊢
    linarith

end CslibFrontierTests.NisanWigdersonBestOf
