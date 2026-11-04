/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

import Complexity.Foundations.BooleanAnalysis.Concentration
import Complexity.MachineLearning.UniformLearning.LowDegreeClasses

/-! # Spectral concentration and the classes it lets the low-degree algorithm learn

The character of two of three coordinates has all its weight above degree one and total
influence two, so the bound `(t + 1) W^{>t}[f] ≤ I[f]` of O'Donnell's Proposition 3.2 is attained
at `t = 1`. Proposition 3.3 applies at `δ = 1 / 2`, `t = 1` on three bits, where the sets above
degree one are nonempty. The hypotheses of all three learning corollaries are satisfiable: some
number of examples lets the low-degree algorithm learn, with error and confidence `1 / 2`, the
functions of three bits with total influence at most one (degree `3`), the monotone functions of
four bits (degree `7`), and the functions of three bits with noise sensitivity at most `1 / 12` at
rate `1 / 2` (degree `1`). The constant functions have noise sensitivity zero, so that last class
is nonempty.
-/

namespace ComplexityTests.BooleanAnalysisConcentration

open Cslib Cslib.BitString Cslib.MachineLearning.UniformLearning Finset

-- Proposition 3.2 is tight for a character of two coordinates at `t = 1`: both sides are `2`.
example : (1 + 1) * ∑ S with 1 < #S, fourierCoeff (chi ℝ ({0, 1} : Finset (Fin 3))) S ^ 2 = 2 ∧
    totalInfluence (chi ℝ ({0, 1} : Finset (Fin 3))) = 2 := by
  refine ⟨?_, by rw [totalInfluence_chi]; rfl⟩
  simp only [fourierCoeff_chi, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  have hmem : ({0, 1} : Finset (Fin 3)) ∈ ({S | 1 < #S} : Finset (Finset (Fin 3))) := by decide
  rw [sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true hmem)]
  norm_num

-- Proposition 3.3 at `δ = 1 / 2`, `t = 1`: the weight above degree one is at most `3 NS_{1/2}[f]`.
example (f : (Fin 3 → Bool) → Bool) :
    ∑ S with 1 < #S, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      3 * noiseSensitivity (1 / 2) f :=
  sum_fourierCoeff_sq_le_three_mul_noiseSensitivity (by norm_num) (by norm_num) f

-- The functions of three bits with total influence at most one are learned at degree `3`:
-- `2 · 1 ≤ (1 / 2) (3 + 1)`.
example : ∃ m, Learns (lowDegreeLearner (Fin 3) 3 m)
    {f | totalInfluence (fun x => signVal (f x)) ≤ 1} (1 / 2) (1 / 2) :=
  ⟨_, lowDegreeLearner_learns_totalInfluence_le (by norm_num) (by norm_num) (by norm_num)
    (Nat.le_ceil _)⟩

-- The functions of three bits with noise sensitivity at most `(1 / 2) / 6` at rate `1 / 2` are
-- learned at degree `1`: `1 ≤ (1 / 2) (1 + 1)`.
example : ∃ m, Learns (lowDegreeLearner (Fin 3) 1 m)
    {f | noiseSensitivity (1 / 2) f ≤ (1 / 2) / 6} (1 / 2) (1 / 2) :=
  ⟨_, lowDegreeLearner_learns_noiseSensitivity_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Nat.le_ceil _)⟩

-- The monotone functions of four bits are learned at degree `7`: `2 √4 = 4 ≤ (1 / 2) (7 + 1)`.
example : ∃ m, Learns (lowDegreeLearner (Fin 4) 7 m) {f | Monotone f} (1 / 2) (1 / 2) := by
  refine ⟨_, lowDegreeLearner_learns_monotone (by norm_num) (by norm_num) ?_ (Nat.le_ceil _)⟩
  rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

-- A constant function never changes under noise, so it lies in every class of noise-stable
-- functions.
example (η ε : ℝ) (hε : 0 ≤ ε) :
    (fun _ : Fin 3 → Bool => false) ∈ {f | noiseSensitivity η f ≤ ε / 6} := by
  change noiseSensitivity η _ ≤ ε / 6
  simp only [noiseSensitivity, ne_eq, not_true_eq_false, ↓reduceIte, bernoulliAverage_const,
    Fintype.expect_const]
  linarith

end ComplexityTests.BooleanAnalysisConcentration
