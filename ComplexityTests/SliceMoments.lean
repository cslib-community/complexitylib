/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.PairwiseIndependentHash.SliceFourthMoment
import Complexity.Probability.PairwiseIndependentHash.ValidatedWords

/-!
# Fourth moments and validated words on retention slices

A concrete valid wrap of an inverse generator inside the box `{-3, …, 3} ^ H`, fourth-moment
conditional averaging over two channels and free bits with every hypothesis discharged, and a
client combining validated words with the `L²` gap: the validated estimator, computed without
referring to the identifier except through the wrap tests, concentrates at the conditional mean.
-/

namespace ComplexityTests.SliceMoments

open Cslib Cslib.Probability Cslib.RotationMap Finset
open scoped BigOperators

-- The inverse of the translation by `e_0` maps the value `(0, 2)` to `(-1, 2)`; the valid wrap
-- `1` brings it back to `(2, 2)` in the box `{0, 1, 2} ^ 2`.
example : wrap 3 (signedMove (affineGenerator 2 (.inr 0)) true).1
    (signedMove (affineGenerator 2 (.inr 0)) true).2 (![0, 2] : Fin 2 → ZMod 5) = ![1, 0] := by
  decide
example : IsValidWrap 3 (signedMove (affineGenerator 2 (.inr 0)) true).1
    (signedMove (affineGenerator 2 (.inr 0)) true).2 ![1, 0] (![0, 2] : Fin 2 → ZMod 5) := by
  decide

instance (j : Fin 2) : Fact (![5, 7] j).Prime := by
  fin_cases j
  exacts [⟨Nat.prime_five⟩, ⟨by decide⟩]

instance (j : Fin 2) : NeZero (![3, 4] j) := by
  fin_cases j
  exacts [⟨by norm_num⟩, ⟨by norm_num⟩]

/-- **Fourth-moment conditional averaging over two channels and free bits, with every hypothesis
discharged**: channels over `𝔽₅` and `𝔽₇` with sides `3` and `4` and free bits in `(ZMod 8) ^ 3`;
`2 t` steps multiply the fourth central moment by at most `2 (1 - 1 / 37822464) ^ (2 t)`. -/
example (y : ∀ j : Fin 2, ZMod (![5, 7] j))
    (f : (∀ j, RetentionSlice (![5, 7] j) 3 1 (![3, 4] j) (y j)) × (Fin 3 → ZMod 8) → ℝ)
    (t : ℕ) :
    𝔼 A, ((((ofPerms (componentMove 3 8 ![5, 7] ![3, 4])).lazy.reindex
        (componentEquiv 8 (fun j ↦ by fin_cases j <;> decide) y).symm).walk ^ (2 * t)) f A -
          𝔼 B, f B) ^ 4 ≤ 2 * (1 - 1 / 37822464) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 4 := by
  have h := expect_walk_pow_componentMove_sub_expect_pow_four_le le_rfl
    (fun j ↦ by fin_cases j <;> decide) y f t
  norm_num at h ⊢
  exact h

/-- **The validated estimator concentrates**: for every prime `P`, side `L ≤ P` and identifier `y`,
and every function `f` of the channel, `t` iterations of the validated step of the affine
generators, evaluated on the retention slice of `y`, have variance at most
`(1 - 1 / (155648 H ^ 4)) ^ (2 t)` times the conditional variance of `f`. -/
example {P L H : ℕ} [Fact P.Prime] [NeZero L] [NeZero H] (hH : 3 ≤ H) (hL : L ≤ P) (y : ZMod P)
    (f : FrameChannel P H 1 → ℝ) (t : ℕ) :
    𝔼 A : RetentionSlice P H 1 L y,
        ((validatedStep L (affineGenerator H) (Fintype.piFinset fun _ ↦ Icc (-3) 3) y)^[t] f A.1 -
          𝔼 B : RetentionSlice P H 1 L y, f B.1) ^ 2 ≤
      (1 - 1 / (155648 * H ^ 4)) ^ (2 * t) *
        𝔼 A : RetentionSlice P H 1 L y, (f A.1 - 𝔼 B : RetentionSlice P H 1 L y, f B.1) ^ 2 := by
  have h := expect_walk_pow_sliceGraph_affineMove_sub_expect_sq_le hH hL y (fun B ↦ f B.1) t
  simp only [walk_pow_sliceGraph_lazy_affineMove_eq] at h
  exact h

end ComplexityTests.SliceMoments
