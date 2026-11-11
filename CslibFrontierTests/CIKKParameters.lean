/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.BestOf
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Parameters

/-! Usage checks for the parameters of the CIKK learner: the instances resolve, the size bound
on `k` evaluates, the list condition has the `ℕ`-subtraction form of its consumer, and the
best-of conditions discharge `learns_bestOf_of_success` for a learner
with the success probability of the amplification stage. -/

namespace CslibFrontierTests.CIKKParameters

open Cslib Cslib.MachineLearning Cslib.MachineLearning.UniformLearning
  Cslib.MachineLearning.UniformLearning.QueryLearner

/-- The run count is nonzero, as `bestOf` requires. -/
example (e g h : ℕ) : cikkRuns e g h ≠ 0 := NeZero.ne _

/-- The fixed set of the direct-product decoder fits in the direct-product length, also as the
instance the seed distribution of the amplification stage uses. -/
example (e g : ℕ) : cikkFixed e g ≤ cikkK e g := cikkFixed_le_cikkK e g

example (e g : ℕ) : Fact (cikkFixed e g ≤ cikkK e g) := inferInstance

/-- At error `1/2` (`e = 1`) and any advantage `2^{-g}`, `k` is at most `2 ^ 11 (6g + 39)`. -/
example (g : ℕ) : cikkK 1 g ≤ 2 ^ 11 * (6 * g + 39) := by
  simpa using cikkK_le 1 g

/-- The list condition, with `2^K - 1` computed in `ℕ`. -/
example (e g : ℕ) :
    (cikkK e g : ℝ) ≤ 2 * (1 / 2 ^ g / 2) ^ 2 * ((2 ^ cikkMasks e g - 1 : ℕ) : ℝ) :=
  cikkK_le_cikkMasks e g

/-- The best-of conditions boost a learner that succeeds with probability `γ δ₀² / 8`, with
`γ = 2^{-g}` and `δ₀ = γ / 2^{K+3}`, to confidence `1 - 2^{-h}` at error `ε + 2^{-(e+1)}`. -/
example {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε : ℝ} (e g h : ℕ)
    (hA : A.Learns μ C ε (1 - 1 / 2 ^ g * ((1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8))) :
    (bestOf A (cikkRuns e g h) (cikkSamples e g h)).Learns
      (bestOfSeed μ (cikkRuns e g h) (cikkSamples e g h)) C (ε + 2 * (1 / 2 ^ (e + 2)))
      (1 / 2 ^ h) := by
  have hγ : (1 : ℝ) / 2 ^ g ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hδ : (1 : ℝ) / 2 ^ g / 2 ^ (cikkMasks e g + 3) ≤ 1 :=
    (div_le_one (by positivity)).2 (hγ.trans (one_le_pow₀ (by norm_num)))
  refine learns_bestOf_of_success hA ?_ (by positivity) (by positivity) (log_le_cikkRuns e g h)
    (log_le_cikkSamples e g h)
  have hsq : ((1 : ℝ) / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8 ≤ 1 := by
    have := pow_le_one₀ (n := 2) (by positivity) hδ
    linarith
  exact (mul_le_mul hγ hsq (by positivity) zero_le_one).trans_eq (one_mul 1)

end CslibFrontierTests.CIKKParameters
