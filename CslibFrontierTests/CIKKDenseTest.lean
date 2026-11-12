/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CIKK.DenseTest
import CslibFrontier.MachineLearning.UniformLearning.CIKK.PPoly

/-! Usage checks for the per-length steps from a dense test to the CIKK learner: the De Morgan
form with the functions of high circuit complexity as the test, and the constant-depth form with
the largest test its usefulness hypothesis allows. -/

namespace CslibFrontierTests.CIKKDenseTest

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MachineLearning.UniformLearning

/-- **The hard functions as the test.** For `16 ≤ ℓ`, at least half of the functions on `ℓ` bits
have De Morgan circuit complexity above `2 ^ ℓ / (5 ℓ)`. When `cikkPPolyBound` is at most that
threshold, the CIKK learner with `g = ℓ + 2` whose test accepts those functions learns the
functions on `n` bits of complexity at most `s`. -/
example {n ℓ : ℕ} (s e h : ℕ) (hℓ : 16 ≤ ℓ)
    (hP : cikkPPolyBound n ℓ e (ℓ + 2) s ≤ 2 ^ ℓ / (5 * ℓ)) :
    (cikkLearner n ℓ e (ℓ + 2) h
        (truthTableTest {f : BooleanFunction ℓ |
          2 ^ ℓ / (5 * ℓ) < complexity interpretation (single f)})).Learns
      (cikkSeed n ℓ e (ℓ + 2) h) {f | complexity interpretation (single f) ≤ s}
      (1 / 2 ^ e) (1 / 2 ^ h) := by
  refine learns_cikkLearner_of_lt_complexity s e (ℓ + 2) h ?_ fun F hF => hP.trans_lt hF
  have hhalf := two_pow_two_pow_le_two_mul_ncard_setOf_lt_complexity hℓ
  calc 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1)
      ≤ 2 * {f : BooleanFunction ℓ |
          2 ^ ℓ / (5 * ℓ) < complexity interpretation (single f)}.ncard * 2 ^ (ℓ + 1) :=
        Nat.mul_le_mul_right _ hhalf
    _ = 2 ^ (ℓ + 2) * {f : BooleanFunction ℓ |
          2 ^ ℓ / (5 * ℓ) < complexity interpretation (single f)}.ncard := by ring

/-- **The largest test.** The functions on `ℓ` bits computed by no `σ`-circuit of depth at most
`d + 7` and size at most `k s + 6 (k n + k)² + 3` satisfy the usefulness hypothesis by definition,
so when they are dense the CIKK learner with that test learns `σ`-circuits of depth at most `d`
and size at most `s`. -/
example {σ : Signature} {I : Interpretation σ Bool} (φ : Unbounded.extSignature.Hom σ)
    [φ.Preserves (Unbounded.extInterpretation (modGate 2)) I] {n ℓ : ℕ} (d s e g h : ℕ)
    (hdense : 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ g * {F : BooleanFunction ℓ |
      ∀ G : Circuit σ ℓ 1, G.depth ≤ d + 7 →
        G.size ≤ cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3 →
          ¬ G.Computes I (single F)}.ncard) :
    (cikkLearner n ℓ e g h (truthTableTest {F : BooleanFunction ℓ |
      ∀ G : Circuit σ ℓ 1, G.depth ≤ d + 7 →
        G.size ≤ cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3 →
          ¬ G.Computes I (single F)})).Learns (cikkSeed n ℓ e g h)
      {f | ∃ C : Circuit σ n 1, C.Computes I (single f) ∧ C.depth ≤ d ∧ C.size ≤ s}
      (1 / 2 ^ e) (1 / 2 ^ h) :=
  learns_cikkLearner_of_hom φ d s e g h hdense fun G hGd hGs _ hF => hF G hGd hGs

end CslibFrontierTests.CIKKDenseTest
