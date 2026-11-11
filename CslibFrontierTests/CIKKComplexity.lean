/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity

/-! Usage checks for the size of the CIKK learner's hypotheses: the closed form bounds every
hypothesis for a test of bounded size, it evaluates at small parameters, and the bound for one run
of the amplification reconstruction composes with the Nisan–Wigderson hypothesis bound. -/

namespace CslibFrontierTests.CIKKComplexity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG.NisanWigderson
  Cslib.MachineLearning Cslib.MachineLearning.UniformLearning

/-- **A test of size at most `c`** gives hypotheses of size at most
`2 ^ (11 g + 9 e + 3 ℓ + 80) (c + 1)`, on every target and seed. -/
example (n ℓ e g h c : ℕ) (test : BitString (2 ^ ℓ) → Bool)
    (htest : complexity interpretation (single test) ≤ c) (f : BooleanFunction n) (ω) :
    complexity interpretation (single ((cikkLearner n ℓ e g h test ω).eval f)) ≤
      2 ^ (11 * g + 9 * e + 3 * ℓ + 80) * (c + 1) :=
  (complexity_eval_cikkLearner_le_two_pow n ℓ e g h test f ω).trans (by gcongr)

/-- At `ℓ = e = g = 0` the closed form is `2 ^ 80 (c + 1)`. -/
example (n h : ℕ) (test : BitString (2 ^ 0) → Bool) (f : BooleanFunction n) (ω) :
    complexity interpretation (single ((cikkLearner n 0 0 0 h test ω).eval f)) ≤
      2 ^ 80 * (complexity interpretation (single test) + 1) :=
  complexity_eval_cikkLearner_le_two_pow n 0 0 0 h test f ω

/-- **One run** of the amplification reconstruction around the Nisan–Wigderson learner: the
Nisan–Wigderson bound feeds the bound of the reconstruction. -/
example {k n ℓ : ℕ} (test : BitString (2 ^ ℓ) → Bool) (s m K : ℕ) (f : BooleanFunction n) (t)
    (a : AmpSeed n k s m K) :
    complexity interpretation (single
        ((ampLearner (nwLearner (Design.binaryPolynomial (k * n + k) ℓ) test) s m K (t, a)).eval
          f)) ≤
      m * (s + 1) * ((2 ^ K - 1) * (complexity interpretation (single test) +
          2 ^ ℓ * (2 ^ (ℓ - 1) * (2 * (ℓ - 1) + 3) + 1) + 1 + 1) +
        (8 + 2 * (2 ^ K - 1) * (2 ^ K + 1))) + 3 * m + 1 :=
  complexity_eval_ampLearner_le _ s m K f t a (complexity_eval_nwLearner_le _ _ _ _)

end CslibFrontierTests.CIKKComplexity
