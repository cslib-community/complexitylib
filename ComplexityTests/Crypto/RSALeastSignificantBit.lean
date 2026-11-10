/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Computational.RSALeastSignificantBit
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the least significant bit of RSA
-/

namespace ComplexityTests.Crypto.RSALeastSignificantBit

open Cslib Cslib.Crypto

/-! ### Doubling and parity -/

example : 2 ^ 3 * 5 % 33 % 2 = 2 ^ 3 * 5 / 33 % 2 :=
  two_pow_mul_mod_mod_two (by decide) (by decide) 5

example : 2 ^ (2 * 3) * rsaEval 33 3 5 % 33 = rsaEval 33 3 (2 ^ 2 * 5 % 33) :=
  two_pow_mul_rsaEval 33 3 2 5

example : lsbDigits [true, false, true, true] = 11 := by decide

/-! ### Recovering a preimage from parities

The toy instance `N = 33`, `e = 3`, `d = 7` hides `x = 5` as `y = 26`. The parity oracle that
decrypts with `d` answers the six doubling queries (`Nat.size 33 = 6`), and the answers recover
`x`. -/

example : rsaEval 33 3 5 = 26 := by decide

example : Nat.size 33 = 6 := by decide

example : lsbQueries 33 3 26 6 = [10, 14, 13, 5, 7, 23] := by decide

example : (lsbQueries 33 3 26 6).map (fun query => (rsaInvert 33 7 query).testBit 0) =
    [false, false, true, false, false, true] := by decide

example : lsbRecover 33 6 ((lsbQueries 33 3 26 6).map fun query =>
    (rsaInvert 33 7 query).testBit 0) = 5 := by decide

/-- The same recovery from the general statement: the decrypting oracle is correct on every RSA
image modulo `33`. -/
example : lsbRecover 33 6 ((lsbQueries 33 3 (rsaEval 33 3 5) 6).map fun query =>
    (rsaInvert 33 7 query).testBit 0) = 5 := by
  have hdesc : RSADescValid ((3, 11), (3, 7)) := by
    refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  refine lsbRecover_lsbQueries (by decide) (by decide) (by decide) _ fun z hz => ?_
  exact congrArg (Nat.testBit · 0) (rsaInvert_rsaEval ⟨_, hdesc⟩ hz)

/-! ### The inverter on a perfect predictor -/

/-- The toy RSA parameters `N = 3 * 11`, `e = 3`, `d = 7`. -/
def desc33 : RSADesc :=
  ⟨((3, 11), (3, 7)), ⟨by norm_num, by norm_num, by decide, by decide, by decide⟩⟩

/-- The predictor that decrypts with `d = 7` and returns the parity: it is always correct on the
toy key, so it satisfies the hypotheses of `eval_lsbInverter`. -/
def perfectPredictor : ℕ → RSAPublicKey × ℕ → ProbComp Bool :=
  fun _ input => pure ((rsaInvert 33 7 input.2).testBit 0)

theorem perfectPredictor_correct (n : ℕ) : ∀ z < desc33.publicKey.N,
    ProbComp.eval (perfectPredictor n
      (desc33.publicKey, rsaEval desc33.publicKey.N desc33.publicKey.e z)) =
      PMF.pure (z.testBit 0) := by
  intro z hz
  simp only [perfectPredictor, ProbComp.eval_pure]
  exact congrArg (fun x => PMF.pure (x.testBit 0)) (rsaInvert_rsaEval desc33 hz)

/-- `lsbInverter` recovers `x = 5` from `y = 26` with certainty. -/
example (n : ℕ) :
    ProbComp.eval (lsbInverter perfectPredictor n
      (desc33.publicKey, rsaEval desc33.publicKey.N desc33.publicKey.e 5)) = PMF.pure 5 :=
  eval_lsbInverter (by decide) (perfectPredictor_correct n) (by decide)

/-- With the constant generator `desc33`, the inverter wins the RSA inversion experiment with
probability one. -/
example (n : ℕ) : Game.succProbability
    (rsaInversionGame (fun _ => PMF.pure desc33) (lsbInverter perfectPredictor) n) = 1 := by
  refine succProbability_rsaInversionGame_lsbInverter ?_ ?_
  · intro desc hdesc
    rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    decide
  · intro desc hdesc
    rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    exact perfectPredictor_correct n

end ComplexityTests.Crypto.RSALeastSignificantBit
