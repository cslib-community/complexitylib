/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Computational.RSALeastSignificantBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.Sampling
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the least significant bit of RSA
-/

public section

namespace CslibFrontierTests.Crypto.RSALeastSignificantBit

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### Doubling and parity -/

example : 2 ^ 3 * 5 % 33 % 2 = 2 ^ 3 * 5 / 33 % 2 :=
  two_pow_mul_mod_mod_two (by decide) (by decide) 5

example : 2 ^ (2 * 3) * rsaEval 33 3 5 % 33 = rsaEval 33 3 (2 ^ 2 * 5 % 33) :=
  two_pow_mul_rsaEval 33 3 2 5

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

/-- The toy RSA parameters `N = 3 * 11`, `e = 3`, `d = 7`. -/
def desc33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- The same recovery from the general statement: the decrypting oracle is correct on every RSA
image modulo `33`. -/
example : lsbRecover 33 6 ((lsbQueries 33 3 (rsaEval 33 3 5) 6).map fun query =>
    (rsaInvert 33 7 query).testBit 0) = 5 := by
  refine lsbRecover_lsbQueries (by decide) (by decide) (by decide) _ fun z hz => ?_
  exact congrArg (Nat.testBit · 0) (rsaInvert_rsaEval desc33 hz)

/-! ### The inverter on a perfect predictor -/

/-- The predictor that decrypts with `d = 7` and returns the parity: it is always correct on the
toy key, so it satisfies the hypotheses of `eval_lsbInverter`. -/
def perfectPredictor : RSAPredictor :=
  fun _ _ y => pure ((rsaInvert 33 7 y).testBit 0)

theorem perfectPredictor_correct (n : ℕ) (z : Fin desc33.modulus) :
    ProbComp.eval (perfectPredictor n desc33.publicKey (desc33.publicKey.eval z)) =
      PMF.pure ((z : ℕ).testBit 0) := by
  simp only [perfectPredictor, ProbComp.eval_pure, RSAPublicKey.val_eval]
  exact congrArg (fun x => PMF.pure (x.testBit 0)) (rsaInvert_rsaEval desc33 z.isLt)

/-- `lsbInverter` recovers `x = 5` from `y = 26` with certainty. -/
example (n : ℕ) :
    ProbComp.eval (lsbInverter perfectPredictor n desc33.publicKey (desc33.publicKey.eval 5)) =
      PMF.pure 5 :=
  eval_lsbInverter (by decide) (perfectPredictor_correct n) 5

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

/-! ### Efficiency certificates and noiseless `RSAOneWay` consequence -/

/-- Query generation is uniform polynomial-time on `RSAInput`. -/
example : ComputableInPolyTime
    (fun x : RSAInput => lsbQueries x.publicKey.N x.publicKey.e x.challenge x.publicKey.N.size)
    encRSAInput (encList encNat) :=
  computableInPolyTime_lsbQueries (by fun_prop) (by fun_prop)
    (RSAInput.computableInPolyTime_challenge_val (by fun_prop))
    (ComputableInPolyTime.binary_size.comp (by fun_prop))
    (fun x => x.challenge.pos)

/-- Recovery arithmetic is uniform polynomial-time on `(RSAInput, List Bool)`. -/
example : ComputableInPolyTime
    (fun p : RSAInput × List Bool => lsbRecover p.1.publicKey.N p.1.publicKey.N.size p.2)
    (encPair encRSAInput (encList encBool)) encNat :=
  computableInPolyTime_lsbRecover (by fun_prop)
    (ComputableInPolyTime.binary_size.comp (by fun_prop)) (by fun_prop)

/-- The toy trapdoor predictor `perfectPredictor` runs in uniform strict polynomial time. -/
theorem perfectPredictor_isPPT : perfectPredictor.IsPPT := by
  have hinv : ComputableInPolyTime
      (fun x : RSAInput => rsaInvert 33 7 x.challenge) encRSAInput encNat :=
    computableInPolyTime_rsaInvert (ComputableInPolyTime.const 33)
      (ComputableInPolyTime.const 7)
      (RSAInput.computableInPolyTime_challenge_val (by fun_prop))
      (fun _ => by decide)
  have hbit : ComputableInPolyTime
      (fun x : RSAInput => (rsaInvert 33 7 x.challenge).testBit 0) encRSAInput encBool :=
    .of_tidy (ComputableTidilyInPolyTime.binary_testBit hinv.tidy
      (ComputableTidilyInPolyTime.const 0))
  exact hbit.isPPTOn

/-- `lsbInverter perfectPredictor` is certified uniform strict PPT via `isPPT_lsbInverter`. -/
theorem lsbInverter_perfectPredictor_isPPT : (lsbInverter perfectPredictor).IsPPT :=
  isPPT_lsbInverter perfectPredictor_isPPT

/-- A genuinely probabilistic uniform-bit predictor also produces a uniform strict-PPT inverter. -/
theorem lsbInverter_uniformPredictor_isPPT :
    (lsbInverter (fun _ _ _ => ProbComp.uniform Bool)).IsPPT :=
  isPPT_lsbInverter (isPPTOn_uniform_bool encRSAInput)

/-- Because `perfectPredictor` is PPT and always correct on `desc33` (`N = 33` odd), the
constant generator `fun _ => PMF.pure desc33` cannot be `RSAOneWay`: a non-vacuous client of
`RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor`. -/
theorem not_rsaOneWay_desc33 : ¬ RSAOneWay (fun _ => PMF.pure desc33) := by
  intro hRSA
  refine hRSA.not_frequently_alwaysCorrect_lsbPredictor
    (Filter.Eventually.of_forall fun _ desc hdesc => ?_) perfectPredictor_isPPT ?_
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
    subst hdesc
    decide
  · exact (Filter.Eventually.of_forall fun n desc hdesc => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hdesc
      subst hdesc
      exact perfectPredictor_correct n).frequently

/-- info: 'Cslib.Crypto.computableInPolyTime_lsbQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_lsbQueries

/-- info: 'Cslib.Crypto.computableInPolyTime_lsbRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.computableInPolyTime_lsbRecover

/-- info: 'Cslib.Crypto.isPPT_lsbInverter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.isPPT_lsbInverter

/--
info: 'Cslib.Crypto.RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor

end CslibFrontierTests.Crypto.RSALeastSignificantBit
