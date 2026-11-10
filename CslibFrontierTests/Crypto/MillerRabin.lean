/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.MillerRabin
import CslibFrontier.Crypto.Computational.ModulusGeneration
import CslibFrontier.Foundations.NumberTheory.Primality.PrimeDensity
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the Miller–Rabin test and random prime generation

Concrete instances of the guarantees in `CslibFrontier/Crypto/Computational/MillerRabin.lean` and
`CslibFrontier/Crypto/Computational/ModulusGeneration.lean`:

* the Carmichael numbers `561 = 3 · 11 · 17` and `1105 = 5 · 13 · 17`, which fool the Fermat test
  for every base coprime to them, pass `t` Miller–Rabin rounds with probability at most `2⁻ᵗ`;
* the primes `2` and `7919` always pass;
* at `n = 16` the random prime generator returns a number that is not prime with probability at
  most `3 · 16² · 2⁻¹⁶`, only returns `16`-bit numbers, and returns the smallest and the largest
  `16`-bit primes, `32771` and `65521`, with the same probability;
* at least a `1 / 48` fraction of the `16`-bit numbers are prime, so at `n = 16` the random prime
  generator fails with probability at most `2⁻¹⁶` and the modulus generator with probability at
  most `1538 · 2⁻¹⁶`;
* the test and both generators are strict PPT programs.
-/

namespace CslibFrontierTests.Crypto.MillerRabin

open Cslib Cslib.Crypto Turing.MultiTapeTM
open scoped ENNReal

/-! ### Carmichael numbers -/

/-- `561` passes `t` Miller–Rabin rounds with probability at most `2⁻ᵗ`. -/
example (t : ℕ) : ProbComp.eval (millerRabinTest 561 t) true ≤ (2 ^ t)⁻¹ :=
  eval_millerRabinTest_le_of_not_prime (by norm_num) t

/-- One round on `561` passes with probability at most `1 / 2`. -/
example : ProbComp.eval (millerRabinRound 561) true ≤ 2⁻¹ :=
  eval_millerRabinRound_le_of_not_prime (by norm_num)

/-- Forty rounds on `1105` pass with probability at most `2⁻⁴⁰`. -/
example : ProbComp.eval (millerRabinTest 1105 40) true ≤ (2 ^ 40)⁻¹ :=
  eval_millerRabinTest_le_of_not_prime (by norm_num) 40

/-- The bound also covers `1`, which is not prime. -/
example (t : ℕ) : ProbComp.eval (millerRabinTest 1 t) true ≤ (2 ^ t)⁻¹ :=
  eval_millerRabinTest_le_of_not_prime Nat.not_prime_one t

/-! ### Primes -/

/-- `2` passes every round. -/
example : ProbComp.eval (millerRabinRound 2) true = 1 :=
  eval_millerRabinRound_of_prime Nat.prime_two

/-- `7919` passes the test with any number of rounds. -/
example (t : ℕ) : ProbComp.eval (millerRabinTest 7919 t) true = 1 :=
  eval_millerRabinTest_of_prime (by norm_num) t

/-- `t` rounds all pass with the `t`-th power of the probability that one round passes. -/
example (n t : ℕ) :
    ProbComp.eval (millerRabinTest n t) true = ProbComp.eval (millerRabinRound n) true ^ t :=
  eval_millerRabinTest_true n t

/-! ### Random primes at `n = 16` -/

/-- A candidate is a given `16`-bit number with probability `2⁻¹⁵`. -/
example : ProbComp.eval (primeCandidate 16) 65521 = (2 ^ 15)⁻¹ :=
  eval_primeCandidate_apply (by norm_num) (by norm_num) (by norm_num)

/-- The generator returns a number that is not prime with probability at most `3 · 16² · 2⁻¹⁶`. -/
example :
    (ProbComp.eval (randomPrime 16)).toOuterMeasure {found | ∃ p, found = some p ∧ ¬ p.Prime} ≤
      3 * 16 ^ 2 * (2 ^ 16)⁻¹ := by
  exact_mod_cast toOuterMeasure_randomPrime_not_prime_le 16

/-- Every output of the generator at `n = 16` is a `16`-bit number. -/
example {p : ℕ} (hp : some p ∈ (ProbComp.eval (randomPrime 16)).support) :
    2 ^ 15 ≤ p ∧ p < 2 ^ 16 :=
  mem_support_randomPrime (by norm_num) hp

/-- The smallest and the largest `16`-bit primes are returned with the same probability. -/
example :
    ProbComp.eval (randomPrime 16) (some 32771) = ProbComp.eval (randomPrime 16) (some 65521) :=
  eval_randomPrime_some_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ### Density and failure bounds -/

/-- At least a `1 / 48` fraction of the `16`-bit numbers are prime. -/
example : 2 ^ (16 - 1) ≤ 3 * 16 * ((Finset.Ico (2 ^ (16 - 1)) (2 ^ 16)).filter Nat.Prime).card :=
  Nat.two_pow_sub_one_le_three_mul_card_primes (by norm_num)

/-- At `n = 16` the random prime generator fails with probability at most `2⁻¹⁶`. -/
example : ProbComp.eval (randomPrime 16) none ≤ (2 ^ 16)⁻¹ :=
  eval_randomPrime_none_le_inv_two_pow (by norm_num)

/-- At `n = 16` the modulus generator fails with probability at most `1538 · 2⁻¹⁶`. -/
example : (ProbComp.eval (genModulus 16)).toOuterMeasure {out | ¬ ∃ p q,
      out = some (p * q, p, q) ∧ p.Prime ∧ q.Prime ∧ 2 ^ (16 - 1) ≤ p ∧ p < 2 ^ 16 ∧
        2 ^ (16 - 1) ≤ q ∧ q < 2 ^ 16} ≤ 1538 * (2 ^ 16)⁻¹ := by
  refine (toOuterMeasure_genModulus_invalid_le_inv_two_pow (by norm_num)).trans_eq ?_
  norm_num

/-! ### Efficiency -/

example : Probability.IsPPTOn (encPair encNat encUnary) encBool
    fun x : ℕ × ℕ => millerRabinTest x.1 x.2 :=
  isPPTOn_millerRabinTest

example : Probability.IsPPTOn encUnary (encOption encNat) randomPrime :=
  isPPTOn_randomPrime

example : Probability.IsPPTOn encUnary (encOption (encPair encNat (encPair encNat encNat)))
    genModulus :=
  isPPTOn_genModulus

end CslibFrontierTests.Crypto.MillerRabin
