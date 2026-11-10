/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MillerRabin
public import CslibFrontier.Languages.Probabilistic.Retry
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Foundations.Analysis.ENNRealOneSubInvPow
import CslibFrontier.Foundations.NumberTheory.PrimeDensity
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Event

/-!
# Random prime and modulus generation

This file implements the random prime generator of [KatzLindell2020], Algorithm 9.34, on top of
the Miller–Rabin test of `CslibFrontier/Crypto/Computational/MillerRabin.lean`. On input `n`, given
in unary, it draws up to `3 n²` uniform `n`-bit candidates, runs the Miller–Rabin test with `n`
rounds on each, and returns the first candidate that passes, or `none` when every candidate fails.

The guarantees of [KatzLindell2020], Section 9.2.1, proved here are:

* the generator returns a number that is not prime with probability at most `3 n² 2⁻ⁿ`: by a
  union bound over the attempts, each of which passes a composite with probability at most `2⁻ⁿ`;
* it returns `none` with probability at most `ρ ^ (3 n²)`, where `ρ` is the probability that a
  uniform `n`-bit candidate is not prime, since a prime candidate always passes;
* for `n > 1`, `ρ ≤ 1 - 1 / (3 n)` by the density of the `n`-bit primes ([KatzLindell2020],
  Theorem 9.32, in `CslibFrontier/Foundations/NumberTheory/PrimeDensity.lean`), so the
  generator returns `none` with probability at most `2⁻ⁿ`;
* every output is an `n`-bit number, and all `n`-bit primes are returned with the same
  probability, so conditioned on returning a prime the output is a uniform `n`-bit prime;
* the generator is a strict PPT program in `n`.

Two independent runs of the generator, multiplied, give the modulus generator `GenModulus` that
[KatzLindell2020], Section 9.2.3, suggests: it returns `(p q, p, q)` for `n`-bit primes `p` and
`q` except with probability at most `2 ρ ^ (3 n²) + 6 n² 2⁻ⁿ`, hence at most `(6 n² + 2) 2⁻ⁿ` for
`n > 1`, and it is a strict PPT program in `n`.

## Main definitions

* `Cslib.Crypto.primeCandidate`: a uniform `n`-bit number.
* `Cslib.Crypto.primeAttempt`: a candidate together with the verdict of the test on it.
* `Cslib.Crypto.randomPrime`: the generator of Algorithm 9.34.
* `Cslib.Crypto.genModulus`: the modulus generator of Section 9.2.3.

## Main results

* `Cslib.Crypto.eval_primeCandidate_apply`: candidates are uniform over the `n`-bit numbers.
* `Cslib.Crypto.toOuterMeasure_randomPrime_not_prime_le`: the generator returns a number that is
  not prime with probability at most `3 n² 2⁻ⁿ`.
* `Cslib.Crypto.eval_randomPrime_none_le`: the generator fails with probability at most
  `ρ ^ (3 n²)`.
* `Cslib.Crypto.inv_three_mul_le_toOuterMeasure_primeCandidate_prime`: for `n > 1`, a candidate is
  prime with probability at least `1 / (3 n)`.
* `Cslib.Crypto.eval_randomPrime_none_le_inv_two_pow`: for `n > 1`, the generator fails with
  probability at most `2⁻ⁿ`.
* `Cslib.Crypto.mem_support_randomPrime`: every output is an `n`-bit number.
* `Cslib.Crypto.eval_randomPrime_some_eq`: all `n`-bit primes are equally likely outputs.
* `Cslib.Crypto.isPPTOn_randomPrime`: the generator is a strict PPT program in `n`.
* `Cslib.Crypto.toOuterMeasure_genModulus_invalid_le`: the modulus generator returns `(p q, p, q)`
  for `n`-bit primes `p` and `q` except with probability at most `2 ρ ^ (3 n²) + 6 n² 2⁻ⁿ`.
* `Cslib.Crypto.toOuterMeasure_genModulus_invalid_le_inv_two_pow`: for `n > 1`, this probability
  is at most `(6 n² + 2) 2⁻ⁿ`.
* `Cslib.Crypto.isPPTOn_genModulus`: the modulus generator is a strict PPT program in `n`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 9.2.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM
open scoped ENNReal

/-- A **uniform `n`-bit candidate**: `n - 1` fair coins below a leading one, read least
significant bit first. For `n = 0` the candidate is `1`. -/
@[expose] noncomputable def primeCandidate (n : ℕ) : ProbComp ℕ := do
  let low ← BitString.sampleList (n - 1)
  return ofBits (low ++ [true])

/-- One **attempt** of the generator: a uniform `n`-bit candidate `p` and the verdict of the
Miller–Rabin test with `n` rounds on `p`. -/
@[expose] noncomputable def primeAttempt (n : ℕ) : ProbComp (ℕ × Bool) := do
  let p ← primeCandidate n
  let verdict ← millerRabinTest p n
  return (p, verdict)

/-- The **random prime generator** of [KatzLindell2020], Algorithm 9.34: up to `3 n²` attempts,
returning the first candidate that passes the test, or `none` when every attempt fails. -/
@[expose] noncomputable def randomPrime (n : ℕ) : ProbComp (Option ℕ) := do
  let found ← OracleComp.retry (fun attempt : ℕ × Bool => attempt.2 = true) (primeAttempt n)
    (3 * n ^ 2)
  return found.map Prod.fst

/-- The **modulus generator** suggested in [KatzLindell2020], Section 9.2.3: two independent runs
of the random prime generator, multiplied. It returns `(N, p, q)` with `N = p q`, or `none` when
either run fails. -/
@[expose] noncomputable def genModulus (n : ℕ) : ProbComp (Option (ℕ × ℕ × ℕ)) := do
  let first ← randomPrime n
  let second ← randomPrime n
  return first.bind fun p => second.map fun q => (p * q, p, q)

/-! ### Candidates -/

/-- Reading `low ++ [true]` least significant bit first puts a one above `low`. -/
private theorem ofBits_append_true (low : List Bool) :
    ofBits (low ++ [true]) = 2 ^ low.length + ofBits low := by
  rw [ofBits_eq_lsbValue, ofBits_eq_lsbValue, BitString.lsbValue_append,
    BitString.lsbValue_singleton, Bool.toNat_true, mul_one, add_comm]

/-- `2 ^ n` is twice `2 ^ (n - 1)` for positive `n`. -/
private theorem two_pow_eq_two_mul {n : ℕ} (hn : 0 < n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- The law of a candidate. -/
theorem eval_primeCandidate (n : ℕ) :
    ProbComp.eval (primeCandidate n) =
      (BitString.uniformList (n - 1)).map fun low => ofBits (low ++ [true]) := by
  simp only [primeCandidate, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  rfl

/-- **Every candidate is an `n`-bit number.** -/
theorem mem_support_primeCandidate {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ (ProbComp.eval (primeCandidate n)).support) : 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n := by
  rw [eval_primeCandidate, PMF.support_map] at hp
  obtain ⟨low, hlow, rfl⟩ := hp
  rw [BitString.mem_support_uniformList_iff] at hlow
  have hlt : ofBits low < 2 ^ (n - 1) := by
    rw [ofBits_eq_lsbValue, ← hlow]
    exact BitString.lsbValue_lt low
  have hpow := two_pow_eq_two_mul hn
  simp only [ofBits_append_true, hlow]
  omega

/-- **Candidates are uniform** over the `n`-bit numbers. -/
theorem eval_primeCandidate_apply {n p : ℕ} (hn : 0 < n) (hlow : 2 ^ (n - 1) ≤ p)
    (hhigh : p < 2 ^ n) : ProbComp.eval (primeCandidate n) p = (2 ^ (n - 1))⁻¹ := by
  have hlt : p - 2 ^ (n - 1) < 2 ^ (n - 1) := by
    have hpow := two_pow_eq_two_mul hn
    omega
  have hcard : (Finset.univ.filter fun r : Fin (n - 1) → Bool =>
      ofBits (List.ofFn r ++ [true]) = p).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨(BitString.equivFin (n - 1)).symm ⟨p - 2 ^ (n - 1), hlt⟩, ?_⟩
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      ofBits_append_true, List.length_ofFn, ofBits_ofFn, Equiv.eq_symm_apply, Fin.ext_iff]
    omega
  rw [eval_primeCandidate, BitString.uniformList_map_apply, hcard, Nat.cast_one, one_div]

/-! ### Attempts -/

/-- The law of an attempt: a candidate `p`, then the verdict of the test on `p`. -/
theorem eval_primeAttempt (n : ℕ) :
    ProbComp.eval (primeAttempt n) =
      (ProbComp.eval (primeCandidate n)).bind fun p =>
        (ProbComp.eval (millerRabinTest p n)).map fun verdict => (p, verdict) := by
  simp only [primeAttempt, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- An attempt returns `(p, b)` with the probability of the candidate `p` times the probability
of the verdict `b` on `p`. -/
private theorem eval_primeAttempt_apply (n p : ℕ) (b : Bool) :
    ProbComp.eval (primeAttempt n) (p, b) =
      ProbComp.eval (primeCandidate n) p * ProbComp.eval (millerRabinTest p n) b := by
  rw [eval_primeAttempt, PMF.bind_apply, tsum_eq_single p]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro c hc
      simp [Ne.symm hc]
  · intro q hq
    simp [PMF.map_apply, Ne.symm hq]

/-- An attempt passes the test on a number that is not prime with probability at most `2⁻ⁿ`. -/
private theorem toOuterMeasure_primeAttempt_not_prime_le (n : ℕ) :
    (ProbComp.eval (primeAttempt n)).toOuterMeasure {a | a.2 = true ∧ ¬ a.1.Prime} ≤
      (2 ^ n)⁻¹ := by
  rw [eval_primeAttempt]
  refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun p => ?_
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hp : p.Prime
  · have hset : (fun verdict => (p, verdict)) ⁻¹' {a : ℕ × Bool | a.2 = true ∧ ¬ a.1.Prime} =
        ∅ := by
      ext verdict
      simp [hp]
    rw [hset]
    simp
  · have hset : (fun verdict => (p, verdict)) ⁻¹' {a : ℕ × Bool | a.2 = true ∧ ¬ a.1.Prime} =
        {true} := by
      ext verdict
      simp [hp]
    rw [hset, PMF.toOuterMeasure_apply_singleton]
    exact eval_millerRabinTest_le_of_not_prime hp n

/-- An attempt on a prime candidate passes, so an attempt fails with at most the probability
that the candidate is not prime. -/
private theorem toOuterMeasure_primeAttempt_fail_le (n : ℕ) :
    (ProbComp.eval (primeAttempt n)).toOuterMeasure {a | ¬ a.2 = true} ≤
      (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} := by
  rw [eval_primeAttempt]
  refine (Probability.PMF.toOuterMeasure_bind_le_add _ _ {p | ¬ p.Prime} _ 0
    fun p _ hp => ?_).trans (add_zero _).le
  simp only [Set.mem_ofPred_eq, not_not] at hp
  rw [PMF.toOuterMeasure_map_apply, nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff,
    (PMF.apply_eq_one_iff _ _).1 (eval_millerRabinTest_of_prime hp n)]
  simp

/-! ### The generator -/

/-- The law of the generator: the first entries of the retry loop over attempts. -/
private theorem eval_randomPrime (n : ℕ) :
    ProbComp.eval (randomPrime n) =
      (ProbComp.eval (OracleComp.retry (fun attempt : ℕ × Bool => attempt.2 = true)
        (primeAttempt n) (3 * n ^ 2))).map fun found => found.map Prod.fst := by
  simp only [randomPrime, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- The retry loop over attempts returns a passing attempt `a` with the probability that one
attempt returns `a`, times the expected number of attempts. -/
private theorem eval_retry_primeAttempt_some (n : ℕ) (a : ℕ × Bool) :
    ProbComp.eval (OracleComp.retry (fun attempt : ℕ × Bool => attempt.2 = true)
        (primeAttempt n) (3 * n ^ 2)) (some a) =
      (if a.2 = true then ProbComp.eval (primeAttempt n) a else 0) *
        ∑ i ∈ Finset.range (3 * n ^ 2),
          (ProbComp.eval (primeAttempt n)).toOuterMeasure {a | ¬ a.2 = true} ^ i :=
  OracleComp.evalWith_retry_some _ _ _ _ _

/-- **The generator returns a number that is not prime with probability at most `3 n² 2⁻ⁿ`**
([KatzLindell2020], Section 9.2.1): by a union bound, each of the `3 n²` attempts passes the
test on a number that is not prime with probability at most `2⁻ⁿ`. -/
theorem toOuterMeasure_randomPrime_not_prime_le (n : ℕ) :
    (ProbComp.eval (randomPrime n)).toOuterMeasure {found | ∃ p, found = some p ∧ ¬ p.Prime} ≤
      3 * n ^ 2 * (2 ^ n)⁻¹ := by
  have hpre : (fun found : Option (ℕ × Bool) => found.map Prod.fst) ⁻¹'
      {found | ∃ p, found = some p ∧ ¬ p.Prime} = some '' {a : ℕ × Bool | ¬ a.1.Prime} := by
    ext found
    rcases found with _ | ⟨q, _ | _⟩ <;> simp
  have h : (ProbComp.eval (OracleComp.retry (fun attempt : ℕ × Bool => attempt.2 = true)
      (primeAttempt n) (3 * n ^ 2))).toOuterMeasure (some '' {a : ℕ × Bool | ¬ a.1.Prime}) ≤
      (3 * n ^ 2 : ℕ) * (2 ^ n)⁻¹ :=
    OracleComp.toOuterMeasure_evalWith_retry_le _ _ _ _
      (toOuterMeasure_primeAttempt_not_prime_le n) _
  rw [eval_randomPrime, PMF.toOuterMeasure_map_apply, hpre]
  simpa using h

/-- **The generator fails with probability at most `ρ ^ (3 n²)`**, where `ρ` is the probability
that a uniform `n`-bit candidate is not prime: an attempt on a prime candidate always passes. -/
theorem eval_randomPrime_none_le (n : ℕ) :
    ProbComp.eval (randomPrime n) none ≤
      (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} ^ (3 * n ^ 2) := by
  have hpre : (fun found : Option (ℕ × Bool) => found.map Prod.fst) ⁻¹' {none} = {none} := by
    ext found
    cases found <;> simp
  rw [← PMF.toOuterMeasure_apply_singleton, eval_randomPrime, PMF.toOuterMeasure_map_apply, hpre,
    PMF.toOuterMeasure_apply_singleton]
  exact OracleComp.evalWith_retry_none_le _ _ _ (toOuterMeasure_primeAttempt_fail_le n) _

/-- The probability that a uniform `n`-bit candidate satisfies `P` is the number of `n`-bit
numbers satisfying `P` divided by `2 ^ (n - 1)`. -/
private theorem toOuterMeasure_primeCandidate {n : ℕ} (hn : 0 < n) (P : ℕ → Prop)
    [DecidablePred P] :
    (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | P p} =
      ((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter P).card * (2 ^ (n - 1))⁻¹ := by
  have hset : {p | P p} ∩ (ProbComp.eval (primeCandidate n)).support =
      ↑((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter P) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Ico]
    refine ⟨fun h => ⟨mem_support_primeCandidate hn h.2, h.1⟩, fun h => ⟨h.2, ?_⟩⟩
    rw [PMF.mem_support_iff, eval_primeCandidate_apply hn h.1.1 h.1.2]
    simp
  rw [← PMF.toOuterMeasure_apply_inter_support, hset, PMF.toOuterMeasure_apply_finset,
    ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_Ico] at hp
  exact eval_primeCandidate_apply hn hp.1.1 hp.1.2

/-- **A uniform `n`-bit candidate is prime with probability at least `1 / (3 n)`** for `1 < n`,
by the density of the `n`-bit primes ([KatzLindell2020], Theorem 9.32). -/
theorem inv_three_mul_le_toOuterMeasure_primeCandidate_prime {n : ℕ} (hn : 1 < n) :
    (3 * n : ℝ≥0∞)⁻¹ ≤ (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | p.Prime} := by
  have hle : ((2 ^ (n - 1) : ℕ) : ℝ≥0∞) ≤
      (((Finset.Ico (2 ^ (n - 1)) (2 ^ n)).filter Nat.Prime).card * (3 * n) : ℕ) := by
    exact_mod_cast (Nat.two_pow_sub_one_le_three_mul_card_primes hn).trans_eq (mul_comm _ _)
  push_cast at hle
  rw [toOuterMeasure_primeCandidate (by omega), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm ((3 : ℝ≥0∞) * n)⁻¹,
    ← div_eq_mul_inv,
    ENNReal.div_le_iff_le_mul (by simp) (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))]
  exact hle

/-- A uniform `n`-bit candidate is not prime with probability at most `1 - 1 / (3 n)` for
`1 < n`. -/
theorem toOuterMeasure_primeCandidate_not_prime_le {n : ℕ} (hn : 1 < n) :
    (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} ≤ 1 - (3 * n : ℝ≥0∞)⁻¹ :=
  Probability.PMF.toOuterMeasure_compl_le_one_sub _ {p : ℕ | p.Prime}
    (inv_three_mul_le_toOuterMeasure_primeCandidate_prime hn)

/-- `ρ ^ (3 n²) ≤ 2⁻ⁿ` for `1 < n`, where `ρ` is the probability that a uniform `n`-bit
candidate is not prime. -/
private theorem toOuterMeasure_primeCandidate_not_prime_pow_le {n : ℕ} (hn : 1 < n) :
    (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} ^ (3 * n ^ 2) ≤
      (2 ^ n)⁻¹ := by
  have hk := ENNReal.one_sub_inv_pow_le_inv_two (k := 3 * n) (by omega)
  push_cast at hk
  calc _ ≤ (1 - (3 * n : ℝ≥0∞)⁻¹) ^ (3 * n ^ 2) := by
        gcongr
        exact toOuterMeasure_primeCandidate_not_prime_le hn
    _ = ((1 - (3 * n : ℝ≥0∞)⁻¹) ^ (3 * n)) ^ n := by
        rw [← pow_mul, show 3 * n * n = 3 * n ^ 2 by ring]
    _ ≤ 2⁻¹ ^ n := by gcongr
    _ = (2 ^ n)⁻¹ := ENNReal.inv_pow.symm

/-- **For `1 < n`, the generator fails with probability at most `2⁻ⁿ`.** A candidate is prime
with probability at least `1 / (3 n)`, so all `3 n²` attempts fail with probability at most
`(1 - 1 / (3 n)) ^ (3 n²) ≤ 2⁻ⁿ`. -/
theorem eval_randomPrime_none_le_inv_two_pow {n : ℕ} (hn : 1 < n) :
    ProbComp.eval (randomPrime n) none ≤ (2 ^ n)⁻¹ :=
  (eval_randomPrime_none_le n).trans (toOuterMeasure_primeCandidate_not_prime_pow_le hn)

/-- **Every output of the generator is an `n`-bit number.** -/
theorem mem_support_randomPrime {n p : ℕ}
    (hp : some p ∈ (ProbComp.eval (randomPrime n)).support) : 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [randomPrime] at hp
  rw [eval_randomPrime, PMF.support_map] at hp
  obtain ⟨found, hfound, hmap⟩ := hp
  rcases found with _ | ⟨q, b⟩
  · simp at hmap
  have hqp : q = p := by simpa using hmap
  rw [← hqp]
  rw [PMF.mem_support_iff, eval_retry_primeAttempt_some] at hfound
  have hattempt : ProbComp.eval (primeAttempt n) (q, b) ≠ 0 := by
    split_ifs at hfound
    · exact left_ne_zero_of_mul hfound
    · simp at hfound
  rw [eval_primeAttempt_apply] at hattempt
  exact mem_support_primeCandidate hn ((PMF.mem_support_iff _ _).2 (left_ne_zero_of_mul hattempt))

/-- **The probability of returning an `n`-bit prime `p`** is the probability `2⁻⁽ⁿ⁻¹⁾` of drawing
`p` as a candidate, times the expected number of attempts. It does not depend on `p`. -/
theorem eval_randomPrime_some {n p : ℕ} (hlow : 2 ^ (n - 1) ≤ p) (hhigh : p < 2 ^ n)
    (hp : p.Prime) :
    ProbComp.eval (randomPrime n) (some p) =
      (2 ^ (n - 1))⁻¹ * ∑ i ∈ Finset.range (3 * n ^ 2),
        (ProbComp.eval (primeAttempt n)).toOuterMeasure {a | ¬ a.2 = true} ^ i := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by
    subst h
    simp only [zero_tsub, pow_zero] at hlow hhigh
    omega
  have hpre : (fun found : Option (ℕ × Bool) => found.map Prod.fst) ⁻¹' {some p} =
      ↑({some (p, true), some (p, false)} : Finset (Option (ℕ × Bool))) := by
    ext found
    rcases found with _ | ⟨q, _ | _⟩ <;> simp
  have hne : (some (p, true) : Option (ℕ × Bool)) ≠ some (p, false) := by simp
  rw [← PMF.toOuterMeasure_apply_singleton, eval_randomPrime, PMF.toOuterMeasure_map_apply, hpre,
    PMF.toOuterMeasure_apply_finset, Finset.sum_pair hne, eval_retry_primeAttempt_some,
    eval_retry_primeAttempt_some, eval_primeAttempt_apply, eval_primeCandidate_apply hn hlow hhigh,
    eval_millerRabinTest_of_prime hp]
  simp

/-- **Conditioned on returning a prime, the output is a uniform `n`-bit prime**
([KatzLindell2020], Section 9.2.1): any two `n`-bit primes are returned with the same
probability. -/
theorem eval_randomPrime_some_eq {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp_low : 2 ^ (n - 1) ≤ p) (hp_high : p < 2 ^ n) (hq_low : 2 ^ (n - 1) ≤ q)
    (hq_high : q < 2 ^ n) :
    ProbComp.eval (randomPrime n) (some p) = ProbComp.eval (randomPrime n) (some q) := by
  rw [eval_randomPrime_some hp_low hp_high hp, eval_randomPrime_some hq_low hq_high hq]

/-! ### Moduli -/

/-- A run of the generator returns a prime except with at most the failure probability plus the
probability of returning a number that is not prime. -/
private theorem toOuterMeasure_randomPrime_not_found_le (n : ℕ) :
    (ProbComp.eval (randomPrime n)).toOuterMeasure {found | ¬ ∃ p, found = some p ∧ p.Prime} ≤
      (ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} ^ (3 * n ^ 2) +
        3 * n ^ 2 * (2 ^ n)⁻¹ := by
  calc _ ≤ (ProbComp.eval (randomPrime n)).toOuterMeasure
        ({none} ∪ {found | ∃ p, found = some p ∧ ¬ p.Prime}) := by
        refine MeasureTheory.measure_mono fun found hfound => ?_
        rcases found with _ | p
        · exact Or.inl rfl
        · exact Or.inr ⟨p, rfl, fun hp => hfound ⟨p, rfl, hp⟩⟩
    _ ≤ _ := MeasureTheory.measure_union_le _ _
    _ ≤ _ := by
        rw [PMF.toOuterMeasure_apply_singleton]
        exact add_le_add (eval_randomPrime_none_le n) (toOuterMeasure_randomPrime_not_prime_le n)

/-- The law of the modulus generator. -/
private theorem eval_genModulus (n : ℕ) :
    ProbComp.eval (genModulus n) = (ProbComp.eval (randomPrime n)).bind fun first =>
      (ProbComp.eval (randomPrime n)).bind fun second =>
        PMF.pure (first.bind fun p => second.map fun q => (p * q, p, q)) := by
  simp only [genModulus, ProbComp.eval_bind, ProbComp.eval_pure]

/-- **The modulus generator returns `(p q, p, q)` for `n`-bit primes `p` and `q`**
([KatzLindell2020], Section 9.2.3) except with probability at most `2 ρ ^ (3 n²) + 6 n² 2⁻ⁿ`,
where `ρ` is the probability that a uniform `n`-bit candidate is not prime: by a union bound over
its two runs. -/
theorem toOuterMeasure_genModulus_invalid_le (n : ℕ) :
    (ProbComp.eval (genModulus n)).toOuterMeasure {out | ¬ ∃ p q, out = some (p * q, p, q) ∧
        p.Prime ∧ q.Prime ∧ 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n ∧ 2 ^ (n - 1) ≤ q ∧ q < 2 ^ n} ≤
      2 * ((ProbComp.eval (primeCandidate n)).toOuterMeasure {p | ¬ p.Prime} ^ (3 * n ^ 2) +
        3 * n ^ 2 * (2 ^ n)⁻¹) := by
  have hfound := toOuterMeasure_randomPrime_not_found_le n
  rw [eval_genModulus, two_mul]
  refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
    {found | ¬ ∃ p, found = some p ∧ p.Prime} _ _ fun first hfirst hfirst' => ?_).trans
    (add_le_add hfound le_rfl)
  obtain ⟨p, rfl, hp⟩ := not_not.1 hfirst'
  have hp_bits := mem_support_randomPrime hfirst
  refine (Probability.PMF.toOuterMeasure_bind_le_add _ _
    {found | ¬ ∃ p, found = some p ∧ p.Prime} _ 0 fun second hsecond hsecond' => ?_).trans
    ((add_zero _).trans_le hfound)
  obtain ⟨q, rfl, hq⟩ := not_not.1 hsecond'
  have hq_bits := mem_support_randomPrime hsecond
  rw [nonpos_iff_eq_zero, PMF.toOuterMeasure_apply_eq_zero_iff, PMF.support_pure,
    Set.disjoint_singleton_left]
  exact fun h => h ⟨p, q, rfl, hp, hq, hp_bits.1, hp_bits.2, hq_bits.1, hq_bits.2⟩

/-- **For `1 < n`, the modulus generator returns `(p q, p, q)` for `n`-bit primes `p` and `q`
except with probability at most `(6 n² + 2) 2⁻ⁿ`**, which is negligible in `n`. -/
theorem toOuterMeasure_genModulus_invalid_le_inv_two_pow {n : ℕ} (hn : 1 < n) :
    (ProbComp.eval (genModulus n)).toOuterMeasure {out | ¬ ∃ p q, out = some (p * q, p, q) ∧
        p.Prime ∧ q.Prime ∧ 2 ^ (n - 1) ≤ p ∧ p < 2 ^ n ∧ 2 ^ (n - 1) ≤ q ∧ q < 2 ^ n} ≤
      (6 * n ^ 2 + 2) * (2 ^ n)⁻¹ := by
  have h := toOuterMeasure_primeCandidate_not_prime_pow_le hn
  refine (toOuterMeasure_genModulus_invalid_le n).trans ?_
  calc _ ≤ (2 : ℝ≥0∞) * ((2 ^ n)⁻¹ + 3 * (n : ℝ≥0∞) ^ 2 * (2 ^ n)⁻¹) := by gcongr
    _ = (6 * (n : ℝ≥0∞) ^ 2 + 2) * (2 ^ n)⁻¹ := by ring

/-! ### Efficiency -/

/-- Candidates are a strict PPT program in `n`, given in unary. -/
theorem isPPTOn_primeCandidate : Probability.IsPPTOn encUnary encNat primeCandidate := by
  have hvalue : ComputableInPolyTime (fun x : ℕ × List Bool => ofBits (x.2 ++ [true]))
      (encPair encUnary encBits) encNat :=
    ComputableInPolyTime.bitsToNat.comp (by fun_prop)
  refine (Probability.IsPPTOn.of_seeded (count := fun n : ℕ => n - 1) (by fun_prop)
    hvalue).congr fun n => ?_
  simp only [primeCandidate, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- An attempt is a strict PPT program in `n`, given in unary. -/
theorem isPPTOn_primeAttempt :
    Probability.IsPPTOn encUnary (encPair encNat encBool) primeAttempt := by
  have htest : Probability.IsPPTOn (encPair encUnary encNat) encBool
      fun x : ℕ × ℕ => millerRabinTest x.2 x.1 :=
    isPPTOn_millerRabinTest.preprocess (prepare := fun x : ℕ × ℕ => (x.2, x.1)) (by fun_prop)
  have hstep : Probability.IsPPTOn (encPair encUnary encNat) (encPair encNat encBool)
      fun x : ℕ × ℕ => (fun verdict => (x.2, verdict)) <$> millerRabinTest x.2 x.1 :=
    htest.map_with (f := fun x verdict => (x.2, verdict)) (by fun_prop)
  refine (isPPTOn_primeCandidate.bind_with
    (second := fun n p => (fun verdict => (p, verdict)) <$> millerRabinTest p n) hstep).congr
    fun n => ?_
  simp only [primeAttempt, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- **The generator is a strict PPT program** in `n`, given in unary. -/
theorem isPPTOn_randomPrime : Probability.IsPPTOn encUnary (encOption encNat) randomPrime := by
  have hfst : ComputableInPolyTime (fun found : Option (ℕ × Bool) => found.map Prod.fst)
      (encOption (encPair encNat encBool)) (encOption encNat) := by
    have heq : (fun found : Option (ℕ × Bool) => found.map Prod.fst) =
        fun found => found.elim none fun a => some a.1 := by
      funext found
      cases found <;> rfl
    rw [heq]
    fun_prop
  refine ((isPPTOn_primeAttempt.retry (good := fun a => a.2) (fuel := fun n => 3 * n ^ 2)
    (by fun_prop) (by fun_prop)).map hfst).congr fun n => ?_
  simp only [randomPrime, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- Combining two optional primes into an optional modulus takes polynomial time. -/
private theorem computableInPolyTime_combine :
    ComputableInPolyTime
      (fun x : Option ℕ × Option ℕ => x.1.bind fun p => x.2.map fun q => (p * q, p, q))
      (encPair (encOption encNat) (encOption encNat))
      (encOption (encPair encNat (encPair encNat encNat))) := by
  have htriple : ComputableInPolyTime (fun pq : ℕ × ℕ => some (pq.1 * pq.2, pq.1, pq.2))
      (encPair encNat encNat) (encOption (encPair encNat (encPair encNat encNat))) :=
    (ComputableInPolyTime.optionSome _).comp
      ((ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
        (ComputableInPolyTime.snd encNat encNat)).prod
        ((ComputableInPolyTime.fst encNat encNat).prod (ComputableInPolyTime.snd encNat encNat)))
  have hinner : ComputableInPolyTime
      (fun r : (Option ℕ × Option ℕ) × ℕ => r.1.2.elim none fun q => some (r.2 * q, r.2, q))
      (encPair (encPair (encOption encNat) (encOption encNat)) encNat)
      (encOption (encPair encNat (encPair encNat encNat))) := by
    refine ComputableInPolyTime.optionElimWithInput (encB := encNat) ?_
      (ComputableInPolyTime.const _) ?_
    · exact ComputableInPolyTime.snd' (ComputableInPolyTime.fst _ _)
    · exact htriple.comp ((ComputableInPolyTime.snd' (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hcombine : ComputableInPolyTime
      (fun x : Option ℕ × Option ℕ =>
        x.1.elim none fun p => x.2.elim none fun q => some (p * q, p, q))
      (encPair (encOption encNat) (encOption encNat))
      (encOption (encPair encNat (encPair encNat encNat))) := by
    refine ComputableInPolyTime.optionElimWithInput (encB := encNat) ?_
      (ComputableInPolyTime.const _) hinner
    exact ComputableInPolyTime.fst _ _
  have heq : (fun x : Option ℕ × Option ℕ => x.1.bind fun p => x.2.map fun q => (p * q, p, q)) =
      fun x => x.1.elim none fun p => x.2.elim none fun q => some (p * q, p, q) := by
    funext x
    rcases x with ⟨_ | _, _ | _⟩ <;> rfl
  rw [heq]
  exact hcombine

/-- **The modulus generator is a strict PPT program** in `n`, given in unary. -/
theorem isPPTOn_genModulus :
    Probability.IsPPTOn encUnary (encOption (encPair encNat (encPair encNat encNat)))
      genModulus := by
  have hcombine : ComputableInPolyTime
      (fun x : (ℕ × Option ℕ) × Option ℕ => x.1.2.bind fun p => x.2.map fun q => (p * q, p, q))
      (encPair (encPair encUnary (encOption encNat)) (encOption encNat))
      (encOption (encPair encNat (encPair encNat encNat))) :=
    computableInPolyTime_combine.comp
      ((ComputableInPolyTime.snd' (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hsecond : Probability.IsPPTOn (encPair encUnary (encOption encNat))
      (encOption (encPair encNat (encPair encNat encNat))) fun x : ℕ × Option ℕ =>
        (fun second => x.2.bind fun p => second.map fun q => (p * q, p, q)) <$> randomPrime x.1 :=
    (isPPTOn_randomPrime.preprocess (prepare := fun x : ℕ × Option ℕ => x.1)
      (by fun_prop)).map_with
      (f := fun x second => x.2.bind fun p => second.map fun q => (p * q, p, q)) hcombine
  refine (isPPTOn_randomPrime.bind_with (second := fun n first =>
    (fun second => first.bind fun p => second.map fun q => (p * q, p, q)) <$> randomPrime n)
    hsecond).congr fun n => ?_
  simp only [genModulus, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

end Cslib.Crypto
