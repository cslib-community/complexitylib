/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Primes.MillerRabin
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Probability.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import Mathlib.Data.Nat.Size

/-!
# The Miller–Rabin primality test as a probabilistic program

This file packages the Miller–Rabin test ([KatzLindell2020], Section 9.2.2) as a probabilistic
program with an explicit coin budget, and proves the guarantee of [KatzLindell2020], Theorem 9.33:
a prime always passes, and a composite passes `t` independent rounds with probability at most
`2⁻ᵗ`. The test is a strict PPT program in the binary length of the candidate and the number of
rounds, given in unary.

The number theory is already in the library and is reused here, not reproved:

* modulo an odd composite `n` the strong liars lie in a proper subgroup of the units
  (`ZMod.exists_subgroup_ne_top_isStrongLiar`), so at most half of the units are strong liars
  (`ZMod.two_mul_card_isStrongLiar_le`). This also covers odd prime powers, so the test needs no
  perfect-power check, unlike Algorithm 9.44 of [KatzLindell2020];
* the coRP verifier `Complexity.MillerRabin.verifier` reads `2 |n|` random bits `r`, takes the
  base `1 + (r mod (n - 1))` and declares an odd `n > 2` composite when that base is a witness.
  `Complexity.MillerRabin.decidesWithOneSidedError` bounds its error; the bias of the reduction
  modulo `n - 1` is absorbed there.

A round (`millerRabinRound`) flips the `2 |n|` coins and negates the verifier, so it answers
`true` for "prime". The test (`millerRabinTest`) runs `t` independent rounds and answers "prime"
when all of them do.

## Main definitions

* `Cslib.Crypto.millerRabinRound`: one round on `n`, answering `true` for "prime".
* `Cslib.Crypto.millerRabinTest`: `t` independent rounds on `n`.

## Main results

* `Cslib.Crypto.eval_millerRabinTest_true`: `t` rounds all pass with the `t`-th power of the
  probability that one round passes.
* `Cslib.Crypto.eval_millerRabinTest_of_prime`: a prime always passes.
* `Cslib.Crypto.eval_millerRabinTest_le_of_not_prime`: a number that is not prime passes `t`
  rounds with probability at most `2⁻ᵗ`.
* `Cslib.Crypto.isPPTOn_millerRabinTest`: the test is a strict PPT program in `|n|` and `t`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 9.2.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM
open scoped ENNReal

/-- One **Miller–Rabin round** on `n`, answering `true` for "prime". It flips `2 |n|` fair coins
and negates the coRP verifier `Complexity.MillerRabin.verifier`: `2` passes, `0`, `1` and the even
numbers above `2` fail, and an odd `n > 2` passes exactly when the base `1 + (r mod (n - 1))`, for
the coin word `r`, is a strong liar for `n`. -/
@[expose] noncomputable def millerRabinRound (n : ℕ) : ProbComp Bool := do
  let coins ← BitString.sampleList (2 * n.size)
  return !Complexity.MillerRabin.verifier (n, coins)

/-- The **Miller–Rabin test** with `t` rounds: run `t` independent rounds on `n` and answer
"prime" (`true`) when every round does. This is Algorithm 9.44 of [KatzLindell2020] without the
perfect-power check, which the strong-liar bound makes unnecessary, and with the base drawn as in
`Complexity.MillerRabin.verifier`. -/
@[expose] noncomputable def millerRabinTest (n t : ℕ) : ProbComp Bool := do
  let verdicts ← OracleComp.replicate t (millerRabinRound n)
  return verdicts.all id

/-! ### One round -/

/-- The law of a round: the image of `2 |n|` uniform coins under the negated verifier. -/
theorem eval_millerRabinRound (n : ℕ) :
    ProbComp.eval (millerRabinRound n) =
      (BitString.uniformList (2 * n.size)).map fun coins =>
        !Complexity.MillerRabin.verifier (n, coins) := by
  simp only [millerRabinRound, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  rfl

/-- A round answers `b` with the fraction of coin words on which the verifier answers `!b`. -/
private theorem eval_millerRabinRound_apply (n : ℕ) (b : Bool) :
    ProbComp.eval (millerRabinRound n) b =
      ((Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
          Complexity.MillerRabin.verifier (n, List.ofFn r) = !b).card : ℝ≥0∞) /
        2 ^ (2 * n.size) := by
  rw [eval_millerRabinRound, BitString.uniformList_map_apply]
  simp only [Bool.not_eq_eq_eq_not]

/-- The verifier reads `2 |n|` random bits on the input `n`. -/
private theorem eval_two_mul_X_length (n : ℕ) :
    (2 * Polynomial.X : Polynomial ℕ).eval (encNat n).length = 2 * n.size := by
  rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, encNat_apply,
    Nat.size_eq_bits_len]

/-- On a prime the verifier answers "composite" on no coin word. -/
private theorem verifier_eq_false_of_prime {n : ℕ} (hn : n.Prime) (r : Fin (2 * n.size) → Bool) :
    Complexity.MillerRabin.verifier (n, List.ofFn r) = false := by
  have h := (Complexity.MillerRabin.decidesWithOneSidedError n).2
  rw [eval_two_mul_X_length] at h
  exact h (by simpa using hn) r

/-- On a number that is not prime the verifier answers "prime" on at most half of the coin
words. -/
private theorem two_mul_card_verifier_false_le {n : ℕ} (hn : ¬ n.Prime) :
    2 * (Finset.univ.filter fun r : Fin (2 * n.size) → Bool =>
      Complexity.MillerRabin.verifier (n, List.ofFn r) = false).card ≤ 2 ^ (2 * n.size) := by
  have h := (Complexity.MillerRabin.decidesWithOneSidedError n).1
  rw [eval_two_mul_X_length] at h
  have hyes := h (by simpa using hn)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * n.size) → Bool)))
    (fun r => Complexity.MillerRabin.verifier (n, List.ofFn r) = true)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Bool.not_eq_true] at hsplit
  omega

/-- A count that is at most half of `2 ^ k` has probability at most `1 / 2` out of `2 ^ k`. -/
private theorem natCast_div_two_pow_le_inv_two {c k : ℕ} (h : 2 * c ≤ 2 ^ k) :
    (c : ℝ≥0∞) / 2 ^ k ≤ 2⁻¹ := by
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  calc (c : ℝ≥0∞) = 2⁻¹ * (2 * c) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 2⁻¹ * 2 ^ k := by
        gcongr
        exact_mod_cast h

/-- **A prime passes every round.** -/
theorem eval_millerRabinRound_of_prime {n : ℕ} (hn : n.Prime) :
    ProbComp.eval (millerRabinRound n) true = 1 := by
  rw [eval_millerRabinRound_apply, Bool.not_true,
    Finset.filter_true_of_mem fun r _ => verifier_eq_false_of_prime hn r, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_self (by simp) (by simp)

/-- **A number that is not prime passes a round with probability at most `1 / 2`.** For an odd
composite this is the strong-liar bound `ZMod.two_mul_card_isStrongLiar_le`, through
`Complexity.MillerRabin.decidesWithOneSidedError`; `0`, `1` and the even numbers above `2` never
pass. -/
theorem eval_millerRabinRound_le_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    ProbComp.eval (millerRabinRound n) true ≤ 2⁻¹ := by
  rw [eval_millerRabinRound_apply, Bool.not_true]
  exact natCast_div_two_pow_le_inv_two (two_mul_card_verifier_false_le hn)

/-! ### Independent rounds -/

/-- The law of the test: the image of `t` independent rounds under `List.all`. -/
private theorem eval_millerRabinTest (n t : ℕ) :
    ProbComp.eval (millerRabinTest n t) =
      (ProbComp.eval (OracleComp.replicate t (millerRabinRound n))).map fun verdicts =>
        verdicts.all id := by
  simp only [millerRabinTest, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- **`t` rounds all pass** with the `t`-th power of the probability that one round passes. -/
theorem eval_millerRabinTest_true (n t : ℕ) :
    ProbComp.eval (millerRabinTest n t) true = ProbComp.eval (millerRabinRound n) true ^ t := by
  have hall : (fun verdicts : List Bool => verdicts.all id) ⁻¹' {true} =
      {verdicts | ∀ b ∈ verdicts, id b = true} := by
    ext verdicts
    simp
  have hone : {b : Bool | id b = true} = {true} := by
    ext b
    simp
  rw [eval_millerRabinTest, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    hall, ProbComp.toOuterMeasure_replicate_forall, hone, PMF.toOuterMeasure_apply_singleton]

/-- **A prime always passes the test** ([KatzLindell2020], Theorem 9.33). -/
theorem eval_millerRabinTest_of_prime {n : ℕ} (hn : n.Prime) (t : ℕ) :
    ProbComp.eval (millerRabinTest n t) true = 1 := by
  rw [eval_millerRabinTest_true, eval_millerRabinRound_of_prime hn, one_pow]

/-- **A composite passes `t` rounds with probability at most `2⁻ᵗ`** ([KatzLindell2020],
Theorem 9.33). The bound holds for every `n` that is not prime, including `0` and `1`. -/
theorem eval_millerRabinTest_le_of_not_prime {n : ℕ} (hn : ¬ n.Prime) (t : ℕ) :
    ProbComp.eval (millerRabinTest n t) true ≤ (2 ^ t)⁻¹ := by
  rw [eval_millerRabinTest_true, ENNReal.inv_pow]
  gcongr
  exact eval_millerRabinRound_le_of_not_prime hn

/-! ### Efficiency -/

/-- A round is a strict PPT program in the binary length of `n`. -/
theorem isPPTOn_millerRabinRound : Probability.IsPPTOn encNat encBool millerRabinRound := by
  have hsize : ComputableInPolyTime (fun n : ℕ => n.size) encNat encUnary := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using
      ComputableInPolyTime.encoding_length encNat
  have hcount : ComputableInPolyTime (fun n : ℕ => 2 * n.size) encNat encUnary := by
    simpa only [two_mul] using hsize.unary_add' hsize
  have hverdict : ComputableInPolyTime
      (fun x : ℕ × List Bool => !Complexity.MillerRabin.verifier x)
      (encPair encNat encBits) encBool := by
    have h := Complexity.MillerRabin.verifier_polyTime
    fun_prop
  refine (Probability.IsPPTOn.of_seeded hcount hverdict).congr fun n => ?_
  simp only [millerRabinRound, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- **The test is a strict PPT program** in the binary length of `n` and the number of rounds
`t`, given in unary. -/
theorem isPPTOn_millerRabinTest :
    Probability.IsPPTOn (encPair encNat encUnary) encBool
      fun x : ℕ × ℕ => millerRabinTest x.1 x.2 := by
  have hround : Probability.IsPPTOn (encPair encNat encUnary) encBool
      fun x : ℕ × ℕ => millerRabinRound x.1 :=
    isPPTOn_millerRabinRound.preprocess (by fun_prop)
  have hall : ComputableInPolyTime (fun verdicts : List Bool => verdicts.all id) encBits
      encBool :=
    ComputableInPolyTime.bitsAllWithInput (list := id) (test := fun _ b => b) (by fun_prop)
      (by fun_prop)
  refine ((hround.replicate_bool (count := fun x : ℕ × ℕ => x.2) (by fun_prop)).map hall).congr
    fun x => ?_
  simp only [millerRabinTest, ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

end Cslib.Crypto
