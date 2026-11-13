/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Repeat

/-!
# Repeated attempts that succeed through an independent coin

A simulator that guesses a verifier's challenge succeeds in each attempt only when its guess is
right. Its output is that of the honest interaction, `μ`, on success and nothing otherwise, and
whether an attempt succeeds is an independent coin `ch : PMF Bool`. After `k` independent
attempts, `firstSuccess d` returns the first successful output, or the fallback `d` when every
attempt failed. Every distinguisher then separates this from `μ` with advantage at most
`(ch false) ^ k`: the selected output has the law of `μ` except on the event that all `k`
attempts fail.

The independence is stated by `ProbComp.eval attempt = μ.bind (tagWith ch)`: the attempt's output
is drawn from `μ` and its success coin from `ch`, independently. For the zero-knowledge simulator
of Goldreich–Micali–Wigderson the coin is a uniform 3-bit guess hitting the verifier's challenge,
so that `ch false = 7 / 8`.

This is the rejection-sampling argument of a black-box simulator. The bounded retry loop
`Cslib.OracleComp.retry` runs a program lazily until a result passes a predicate and states the
law of the result; here every attempt is run and the bound is on the advantage against `μ`.

## Main definitions

* `Cslib.Crypto.mixWith`: run `p` when the coin `ch` shows `true` and `q` otherwise.
* `Cslib.Crypto.tagWith`: keep an output when an independent coin `ch` shows `true`.
* `Cslib.Crypto.firstSuccess`: the first successful attempt in a list, with a fallback.

## Main results

* `Cslib.Crypto.Game.advantage_mixWith`: mixing in `g2` with probability `ch false` scales the
  advantage against `g1` by `ch false`.
* `Cslib.Crypto.eval_firstSuccess_replicate_succ`: one more attempt mixes the law of `μ` with the
  law of the remaining attempts.
* `Cslib.Crypto.Game.advantage_bind_firstSuccess_replicate_le`: after `k` attempts, every
  continuation separates the first success from `μ` with advantage at most `(ch false) ^ k`.

## References

* [O. Goldreich, *Foundations of Cryptography: Volume 1, Basic Tools*][Goldreich2001],
  Section 4.3.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal ENNReal

/-- Run `p` when the coin `ch` shows `true`, and `q` when it shows `false`. -/
noncomputable def mixWith {α : Type*} (ch : PMF Bool) (p q : PMF α) : PMF α :=
  ch.bind fun b => if b then p else q

theorem bind_mixWith {α β : Type*} (ch : PMF Bool) (p q : PMF α) (f : α → PMF β) :
    (mixWith ch p q).bind f = mixWith ch (p.bind f) (q.bind f) := by
  simp only [mixWith, PMF.bind_bind]
  congr 1 with b : 1
  cases b <;> rfl

/-- Keep the output `out` when an independent coin `ch` shows `true`, and fail otherwise. -/
noncomputable def tagWith {β : Type*} (ch : PMF Bool) (out : β) : PMF (Option β) :=
  ch.map fun b => if b then some out else none

/-- The first successful attempt in `attempts`, or `d` when every attempt failed. -/
def firstSuccess {β : Type*} (d : β) (attempts : List (Option β)) : β :=
  ((attempts.filter Option.isSome).headD none).getD d

@[simp] theorem firstSuccess_nil {β : Type*} (d : β) :
    firstSuccess d ([] : List (Option β)) = d := rfl

@[simp] theorem firstSuccess_cons {β : Type*} (d : β) (o : Option β) (xs : List (Option β)) :
    firstSuccess d (o :: xs) = o.getD (firstSuccess d xs) := by
  cases o <;> rfl

/-- The first success is the fallback or one of the successful attempts. -/
theorem firstSuccess_eq_or_mem {β : Type*} (d : β) (xs : List (Option β)) :
    firstSuccess d xs = d ∨ some (firstSuccess d xs) ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons o xs ih =>
    cases o with
    | none => simpa using ih
    | some x => simp

/-- One more attempt succeeds with the law of `μ` when its coin shows `true`, and otherwise falls
back to the first success among the remaining attempts. -/
theorem eval_firstSuccess_replicate_succ {β : Type} (d : β) {attempt : ProbComp (Option β)}
    {ch : PMF Bool} {μ : PMF β} (hattempt : ProbComp.eval attempt = μ.bind (tagWith ch)) (k : ℕ) :
    ProbComp.eval (firstSuccess d <$> OracleComp.replicate (k + 1) attempt) =
      mixWith ch μ (ProbComp.eval (firstSuccess d <$> OracleComp.replicate k attempt)) := by
  simp only [OracleComp.replicate_succ, map_bind, Functor.map_map, firstSuccess_cons,
    ProbComp.eval_bind, ProbComp.eval_map, hattempt, tagWith, PMF.bind_bind, PMF.bind_map,
    mixWith]
  rw [PMF.bind_comm]
  congr 1 with b : 1
  cases b
  · simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      PMF.bind_const]
  · have hconst (b : β) : PMF.map (fun _ => b)
        (ProbComp.eval (OracleComp.replicate k attempt)) = PMF.pure b := PMF.map_const _ b
    simp only [Function.comp_apply, ↓reduceIte, Option.getD_some, hconst, PMF.bind_pure]

namespace Game

/-- Mixing in `g2` with probability `ch false` scales the advantage against `g1` by `ch false`. -/
theorem advantage_mixWith (ch : PMF Bool) (g1 g2 : Game) :
    advantage (mixWith ch g1 g2) g1 = (ch false).toNNReal * advantage g2 g1 := by
  have hsum : (ch true).toReal + (ch false).toReal = 1 := by
    simpa [add_comm] using Probability.PMF.sum_toReal ch
  have hmix : (succProbability (mixWith ch g1 g2) : ℝ) =
      (ch true).toReal * (succProbability g1 : ℝ) +
        (ch false).toReal * (succProbability g2 : ℝ) := by
    simp only [coe_succProbability, mixWith, Probability.PMF.bind_apply_toReal, Fintype.univ_bool,
      Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, ↓reduceIte, Bool.false_eq_true]
  apply NNReal.eq
  rw [NNReal.coe_mul, coe_advantage, coe_advantage, hmix,
    show (ch true).toReal * (succProbability g1 : ℝ) + (ch false).toReal * succProbability g2 -
        succProbability g1 = (ch false).toReal * (succProbability g2 - succProbability g1) by
      linear_combination (succProbability g1 : ℝ) * hsum,
    abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.coe_toNNReal_eq_toReal (ch false)]

/-- **Repeated attempts.** If each attempt has the law of `μ` on success and succeeds through an
independent coin `ch`, then after `k` attempts every continuation `f` separates the first success
from `μ` with advantage at most `(ch false) ^ k`, the probability that all attempts fail. -/
theorem advantage_bind_firstSuccess_replicate_le {β : Type} (d : β)
    {attempt : ProbComp (Option β)} {ch : PMF Bool} {μ : PMF β}
    (hattempt : ProbComp.eval attempt = μ.bind (tagWith ch)) (f : β → Game) (k : ℕ) :
    advantage ((ProbComp.eval (firstSuccess d <$> OracleComp.replicate k attempt)).bind f)
      (μ.bind f) ≤ (ch false).toNNReal ^ k := by
  induction k with
  | zero => simpa using advantage_le_one _ _
  | succ k ih =>
    rw [eval_firstSuccess_replicate_succ d hattempt, bind_mixWith, advantage_mixWith, pow_succ']
    gcongr

end Game

end Cslib.Crypto
