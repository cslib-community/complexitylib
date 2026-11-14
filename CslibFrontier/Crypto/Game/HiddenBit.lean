/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment

/-!
# Guessing a hidden bit

A distinguishing game between two experiments `e false` and `e true` has a bit-guessing form:
draw a uniform hidden bit `b`, run `e b` and win when the output equals `b`.
`Experiment.guessBit e` is that experiment. The distinguishing advantage is twice the bias of the
bit-guessing experiment over a fair coin, and a guess that does not depend on the hidden bit is
right with probability exactly one half.

## Main definitions

* `Cslib.Crypto.Experiment.guessBit`: the bit-guessing form of a pair of experiments.

## Main results

* `Cslib.Crypto.Game.succProbability_uniform_bool_beq`: the success probability of guessing a
  uniform hidden bit with the output of `g bit`.
* `Cslib.Crypto.Game.advantage_eq_two_mul_guessingAdvantage_uniform_bool_beq`: the advantage
  between `g false` and `g true` is twice the guessing advantage of the hidden-bit game.
* `Cslib.Crypto.Game.uniform_bool_bind_map_beq_const`: a guess drawn independently of the hidden
  bit leaves the outcome uniform.
* `Cslib.Crypto.Experiment.eval_guessBit`,
  `Cslib.Crypto.Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit`: the same facts for
  experiments.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped NNReal

namespace Game

/-- For any Boolean-indexed family of games `g : Bool → Game`, sampling a uniform hidden bit
`bit ← PMF.uniformOfFintype Bool` and outputting `guess == bit` for `guess ← g bit` succeeds with
probability `(1 - succProbability (g false) + succProbability (g true)) / 2`. This is
`succProbability_uniform_bool_xor` with the complementary output convention. -/
theorem succProbability_uniform_bool_beq (g : Bool → Game) :
    (succProbability
      ((PMF.uniformOfFintype Bool).bind fun bit => (g bit).map (fun guess => guess == bit)) : ℝ) =
      (1 - (succProbability (g false) : ℝ) + succProbability (g true)) / 2 := by
  have hmap :
      ((PMF.uniformOfFintype Bool).bind fun bit => (g bit).map (fun guess => guess == bit)) =
        ((PMF.uniformOfFintype Bool).bind fun bit =>
          (g bit).map (fun guess => guess ^^ bit)).map Bool.not := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun bit => ?_)
    rw [PMF.map_comp]
    refine congrArg _ (funext fun guess => ?_)
    cases guess <;> cases bit <;> rfl
  rw [hmap, succProbability_not, failProbability_eq, NNReal.coe_sub (succProbability_le_one _),
    NNReal.coe_one, succProbability_uniform_bool_xor]
  ring

/-- The advantage between `g false` and `g true` is twice the guessing advantage of the game that
guesses a uniform hidden bit `bit` with the output of `g bit`. -/
theorem advantage_eq_two_mul_guessingAdvantage_uniform_bool_beq (g : Bool → Game) :
    advantage (g false) (g true) =
      2 * guessingAdvantage
        ((PMF.uniformOfFintype Bool).bind fun bit => (g bit).map (fun guess => guess == bit)) := by
  have key : ∀ a b : ℝ, |a - b| = 2 * |(1 - a + b) / 2 - 1 / 2| := fun a b => by
    rw [show (1 - a + b) / 2 - 1 / 2 = (b - a) / 2 by ring, abs_div, Nat.abs_ofNat, abs_sub_comm]
    ring
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_ofNat, coe_guessingAdvantage, succProbability_uniform_bool_beq,
    coe_advantage]
  exact key _ _

/-- Guessing a uniform hidden bit with a guess drawn from `m`, independently of the bit, leaves
the outcome a fair coin. -/
theorem uniform_bool_bind_map_beq_const (m : PMF Bool) :
    ((PMF.uniformOfFintype Bool).bind fun bit => m.map (fun guess => guess == bit)) =
      PMF.uniformOfFintype Bool := by
  calc ((PMF.uniformOfFintype Bool).bind fun bit => m.map (fun guess => guess == bit))
      = m.bind fun guess => (PMF.uniformOfFintype Bool).map (fun bit => guess == bit) := by
        simp only [PMF.map, PMF.bind_comm (PMF.uniformOfFintype Bool) m]
        rfl
    _ = m.bind fun _ => PMF.uniformOfFintype Bool := by
        refine congrArg _ (funext fun guess => ?_)
        exact PMF.uniformOfFintype_map_equiv
          (Equiv.ofBijective (fun bit => guess == bit) (by cases guess <;> decide))
    _ = PMF.uniformOfFintype Bool := PMF.bind_const _ _

end Game

namespace Experiment

/-- The bit-guessing form of the experiments `e false` and `e true`: draw a uniform hidden bit
`b`, run `e b` and return whether its output equals `b`. -/
noncomputable def guessBit (e : Bool → Experiment) : Experiment := do
  let b ← ProbComp.uniform Bool
  (· == b) <$> e b

theorem eval_guessBit (e : Bool → Experiment) :
    ProbComp.eval (guessBit e) =
      (PMF.uniformOfFintype Bool).bind fun b => (ProbComp.eval (e b)).map (· == b) := by
  simp only [guessBit, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_map]

/-- The advantage between `e false` and `e true` is twice the guessing advantage of their
bit-guessing form. -/
theorem advantage_eq_two_mul_guessingAdvantage_guessBit (e : Bool → Experiment) :
    advantage (e false) (e true) = 2 * Game.guessingAdvantage (ProbComp.eval (guessBit e)) := by
  rw [eval_guessBit]
  exact Game.advantage_eq_two_mul_guessingAdvantage_uniform_bool_beq fun b => ProbComp.eval (e b)

end Experiment

end Cslib.Crypto
