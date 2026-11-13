/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Notation

/-!
# Security experiments as programs

A security experiment is the challenger's program: it samples, runs the adversary and returns a
bit. `Experiment` is that program, a `ProbComp Bool`, and mirrors `Game := PMF Bool`, its output
distribution. Scheme algorithms, adversaries and experiments are written as programs, and
`ProbComp.eval` appears only where a probability is taken: in `Experiment.succProbability` and
`Experiment.advantage`, which are the `Game` notions of the evaluated programs.

Names follow one convention. A `…Experiment` is one instance, at fixed parameters (a group, a key
space, a security parameter already chosen). A `…Game` is a family: `Game.withSetup` draws public
parameters from a setup law, which need not be efficiently sampleable, and then runs the fixed
experiment. When the setup is itself a program, such as key generation, the experiment binds it:
`Experiment.advantage_bind_le_of_support` and `Experiment.succProbability_bind_le_of_support`
lift a bound that holds at every possible output of the setup program.

`Experiment.succProbability` and `Experiment.advantage` are reducible abbreviations, so `simp` and
term-mode applications of the `Game` lemmas see through them. `rw` matches syntactically: unfold
with `simp only [Experiment.advantage]` before rewriting with a `Game` lemma.

`distAdvantage real sim D` is the advantage of a distinguisher `D` between two view distributions,
as in simulation-based definitions.

## Main definitions

* `Cslib.Crypto.Experiment`: a security experiment, as a program returning a bit.
* `Cslib.Crypto.Experiment.succProbability`, `Cslib.Crypto.Experiment.advantage`: the success
  probability of an experiment and the distinguishing advantage between two experiments.
* `Cslib.Crypto.distAdvantage`: the advantage of a distinguisher between two view distributions.
* `Cslib.Crypto.Game.withSetup`: the game that draws public parameters and runs an experiment.

## Main results

* `Cslib.Crypto.Experiment.coe_succProbability`, `Cslib.Crypto.Experiment.coe_advantage`: as real
  numbers, the success probability is `Pr[e]` and the advantage is `|Pr[e₀] - Pr[e₁]|`.
* `Cslib.Crypto.distAdvantage_eq_zero_of_eval_eq`: a perfect simulation has advantage zero.
* `Cslib.Crypto.Game.withSetup_pure`: a point setup law runs one experiment.
* `Cslib.Crypto.Game.advantage_withSetup_le`, `Cslib.Crypto.Game.succProbability_withSetup_le`: a
  bound for every supported parameter bounds the game.
* `Cslib.Crypto.Experiment.advantage_bind_le_of_support`,
  `Cslib.Crypto.Experiment.succProbability_bind_le_of_support`: a bound for every output of a setup
  program bounds the experiment that runs it first.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability
open scoped NNReal

/-- A security experiment: the challenger's program, which returns whether the adversary won (for
a search or forgery experiment) or the adversary's guess (for a distinguishing experiment). Its
output distribution is the `Game` `ProbComp.eval e`. -/
abbrev Experiment : Type := ProbComp Bool

namespace Experiment

/-- The success probability of an experiment: the probability that it returns `true`. -/
noncomputable abbrev succProbability (e : Experiment) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval e)

/-- The distinguishing advantage between two experiments: the absolute difference of their
success probabilities ([BonehShoup2023], Section 3.1). -/
noncomputable abbrev advantage (e₀ e₁ : Experiment) : ℝ≥0 :=
  Game.advantage (ProbComp.eval e₀) (ProbComp.eval e₁)

/-- As a real number, the success probability of an experiment is `Pr[e]`. -/
theorem coe_succProbability (e : Experiment) : (succProbability e : ℝ) = Pr[e] := rfl

/-- As a real number, the advantage between two experiments is `|Pr[e₀] - Pr[e₁]|`. -/
theorem coe_advantage (e₀ e₁ : Experiment) : (advantage e₀ e₁ : ℝ) = |Pr[e₀] - Pr[e₁]| :=
  Game.coe_advantage _ _

end Experiment

/-- The advantage of the distinguisher `D` between the view distributions `real` and `sim`: the
advantage between running `D` on a real view and on a simulated one. -/
noncomputable abbrev distAdvantage {V : Type} (real sim : ProbComp V) (D : V → Experiment) :
    ℝ≥0 :=
  Experiment.advantage (real >>= D) (sim >>= D)

/-- A perfect simulation, one with the same view distribution, gives every distinguisher
advantage zero. -/
theorem distAdvantage_eq_zero_of_eval_eq {V : Type} {real sim : ProbComp V}
    (h : ProbComp.eval real = ProbComp.eval sim) (D : V → Experiment) :
    distAdvantage real sim D = 0 := by
  simp only [distAdvantage, Experiment.advantage, ProbComp.eval_bind, h, Game.advantage_self]

namespace Game

/-- The game that draws public parameters `p` from the setup law `setup` and runs the experiment
`exp p`. The setup law is a distribution, not a program: it need not be efficiently
sampleable. -/
noncomputable def withSetup {P : Type} (setup : PMF P) (exp : P → Experiment) : Game :=
  setup.bind fun p => ProbComp.eval (exp p)

/-- With a point setup law, the game is the evaluated experiment. -/
@[simp] theorem withSetup_pure {P : Type} (p : P) (exp : P → Experiment) :
    withSetup (PMF.pure p) exp = ProbComp.eval (exp p) :=
  PMF.pure_bind _ _

/-- A bound on the advantage between two experiments at every supported parameter bounds the
advantage between the games over the same setup law. -/
theorem advantage_withSetup_le {P : Type} (setup : PMF P) (exp₀ exp₁ : P → Experiment)
    {ε : ℝ≥0} (h : ∀ p ∈ setup.support, Experiment.advantage (exp₀ p) (exp₁ p) ≤ ε) :
    advantage (withSetup setup exp₀) (withSetup setup exp₁) ≤ ε :=
  advantage_bind_le_of_support setup _ _ h

/-- A bound on the success probability of an experiment at every supported parameter bounds the
success probability of the game. -/
theorem succProbability_withSetup_le {P : Type} (setup : PMF P) (exp : P → Experiment)
    {ε : ℝ≥0} (h : ∀ p ∈ setup.support, Experiment.succProbability (exp p) ≤ ε) :
    succProbability (withSetup setup exp) ≤ ε := by
  have hle := advantage_withSetup_le setup exp (fun _ => pure false) fun p hp => by
    simpa only [Experiment.advantage, ProbComp.eval_pure, advantage_pure_false] using h p hp
  simpa only [withSetup, ProbComp.eval_pure, PMF.bind_const, advantage_pure_false] using hle

end Game

/-- The experiment that runs a setup program and then an experiment on its output is the game
over the setup's output distribution. -/
theorem Experiment.eval_bind_eq_withSetup {P : Type} (setup : ProbComp P) (exp : P → Experiment) :
    ProbComp.eval (setup >>= exp) = Game.withSetup (ProbComp.eval setup) exp :=
  ProbComp.eval_bind _ _

/-- A bound on the advantage at every possible output of a setup program, such as key generation,
bounds the advantage between the experiments that run it first. -/
theorem Experiment.advantage_bind_le_of_support {P : Type} (setup : ProbComp P)
    (exp₀ exp₁ : P → Experiment) {ε : ℝ≥0}
    (h : ∀ p ∈ (ProbComp.eval setup).support, Experiment.advantage (exp₀ p) (exp₁ p) ≤ ε) :
    Experiment.advantage (setup >>= exp₀) (setup >>= exp₁) ≤ ε := by
  simp only [Experiment.advantage, Experiment.eval_bind_eq_withSetup]
  exact Game.advantage_withSetup_le _ _ _ h

/-- A bound on the success probability at every possible output of a setup program bounds the
success probability of the experiment that runs it first. -/
theorem Experiment.succProbability_bind_le_of_support {P : Type} (setup : ProbComp P)
    (exp : P → Experiment) {ε : ℝ≥0}
    (h : ∀ p ∈ (ProbComp.eval setup).support, Experiment.succProbability (exp p) ≤ ε) :
    Experiment.succProbability (setup >>= exp) ≤ ε := by
  simp only [Experiment.succProbability, Experiment.eval_bind_eq_withSetup]
  exact Game.succProbability_withSetup_le _ _ h

end Cslib.Crypto
