/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Oracle.Run

/-!
# Finite pseudorandom functions

A keyed function `F : Key → D → R` on finite types is compared with a uniformly random function
`D → R` by an adaptive oracle adversary with private coins ([BonehShoup2023], Section 4.4, Attack
Game 4.2). The real experiment samples one uniform key and answers every query `x` with `F key x`;
the ideal experiment samples one whole random function `f` and answers every query with `f x`. The
adversary's private samples are independent of the key or table. The advantage is the
distinguishing advantage of the two experiments.

This is the concrete, single-key form of PRF security for arbitrary finite domains and ranges. It
complements the word-level asymptotic games `Cslib.Crypto.prfRealGame` and
`Cslib.Crypto.prfIdealGame`. Several independent keys reduce to this game through the hybrid
reductions of `Cslib.Crypto.PRF.multiKeyReduction`, which the finite Luby–Rackoff theorems use.

## Main definitions

* `Cslib.Crypto.PRF.Adversary`: an adaptive oracle test with private coins.
* `Cslib.Crypto.PRF.realExperiment`, `Cslib.Crypto.PRF.idealExperiment`: the keyed and
  random-function experiments.
* `Cslib.Crypto.PRF.advantage`: their distinguishing advantage.

## Main results

* `Cslib.Crypto.PRF.eval_realExperiment`, `Cslib.Crypto.PRF.eval_idealExperiment`: the laws of the
  two experiments, with the key or the random function sampled at the `PMF` level.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 4.4,
  Attack Game 4.2 and Definition 4.2.
-/

@[expose] public section

namespace Cslib.Crypto.PRF

open Probability
open scoped NNReal

variable {Key D R : Type}

/-- An adaptive test with private coins and oracle access to a function `D → R`. -/
abbrev Adversary (D R : Type) := ProbOracleComp (fun _ : D => R) Bool

/-- The real experiment: sample one uniform key and answer every query `x` with `F key x`. -/
noncomputable def realExperiment [Fintype Key] [Nonempty Key] (F : Key → D → R)
    (A : Adversary D R) : ProbComp Bool := do
  let key ← ProbComp.uniform Key
  A.run fun x => pure (F key x)

/-- The ideal experiment: sample one uniform function `f : D → R` and answer every query `x` with
`f x`. -/
noncomputable def idealExperiment [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    (A : Adversary D R) : ProbComp Bool := do
  let f ← ProbComp.uniform (D → R)
  A.run fun x => pure (f x)

/-- The PRF distinguishing advantage of `A` against `F`. -/
noncomputable abbrev advantage [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D]
    [Fintype R] [Nonempty R] (F : Key → D → R) (A : Adversary D R) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (realExperiment F A)) (ProbComp.eval (idealExperiment A))

/-- The law of `realExperiment`: a uniform key, then the adversary interpreted at the `PMF` level
against `F key`. -/
theorem eval_realExperiment [Fintype Key] [Nonempty Key] (F : Key → D → R) (A : Adversary D R) :
    ProbComp.eval (realExperiment F A) =
      (PMF.uniformOfFintype Key).bind fun key =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun x => PMF.pure (F key x)) A := by
  simp only [realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure]

/-- The law of `idealExperiment`: a uniform function `f`, then the adversary interpreted at the
`PMF` level against `f`. -/
theorem eval_idealExperiment [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    (A : Adversary D R) :
    ProbComp.eval (idealExperiment A) =
      (PMF.uniformOfFintype (D → R)).bind fun f =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun x => PMF.pure (f x)) A := by
  simp only [idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure]

end Cslib.Crypto.PRF
