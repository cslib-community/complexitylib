/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.Oracle

/-!
# Finite pseudorandom functions

A keyed function `F : Key → D → R` on finite types is compared with a uniformly random function
`D → R` by an adaptive oracle adversary with private coins. The real game samples one uniform key
and answers every query with `F key`; the ideal game samples one whole random function and reuses
it across queries. The adversary's private samples are independent of the key or table. The
advantage is the distinguishing advantage of the two games.

This is the concrete, single-key form of PRF security for arbitrary finite domains and ranges. It
complements the word-level asymptotic games `Cslib.Crypto.prfRealGame` and
`Cslib.Crypto.prfIdealGame`, and the same-domain-and-range games without private coins used for
the Luby–Rackoff hybrids (`Cslib.Crypto.LubyRackoff.prfSingleRealGame`).

## Main definitions

* `Cslib.Crypto.PRF.Adversary`: an adaptive oracle test with private coins.
* `Cslib.Crypto.PRF.realGame`, `Cslib.Crypto.PRF.idealGame`: the keyed and random-function
  experiments.
* `Cslib.Crypto.PRF.advantage`: their distinguishing advantage.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/

@[expose] public section

namespace Cslib.Crypto.PRF

open scoped NNReal

variable {Key D R : Type}

/-- An adaptive test with private coins and oracle access to a function `D → R`. -/
abbrev Adversary (D R : Type) := ProbOracleComp (fun _ : D => R) Bool

/-- The real experiment: sample one uniform key and answer every query `x` with `F key x`. -/
noncomputable def realGame [Fintype Key] [Nonempty Key] (F : Key → D → R)
    (adversary : Adversary D R) : Game :=
  ProbComp.eval do
    let key ← ProbComp.uniform Key
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun x => pure (F key x)) adversary

/-- The ideal experiment: sample one uniform function `D → R` and answer every query with it. -/
noncomputable def idealGame [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    (adversary : Adversary D R) : Game :=
  ProbComp.eval do
    let f ← ProbComp.uniform (D → R)
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun x => pure (f x)) adversary

/-- The PRF distinguishing advantage of `adversary` against `F`. -/
noncomputable abbrev advantage [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D]
    [Fintype R] [Nonempty R] (F : Key → D → R) (adversary : Adversary D R) : ℝ≥0 :=
  Game.advantage (realGame F adversary) (idealGame adversary)

end Cslib.Crypto.PRF
