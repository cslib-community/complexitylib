/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.Basic

/-!
# Correlation-robust hash families

A family of functions `H : Fin m → K → L`, indexed by the position `j` of a query, is correlation
robust when the outputs `H j (t j + s)` on uniform inputs `t j` all shifted by one hidden uniform
offset `s` look uniform, even given the inputs `t`. This is the property of Ishai, Kilian, Nissim
and Petrank [IshaiKilianNissimPetrank2003, Definition 1] that replaces the random oracle in their
oblivious-transfer extension (`Cslib.Crypto.Protocols.MPC.iknpProtocol`). Their definition takes
`K` to be bit strings and one function `h` for every position; the family here allows the `j`-th
query to use its own function `H j`, as their protocol does, and `H j = h` recovers their form.

The real game samples `s` and `t` and hands `(t, fun j => H j (t j + s))` to a distinguisher; the
ideal game hands it `(t, u)` with `u` uniform. The advantage is the distinguishing advantage of the
two games. As for `Cslib.Crypto.PRF.advantage`, it is concrete: `m`, `H` and the distinguisher are
fixed, and computational security is a bound on it for a class of efficient distinguishers.

## Main definitions

* `Cslib.Crypto.CorrelationRobust.Adversary`: a distinguisher on inputs and outputs.
* `Cslib.Crypto.CorrelationRobust.realGame`, `Cslib.Crypto.CorrelationRobust.idealGame`: the
  correlated and uniform experiments.
* `Cslib.Crypto.CorrelationRobust.advantage`: their distinguishing advantage.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003], Definition 1.
-/

@[expose] public section

namespace Cslib.Crypto.CorrelationRobust

open scoped NNReal

variable {m : ℕ} {K L : Type}

/-- A randomized test on `m` inputs in `K` and `m` outputs in `L`. -/
abbrev Adversary (m : ℕ) (K L : Type) := (Fin m → K) × (Fin m → L) → ProbComp Bool

/-- The real experiment: sample a uniform offset `s` and uniform inputs `t`, and test
`(t, fun j => H j (t j + s))`. -/
noncomputable def realGame [Fintype K] [Nonempty K] [Add K] (H : Fin m → K → L)
    (adversary : Adversary m K L) : Game :=
  ProbComp.eval do
    let s ← ProbComp.uniform K
    let t ← ProbComp.uniform (Fin m → K)
    adversary (t, fun j => H j (t j + s))

/-- The ideal experiment: sample uniform inputs `t` and uniform outputs `u`, and test `(t, u)`. -/
noncomputable def idealGame [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    (adversary : Adversary m K L) : Game :=
  ProbComp.eval do
    let t ← ProbComp.uniform (Fin m → K)
    let u ← ProbComp.uniform (Fin m → L)
    adversary (t, u)

/-- The correlation-robustness advantage of `adversary` against `H`. -/
noncomputable abbrev advantage [Fintype K] [Nonempty K] [Add K] [Fintype L] [Nonempty L]
    (H : Fin m → K → L) (adversary : Adversary m K L) : ℝ≥0 :=
  Game.advantage (realGame H adversary) (idealGame adversary)

end Cslib.Crypto.CorrelationRobust
