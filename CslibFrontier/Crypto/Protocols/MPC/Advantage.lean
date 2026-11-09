/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.MPC.Basic

/-!
# Distinguishing advantage for semi-honest privacy

`PerfectSemiHonestPrivate` asks the ideal and real joint view-and-output distributions to be
equal. Goldreich's Definitions 7.2.1 and 7.5.1 ask them to be computationally indistinguishable.
This module provides the concrete quantity behind that requirement:
`semiHonestAdvantage proto W f I S x D` is the advantage of a distinguisher `D`, a randomized test
on the coalition's views and all parties' outputs, between the ideal execution with simulator `S`
(`idealJoint`) and the real execution (`Protocol.realJoint`) on the input tuple `x`.

The quantity is concrete and per instance: the protocol, input tuple and distinguisher are
fixed, and there is no security parameter or efficiency requirement on `D` or `S`. A
computational security statement bounds it for a class of distinguishers, for instance by the
advantage of explicit reductions against a primitive. Perfect privacy is the case where it
vanishes for every distinguisher (`semiHonestAdvantage_eq_zero_iff`).

Singleton coalitions `{i}` give the two-party form of the definition, with one simulator per
corrupted party; `singletonView` and `restrict_singleton` move a single view in and out of the
coalition-indexed tuples.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage`: the distinguishing advantage between the
  ideal and real joint distributions.
* `Cslib.Crypto.Protocols.MPC.singletonView`: a single view as a tuple over the coalition `{i}`.

## Main results

* `Cslib.Crypto.Protocols.MPC.semiHonestAdvantage_eq_zero_iff`: zero advantage against every
  distinguisher is equality of the ideal and real joint distributions.
* `Cslib.Crypto.Protocols.MPC.PerfectSemiHonestPrivate.semiHonestAdvantage_eq_zero`: perfect
  privacy gives zero advantage.
* `Cslib.Crypto.Protocols.MPC.restrict_singleton`: restricting a tuple of views to `{i}`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.2.2.1 (Definition 7.2.1, pp. 620–622) and Section 7.5.1.2 (Definition 7.5.1,
  pp. 696–697).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability
open scoped NNReal

variable {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec} {In Coins Out : Fin m → Type}

/-- The advantage of a distinguisher `D` between the ideal joint view-and-output distribution of
the coalition `I` with simulator `S` and the real one of `proto` in world `W`, on the input tuple
`x` (cf. Goldreich Def. 7.5.1, Eq. 7.40, p. 696, with a concrete advantage in place of
computational indistinguishability). -/
@[expose] noncomputable def semiHonestAdvantage (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out) (I : Finset (Fin m))
    (S : CoalitionSimulator sc In Coins Out I) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i) → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (idealJoint f I S x >>= D))
    ((proto.realJoint W I x).bind fun r => ProbComp.eval (D r))

/-- The probability that a pointwise test accepts is the probability of its point. -/
private theorem bind_eval_decide_eq {α : Type} [DecidableEq α] (p : PMF α) (a : α) :
    (p.bind fun r => ProbComp.eval (pure (decide (r = a)) : ProbComp Bool)) true = p a := by
  simp only [ProbComp.eval_pure, PMF.bind_apply, PMF.pure_apply]
  rw [tsum_eq_single a fun r hr => by simp [hr]]
  simp

/-- **Perfect privacy is zero advantage**: the ideal and real joint distributions of `I` are
equal exactly when every distinguisher has advantage zero. -/
theorem semiHonestAdvantage_eq_zero_iff (proto : Protocol m spec sc In Coins Out)
    (W : MultiOracleWorld spec) (f : Functionality m In Out) (I : Finset (Fin m))
    (S : CoalitionSimulator sc In Coins Out I) (x : (i : Fin m) → In i) :
    (∀ D, semiHonestAdvantage proto W f I S x D = 0) ↔
      ProbComp.eval (idealJoint f I S x) = proto.realJoint W I x := by
  constructor
  · intro h
    ext a
    classical
    have ha := h fun r => pure (decide (r = a))
    rw [semiHonestAdvantage, Game.advantage, nndist_eq_zero, ProbComp.eval_bind,
      Game.succProbability, Game.succProbability, bind_eval_decide_eq, bind_eval_decide_eq] at ha
    exact (ENNReal.toNNReal_eq_toNNReal_iff' (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)).mp ha
  · intro h D
    rw [semiHonestAdvantage, ProbComp.eval_bind, h]
    exact Game.advantage_self _

/-- Perfect semi-honest privacy gives zero advantage against every distinguisher. -/
theorem PerfectSemiHonestPrivate.semiHonestAdvantage_eq_zero
    {proto : Protocol m spec sc In Coins Out} {W : MultiOracleWorld spec}
    {f : Functionality m In Out} {S : (I : Finset (Fin m)) → CoalitionSimulator sc In Coins Out I}
    (h : PerfectSemiHonestPrivate proto W f S) (I : Finset (Fin m)) (x : (i : Fin m) → In i)
    (D : ((i : I) → PartyView In Coins sc i) × ((i : Fin m) → Out i) → ProbComp Bool) :
    semiHonestAdvantage proto W f I (S I) x D = 0 :=
  (semiHonestAdvantage_eq_zero_iff proto W f I (S I) x).mpr (h I x) D

/-! ### Singleton coalitions -/

/-- A single view of party `i` as a tuple over the coalition `{i}`. -/
@[expose] def singletonView {i : Fin m} (v : PartyView In Coins sc i) :
    (j : ({i} : Finset (Fin m))) → PartyView In Coins sc j :=
  fun j => (Finset.mem_singleton.mp j.2).symm ▸ v

/-- Restricting a tuple of views to the coalition `{i}` keeps only the view of `i`. -/
theorem restrict_singleton (i : Fin m) (v : (j : Fin m) → PartyView In Coins sc j) :
    ({i} : Finset (Fin m)).restrict v = singletonView (v i) := by
  funext j
  obtain ⟨j, hj⟩ := j
  obtain rfl := Finset.mem_singleton.mp hj
  rfl

end Cslib.Crypto.Protocols.MPC
