/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Basic
public import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin

/-!
# Strong Nash equilibria

A coalition `A` of players has a **beneficial deviation** from a profile `s` if its members can
jointly switch strategies so that none of them is worse off and at least one is strictly better
off, while the players outside `A` keep their strategies. A **strong Nash equilibrium** is a
profile from which no coalition has a beneficial deviation ([Roughgarden2013CS364A], Lecture #15,
Definition 3.1). A joint deviation of `A` to the strategies of a profile `t` is the profile
`A.piecewise t s`.

The literature uses "strong equilibrium" for two notions. Lecture #15 lets a coalition deviate when
no member loses and some member gains; this is `IsStrongNash`. The weaker requirement that no
nonempty coalition has a deviation from which *every* member strictly gains (the definition in
[BabaioffChuangFeldman2007], Exercise 23.6, stated there for utilities; nonemptiness is implicit
there, since the empty coalition would block every profile) is `IsStrongEquilibrium`. Every strong
Nash equilibrium is a strong equilibrium (`IsStrongNash.isStrongEquilibrium`), and the converse
fails (see the tests). Bounds proved for strong equilibria therefore also hold for strong Nash
equilibria.

Singleton coalitions are unilateral deviations, so every strong equilibrium, and hence every strong
Nash equilibrium, is a pure Nash equilibrium (`IsStrongEquilibrium.isPureNash`,
`IsStrongNash.isPureNash`). The grand coalition shows that a strong Nash equilibrium is Pareto
optimal (Pareto efficient): no profile makes every player weakly and some player strictly better
off (`IsStrongNash.not_pareto`). The basic tool for bounding the cost of strong equilibria is
`IsStrongEquilibrium.exists_cost_le`: whatever joint deviation a nonempty coalition considers, one
of its members does not gain.

## Main definitions

* `Cslib.GameTheory.CostGame.IsBeneficialDeviation`: the coalition `A` gains by deviating to the
  strategies of `t`, with no member worse off and some member strictly better off.
* `Cslib.GameTheory.CostGame.IsStrongNash`: no coalition has a beneficial deviation.
* `Cslib.GameTheory.CostGame.IsStrictlyBeneficialDeviation`: the nonempty coalition `A` gains by
  deviating to the strategies of `t`, with every member strictly better off.
* `Cslib.GameTheory.CostGame.IsStrongEquilibrium`: no coalition has a strictly beneficial
  deviation.

## Main results

* `Cslib.GameTheory.CostGame.isStrongEquilibrium_iff`: a profile is a strong equilibrium iff every
  joint deviation of a nonempty coalition leaves some member no better off.
* `Cslib.GameTheory.CostGame.IsStrongNash.isStrongEquilibrium`: a strong Nash equilibrium is a
  strong equilibrium.
* `Cslib.GameTheory.CostGame.IsStrongEquilibrium.isPureNash`,
  `Cslib.GameTheory.CostGame.IsStrongNash.isPureNash`: strong equilibria and strong Nash equilibria
  are pure Nash equilibria.
* `Cslib.GameTheory.CostGame.IsStrongNash.not_pareto`: a strong Nash equilibrium is Pareto optimal.

## References

* [BabaioffChuangFeldman2007]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- The coalition `A` has a **beneficial deviation** from `s` to the strategies of `t`: at the
profile `A.piecewise t s`, in which the members of `A` play as in `t` and the others as in `s`,
no member of `A` pays more than at `s` and some member pays strictly less
([Roughgarden2013CS364A], Lecture #15, Definition 3.1(a)). -/
@[expose] def IsBeneficialDeviation (s : ∀ i, S i) (A : Finset ι) (t : ∀ i, S i) : Prop :=
  (∀ i ∈ A, G.cost i (A.piecewise t s) ≤ G.cost i s) ∧
    ∃ i ∈ A, G.cost i (A.piecewise t s) < G.cost i s

/-- A profile `s` is a **strong Nash equilibrium** if no coalition has a beneficial deviation from
it ([Roughgarden2013CS364A], Lecture #15, Definition 3.1(b)). A deviation counts as soon as no
member of the coalition loses and some member gains; `IsStrongEquilibrium` is the weaker notion in
which every member must gain. -/
@[expose] def IsStrongNash (s : ∀ i, S i) : Prop :=
  ∀ A t, ¬ G.IsBeneficialDeviation s A t

/-- The coalition `A` has a **strictly beneficial deviation** from `s` to the strategies of `t`:
`A` is nonempty and every member of `A` pays strictly less at `A.piecewise t s` than at `s`
([BabaioffChuangFeldman2007], Exercise 23.6). -/
@[expose] def IsStrictlyBeneficialDeviation (s : ∀ i, S i) (A : Finset ι) (t : ∀ i, S i) : Prop :=
  A.Nonempty ∧ ∀ i ∈ A, G.cost i (A.piecewise t s) < G.cost i s

/-- A profile `s` is a **strong equilibrium** if no coalition has a strictly beneficial deviation
from it, that is, no nonempty coalition can jointly deviate so that every member strictly gains
([BabaioffChuangFeldman2007], Exercise 23.6). This is weaker than `IsStrongNash`
(`IsStrongNash.isStrongEquilibrium`), so bounds for strong equilibria apply to strong Nash
equilibria. -/
@[expose] def IsStrongEquilibrium (s : ∀ i, S i) : Prop :=
  ∀ A t, ¬ G.IsStrictlyBeneficialDeviation s A t

variable {G}

/-- A profile `s` is a strong equilibrium iff, whatever joint deviation `t` a nonempty coalition
`A` considers, some member `i ∈ A` does not gain: `cost i s ≤ cost i (A.piecewise t s)`. -/
theorem isStrongEquilibrium_iff {s : ∀ i, S i} :
    G.IsStrongEquilibrium s ↔
      ∀ A : Finset ι, A.Nonempty → ∀ t, ∃ i ∈ A, G.cost i s ≤ G.cost i (A.piecewise t s) := by
  refine ⟨fun h A hA t => ?_, fun h A t ⟨hA, hlt⟩ => ?_⟩
  · by_contra hne
    push Not at hne
    exact h A t ⟨hA, hne⟩
  · obtain ⟨i, hi, hle⟩ := h A hA t
    exact (hle.trans_lt (hlt i hi)).false

/-- In a strong equilibrium `s`, whatever joint deviation `t` a nonempty coalition `A` considers,
some member `i ∈ A` does not gain: `cost i s ≤ cost i (A.piecewise t s)`. -/
theorem IsStrongEquilibrium.exists_cost_le {s : ∀ i, S i} (h : G.IsStrongEquilibrium s)
    {A : Finset ι} (hA : A.Nonempty) (t : ∀ i, S i) :
    ∃ i ∈ A, G.cost i s ≤ G.cost i (A.piecewise t s) :=
  isStrongEquilibrium_iff.1 h A hA t

/-- **A strong Nash equilibrium is a strong equilibrium**: a deviation from which every member of a
nonempty coalition strictly gains is a beneficial deviation. -/
theorem IsStrongNash.isStrongEquilibrium {s : ∀ i, S i} (h : G.IsStrongNash s) :
    G.IsStrongEquilibrium s := by
  rintro A t ⟨⟨i, hi⟩, hlt⟩
  exact h A t ⟨fun j hj => (hlt j hj).le, i, hi, hlt i hi⟩

/-- In a strong Nash equilibrium `s`, whatever joint deviation `t` a nonempty coalition `A`
considers, some member `i ∈ A` does not gain: `cost i s ≤ cost i (A.piecewise t s)`. -/
theorem IsStrongNash.exists_cost_le {s : ∀ i, S i} (h : G.IsStrongNash s) {A : Finset ι}
    (hA : A.Nonempty) (t : ∀ i, S i) : ∃ i ∈ A, G.cost i s ≤ G.cost i (A.piecewise t s) :=
  h.isStrongEquilibrium.exists_cost_le hA t

/-- **A strong equilibrium is a pure Nash equilibrium**: a unilateral deviation is a deviation of
a singleton coalition. -/
theorem IsStrongEquilibrium.isPureNash {s : ∀ i, S i} (h : G.IsStrongEquilibrium s) :
    G.IsPureNash s := by
  intro i a
  obtain ⟨j, hj, hle⟩ := h.exists_cost_le (Finset.singleton_nonempty i) (Function.update s i a)
  rw [Finset.mem_singleton] at hj
  subst hj
  rwa [Finset.piecewise_singleton, Function.update_self] at hle

/-- **A strong Nash equilibrium is a pure Nash equilibrium**: a unilateral deviation is a
deviation of a singleton coalition ([Roughgarden2013CS364A], Lecture #15, Section 3). -/
theorem IsStrongNash.isPureNash {s : ∀ i, S i} (h : G.IsStrongNash s) : G.IsPureNash s :=
  h.isStrongEquilibrium.isPureNash

/-- **A strong Nash equilibrium is Pareto optimal** (Pareto efficient): no profile `t` is weakly
better for every player and strictly better for some player. This is the deviation of the grand
coalition. -/
theorem IsStrongNash.not_pareto [Finite ι] {s : ∀ i, S i} (h : G.IsStrongNash s)
    (t : ∀ i, S i) : ¬ ((∀ i, G.cost i t ≤ G.cost i s) ∧ ∃ i, G.cost i t < G.cost i s) := by
  have := Fintype.ofFinite ι
  rintro ⟨hle, i, hlt⟩
  refine h Finset.univ t ⟨fun j _ => ?_, i, Finset.mem_univ i, ?_⟩
  · rw [Finset.piecewise_univ]
    exact hle j
  · rw [Finset.piecewise_univ]
    exact hlt

end Cslib.GameTheory.CostGame
