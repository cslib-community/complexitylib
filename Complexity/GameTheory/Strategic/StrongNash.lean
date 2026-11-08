/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Strategic.Basic
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

Singleton coalitions are unilateral deviations, so every strong Nash equilibrium is a pure Nash
equilibrium (`IsStrongNash.isPureNash`). The grand coalition shows that a strong Nash equilibrium
is weakly Pareto optimal: no profile makes every player weakly and some player strictly better
off (`IsStrongNash.not_pareto`). The basic tool for bounding the cost of strong Nash equilibria is
`IsStrongNash.exists_cost_le`: whatever joint deviation a nonempty coalition considers, one of its
members does not gain.

## Main definitions

* `Cslib.GameTheory.CostGame.IsBeneficialDeviation`: the coalition `A` gains by deviating to the
  strategies of `t`.
* `Cslib.GameTheory.CostGame.IsStrongNash`: no coalition has a beneficial deviation.

## Main results

* `Cslib.GameTheory.CostGame.IsStrongNash.exists_cost_le`: in a strong Nash equilibrium, every
  joint deviation of a nonempty coalition leaves some member no better off.
* `Cslib.GameTheory.CostGame.IsStrongNash.isPureNash`: a strong Nash equilibrium is a pure Nash
  equilibrium.
* `Cslib.GameTheory.CostGame.IsStrongNash.not_pareto`: a strong Nash equilibrium is weakly Pareto
  optimal.

## References

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
it ([Roughgarden2013CS364A], Lecture #15, Definition 3.1(b)). -/
@[expose] def IsStrongNash (s : ∀ i, S i) : Prop :=
  ∀ A t, ¬ G.IsBeneficialDeviation s A t

variable {G}

/-- In a strong Nash equilibrium `s`, whatever joint deviation `t` a nonempty coalition `A`
considers, some member `i ∈ A` does not gain: `cost i s ≤ cost i (A.piecewise t s)`. -/
theorem IsStrongNash.exists_cost_le {s : ∀ i, S i} (h : G.IsStrongNash s) {A : Finset ι}
    (hA : A.Nonempty) (t : ∀ i, S i) : ∃ i ∈ A, G.cost i s ≤ G.cost i (A.piecewise t s) := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hA
  exact h A t ⟨fun j hj => (hne j hj).le, i, hi, hne i hi⟩

/-- **A strong Nash equilibrium is a pure Nash equilibrium**: a unilateral deviation is a
deviation of a singleton coalition ([Roughgarden2013CS364A], Lecture #15, Section 3). -/
theorem IsStrongNash.isPureNash {s : ∀ i, S i} (h : G.IsStrongNash s) : G.IsPureNash s := by
  intro i a
  obtain ⟨j, hj, hle⟩ := h.exists_cost_le (Finset.singleton_nonempty i) (Function.update s i a)
  rw [Finset.mem_singleton] at hj
  subst hj
  rwa [Finset.piecewise_singleton, Function.update_self] at hle

/-- **A strong Nash equilibrium is weakly Pareto optimal**: no profile `t` is weakly better for
every player and strictly better for some player. This is the deviation of the grand
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
