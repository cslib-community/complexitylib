/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Potential
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

/-!
# The potential function method and the price of stability

The **price of stability** of a cost-minimization game is the ratio between the social cost of its
best pure Nash equilibrium and the optimal social cost ([RoughgardenTardos2007], Section 17.1.3).
A bound `ρ` on it says that *some* pure Nash equilibrium `s` satisfies
`socialCost s ≤ ρ * socialCost s'` for every profile `s'`; a bound on the price of anarchy, as in
`Cslib.GameTheory.CostGame.IsSmooth.socialCost_le_of_isPureNash`, says this of *every* pure Nash
equilibrium. As for the price of anarchy, we state these bounds as inequalities rather than
defining the ratio.

The **potential function method** ([TardosWexler2007], Theorem 19.13) bounds the price of stability
of a potential game whose potential `Φ` approximates the social cost:
if `socialCost s ≤ A * Φ s` and `Φ s ≤ B * socialCost s` for every profile `s`, then a global
minimizer of `Φ` is a pure Nash equilibrium of social cost at most `A * B` times the optimum. The
same chain of inequalities, run along an improvement path instead of at a global minimizer, shows
that better-response dynamics started at any profile `s₀` reach a pure Nash equilibrium of social
cost at most `A * B * socialCost s₀`.

The source states the hypothesis as `cost(S) / A ≤ Φ(S) ≤ B · cost(S)` with `A, B > 0`; we write
the first inequality as `socialCost s ≤ A * Φ s` and need only `0 ≤ A`. The source takes `Φ` to be
an exact potential; a generalized ordinal potential suffices, and every exact potential is one
(`Cslib.GameTheory.CostGame.IsExactPotential.isGeneralizedOrdinalPotential`).

## Main results

* `IsGeneralizedOrdinalPotential.exists_reflTransGen_isPureNash_socialCost_le` (in
  `Cslib.GameTheory.CostGame`): better-response dynamics started at `s₀` reach a pure Nash
  equilibrium of social cost at most `A * B * socialCost s₀`.
* `Cslib.GameTheory.CostGame.IsGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le`
  ([TardosWexler2007], Theorem 19.13): **the price of stability is at most `A * B`**.

## References

* [RoughgardenTardos2007]
* [TardosWexler2007]
-/

public section

namespace Cslib.GameTheory.CostGame

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] {G : CostGame ι S}

/-- **The potential function method along better-response dynamics**: if a generalized ordinal
potential `Φ` satisfies `socialCost s ≤ A * Φ s` and `Φ s ≤ B * socialCost s` for every profile
`s`, with `0 ≤ A`, and there are finitely many profiles, then better-response dynamics started at
any profile `s₀` reach a pure Nash equilibrium `t` with `socialCost t ≤ A * B * socialCost s₀`.

Started at a socially optimal profile, this gives the price-of-stability bound of
`exists_isPureNash_socialCost_le` for an equilibrium reachable from the optimum. -/
theorem IsGeneralizedOrdinalPotential.exists_reflTransGen_isPureNash_socialCost_le
    [Finite (∀ i, S i)] {Φ : (∀ i, S i) → ℝ} (h : G.IsGeneralizedOrdinalPotential Φ) {A B : ℝ}
    (hA : 0 ≤ A) (hlow : ∀ s, G.socialCost s ≤ A * Φ s) (hup : ∀ s, Φ s ≤ B * G.socialCost s)
    (s₀ : ∀ i, S i) :
    ∃ t, Relation.ReflTransGen (flip G.Improves) s₀ t ∧ G.IsPureNash t ∧
      G.socialCost t ≤ A * B * G.socialCost s₀ := by
  obtain ⟨t, hpath, ht⟩ := h.hasFIP.exists_reflTransGen_isPureNash s₀
  refine ⟨t, hpath, ht, ?_⟩
  calc G.socialCost t ≤ A * Φ t := hlow t
    _ ≤ A * Φ s₀ := mul_le_mul_of_nonneg_left (h.le_of_reflTransGen hpath) hA
    _ ≤ A * (B * G.socialCost s₀) := mul_le_mul_of_nonneg_left (hup s₀) hA
    _ = A * B * G.socialCost s₀ := (mul_assoc _ _ _).symm

/-- **The potential function method** ([TardosWexler2007], Theorem 19.13): if a game with finitely
many (and at least one) profiles has a generalized ordinal potential `Φ` with
`socialCost s ≤ A * Φ s` and `Φ s ≤ B * socialCost s` for every profile `s`, where `0 ≤ A`, then
some pure Nash equilibrium `s` (a global minimizer of `Φ`) satisfies
`socialCost s ≤ A * B * socialCost s'` for every profile `s'`. That is, the price of stability is at
most `A * B`.

The source writes the hypothesis as `cost(S) / A ≤ Φ(S) ≤ B · cost(S)` with `A, B > 0` and takes
`Φ` to be an exact potential. -/
theorem IsGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le [Finite (∀ i, S i)]
    [Nonempty (∀ i, S i)] {Φ : (∀ i, S i) → ℝ} (h : G.IsGeneralizedOrdinalPotential Φ) {A B : ℝ}
    (hA : 0 ≤ A) (hlow : ∀ s, G.socialCost s ≤ A * Φ s) (hup : ∀ s, Φ s ≤ B * G.socialCost s) :
    ∃ s, G.IsPureNash s ∧ ∀ s', G.socialCost s ≤ A * B * G.socialCost s' := by
  obtain ⟨s, hs⟩ := Finite.exists_min Φ
  refine ⟨s, h.isPureNash_of_forall_le hs, fun s' => ?_⟩
  calc G.socialCost s ≤ A * Φ s := hlow s
    _ ≤ A * Φ s' := mul_le_mul_of_nonneg_left (hs s') hA
    _ ≤ A * (B * G.socialCost s') := mul_le_mul_of_nonneg_left (hup s') hA
    _ = A * B * G.socialCost s' := (mul_assoc _ _ _).symm

end Cslib.GameTheory.CostGame
