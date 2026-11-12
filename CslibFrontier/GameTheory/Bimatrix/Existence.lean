/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nash's theorem for bimatrix games

Every bimatrix game with nonempty strategy sets has a Nash equilibrium
(`Cslib.GameTheory.BimatrixGame.exists_isNash`), with no nondegeneracy assumption. This is the
two-player case of Nash's theorem ([Nash1951], Theorem 1).

The proof views the game as a two-player cost-minimization game indexed by `Bool`, with costs the
negated payoffs, and applies `Cslib.GameTheory.CostGame.exists_isMixedNash`. The strategy sets are
lifted to a common universe. Against mixed strategies, the expected cost vector of each player is
the negated vector of expected payoffs of its pure strategies, so a mixed Nash equilibrium of the
cost game is a pair of mutual best responses.

For nondegenerate games, `Cslib.GameTheory.BimatrixGame.IsNondegenerate.odd_ncard_isNash` gives
the sharper parity statement of Lemke and Howson.

## Main results

* `Cslib.GameTheory.BimatrixGame.exists_isNash`: **Nash's theorem** for bimatrix games.

## References

* [J. Nash, *Non-Cooperative Games*][Nash1951]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

open Finset Function Matrix

universe u v

variable {M : Type u} {N : Type v} [Fintype M] [Fintype N]

/-- The strategy set of player `false` (the row player) and player `true` (the column player),
lifted to a common universe. -/
private abbrev Strat (M : Type u) (N : Type v) (b : Bool) : Type (max u v) :=
  cond b (ULift.{u} N) (ULift.{v} M)

private instance instFintypeStrat (b : Bool) : Fintype (Strat M N b) :=
  match b with
  | true => inferInstanceAs (Fintype (ULift.{u} N))
  | false => inferInstanceAs (Fintype (ULift.{v} M))

private instance instNonemptyStrat [Nonempty M] [Nonempty N] (b : Bool) :
    Nonempty (Strat M N b) :=
  match b with
  | true => inferInstanceAs (Nonempty (ULift.{u} N))
  | false => inferInstanceAs (Nonempty (ULift.{v} M))

/-- A bimatrix game as a cost-minimization game: the costs are the negated payoffs. -/
private def toCostGame (G : BimatrixGame M N) : CostGame Bool (Strat M N) where
  cost
    | false => fun s => -G.A (ULift.down (s false)) (ULift.down (s true))
    | true => fun s => -G.B (ULift.down (s false)) (ULift.down (s true))

private theorem sum_strat_false (f : Strat M N false → ℝ) :
    ∑ a, f a = ∑ i : M, f (ULift.up i) :=
  Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl

private theorem sum_strat_true (f : Strat M N true → ℝ) :
    ∑ a, f a = ∑ j : N, f (ULift.up j) :=
  Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl

/-- The expected cost vector of the row player is the negated vector of its expected payoffs. -/
private theorem deviationCost_false (G : BimatrixGame M N) (p : ∀ b, Strat M N b → ℝ)
    (hp : ∑ a, p false a = 1) (i : M) :
    G.toCostGame.deviationCost p false (ULift.up i)
      = -(G.A *ᵥ fun j => p true (ULift.up j)) i := by
  have hp' : ∀ b, b ≠ true → ∑ a, p b a = 1 := by
    rintro (_ | _) hb
    exacts [hp, absurd rfl hb]
  rw [CostGame.deviationCost_def]
  calc ∑ s, productWeight p s * G.toCostGame.cost false (update s false (ULift.up i))
      = ∑ s, productWeight p s * (fun c : Strat M N true => -G.A i (ULift.down c)) (s true) :=
        sum_congr rfl fun s _ => by
          simp only [toCostGame, update_self, update_of_ne (show true ≠ false by decide)]
    _ = -(G.A *ᵥ fun j => p true (ULift.up j)) i := by
        rw [sum_productWeight_mul_apply hp' fun c : Strat M N true => -G.A i (ULift.down c),
          sum_strat_true]
        simp only [mulVec, dotProduct, ← sum_neg_distrib, mul_neg, mul_comm]

/-- The expected cost vector of the column player is the negated vector of its expected
payoffs. -/
private theorem deviationCost_true (G : BimatrixGame M N) (p : ∀ b, Strat M N b → ℝ)
    (hp : ∑ a, p true a = 1) (j : N) :
    G.toCostGame.deviationCost p true (ULift.up j)
      = -((fun i => p false (ULift.up i)) ᵥ* G.B) j := by
  have hp' : ∀ b, b ≠ false → ∑ a, p b a = 1 := by
    rintro (_ | _) hb
    exacts [absurd rfl hb, hp]
  rw [CostGame.deviationCost_def]
  calc ∑ s, productWeight p s * G.toCostGame.cost true (update s true (ULift.up j))
      = ∑ s, productWeight p s * (fun c : Strat M N false => -G.B (ULift.down c) j) (s false) :=
        sum_congr rfl fun s _ => by
          simp only [toCostGame, update_self, update_of_ne (show false ≠ true by decide)]
    _ = -((fun i => p false (ULift.up i)) ᵥ* G.B) j := by
        rw [sum_productWeight_mul_apply hp' fun c : Strat M N false => -G.B (ULift.down c) j,
          sum_strat_false]
        simp only [vecMul, dotProduct, ← sum_neg_distrib, mul_neg]

/-- **Nash's theorem** for bimatrix games ([Nash1951], Theorem 1): every bimatrix game with
nonempty strategy sets has a Nash equilibrium. -/
theorem exists_isNash [Nonempty M] [Nonempty N] (G : BimatrixGame M N) :
    ∃ x y, G.IsNash x y := by
  obtain ⟨p, hp⟩ := G.toCostGame.exists_isMixedNash
  have h0 : ∑ i : M, p false (ULift.up i) = 1 :=
    (sum_strat_false (p false)).symm.trans (hp.1 false).sum_eq_one
  have h1 : ∑ j : N, p true (ULift.up j) = 1 :=
    (sum_strat_true (p true)).symm.trans (hp.1 true).sum_eq_one
  refine ⟨fun i => p false (ULift.up i), fun j => p true (ULift.up j), isNash_iff.2 ⟨?_, ?_⟩⟩
  · refine isBestResponse₁_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun i => (hp.1 false).nonneg _, h0⟩,
      fun i hi => isPureBestResponse₁_iff.2 fun i' => ?_⟩
    have h := hp.2 false (ULift.up i')
    rw [← hp.deviationCost_eq_of_pos false hi] at h
    simp only [deviationCost_false G p (hp.1 false).sum_eq_one] at h
    linarith
  · refine isBestResponse₂_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun j => (hp.1 true).nonneg _, h1⟩,
      fun j hj => isPureBestResponse₂_iff.2 fun j' => ?_⟩
    have h := hp.2 true (ULift.up j')
    rw [← hp.deviationCost_eq_of_pos true hj] at h
    simp only [deviationCost_true G p (hp.1 true).sum_eq_one] at h
    linarith

end Cslib.GameTheory.BimatrixGame
