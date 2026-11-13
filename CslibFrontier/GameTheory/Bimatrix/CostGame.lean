/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Bimatrix games as cost games

A bimatrix game is a two-player game in strategic form, so it is an instance of the general
`Cslib.GameTheory.CostGame`: the players are indexed by `Bool`, with `false` the row player and
`true` the column player, each minimizes its negated payoff, and the strategy sets are lifted to a
common universe (`BimatrixGame.PureStrategy`). `BimatrixGame.toCostGame` is this cost game, and
`BimatrixGame.profile x y` is the mixed profile in which the row player plays `x` and the column
player `y`.

Against mixed strategies, the expected cost vector of each player is the negated vector of expected
payoffs of its pure strategies (`deviationCost_toCostGame_row`,
`deviationCost_toCostGame_column`), and its expected cost is its negated payoff. Consequently a
pair of mixed strategies is a Nash equilibrium of the bimatrix game exactly when it is a mixed Nash
equilibrium of the cost game (`isNash_iff_isMixedNash`), so results about mixed Nash equilibria
of cost games, such as `CostGame.exists_isMixedNash` and
`CostGame.IsMixedNash.isCorrelatedEquilibrium`, apply to bimatrix games.

## Main definitions

* `Cslib.GameTheory.BimatrixGame.PureStrategy`: the pure strategies of the row player (`false`) and
  the column player (`true`), lifted to a common universe.
* `Cslib.GameTheory.BimatrixGame.toCostGame`: a bimatrix game as a cost game on `Bool`.
* `Cslib.GameTheory.BimatrixGame.profile`: the mixed profile of a pair of mixed strategies.

## Main results

* `Cslib.GameTheory.BimatrixGame.isNash_iff_isMixedNash`: Nash equilibria of the bimatrix game
  are the mixed Nash equilibria of its cost game.
* `Cslib.GameTheory.BimatrixGame.eq_profile`: every mixed profile of the cost game is a `profile`.

## References

* [J. Nash, *Non-Cooperative Games*][Nash1951]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

open Finset Function Matrix

universe u v

variable {M : Type u} {N : Type v}

/-- The pure strategies of player `false` (the row player, `M`) and player `true` (the column
player, `N`), lifted to a common universe. -/
abbrev PureStrategy (M : Type u) (N : Type v) (b : Bool) : Type (max u v) :=
  cond b (ULift.{u} N) (ULift.{v} M)

instance instFintypePureStrategy [Fintype M] [Fintype N] (b : Bool) :
    Fintype (PureStrategy M N b) :=
  match b with
  | true => inferInstanceAs (Fintype (ULift.{u} N))
  | false => inferInstanceAs (Fintype (ULift.{v} M))

instance instNonemptyPureStrategy [Nonempty M] [Nonempty N] (b : Bool) :
    Nonempty (PureStrategy M N b) :=
  match b with
  | true => inferInstanceAs (Nonempty (ULift.{u} N))
  | false => inferInstanceAs (Nonempty (ULift.{v} M))

/-- A bimatrix game as a cost-minimization game on the players `Bool`: the row player `false` and
the column player `true` pay their negated payoffs. -/
@[expose] def toCostGame (G : BimatrixGame M N) : CostGame Bool (PureStrategy M N) where
  cost
    | false => fun s => -G.A (ULift.down (s false)) (ULift.down (s true))
    | true => fun s => -G.B (ULift.down (s false)) (ULift.down (s true))

/-- The mixed profile of the cost game in which the row player plays `x` and the column player
plays `y`. -/
@[expose] def profile (x : M → ℝ) (y : N → ℝ) : ∀ b, PureStrategy M N b → ℝ
  | false => fun a => x a.down
  | true => fun a => y a.down

@[simp]
theorem profile_false (x : M → ℝ) (y : N → ℝ) (i : M) : profile x y false (ULift.up i) = x i :=
  rfl

@[simp]
theorem profile_true (x : M → ℝ) (y : N → ℝ) (j : N) : profile x y true (ULift.up j) = y j :=
  rfl

/-- Every mixed profile of the cost game is the profile of its row and column strategies. -/
theorem eq_profile (p : ∀ b, PureStrategy M N b → ℝ) :
    p = profile (fun i => p false (ULift.up i)) (fun j => p true (ULift.up j)) := by
  funext b a
  cases b <;> rfl

variable [Fintype M] [Fintype N]

private theorem sum_pureStrategy_false (f : PureStrategy M N false → ℝ) :
    ∑ a, f a = ∑ i : M, f (ULift.up i) :=
  Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl

private theorem sum_pureStrategy_true (f : PureStrategy M N true → ℝ) :
    ∑ a, f a = ∑ j : N, f (ULift.up j) :=
  Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl

/-- The row player's component of `profile x y` is a mixed strategy exactly when `x` is. -/
theorem isMixedStrategy_profile_false_iff {x : M → ℝ} {y : N → ℝ} :
    IsMixedStrategy (profile x y false) ↔ IsMixedStrategy x := by
  rw [isMixedStrategy_iff, isMixedStrategy_iff, sum_pureStrategy_false]
  exact and_congr ⟨fun h i => h (ULift.up i), fun h a => h (ULift.down a)⟩ Iff.rfl

/-- The column player's component of `profile x y` is a mixed strategy exactly when `y` is. -/
theorem isMixedStrategy_profile_true_iff {x : M → ℝ} {y : N → ℝ} :
    IsMixedStrategy (profile x y true) ↔ IsMixedStrategy y := by
  rw [isMixedStrategy_iff, isMixedStrategy_iff, sum_pureStrategy_true]
  exact and_congr ⟨fun h j => h (ULift.up j), fun h a => h (ULift.down a)⟩ Iff.rfl

/-- If `x` is a probability vector, the expected cost of the row player's pure strategy `i` against
`y` is its negated expected payoff `-(A y)ᵢ`. -/
theorem deviationCost_toCostGame_row (G : BimatrixGame M N) {x : M → ℝ} (y : N → ℝ)
    (hx : ∑ i, x i = 1) (i : M) :
    G.toCostGame.deviationCost (profile x y) false (ULift.up i) = -(G.A *ᵥ y) i := by
  have hp : ∀ b, b ≠ true → ∑ a, profile x y b a = 1 := by
    rintro (_ | _) hb
    · rw [sum_pureStrategy_false]
      exact hx
    · exact absurd rfl hb
  rw [CostGame.deviationCost_def]
  calc ∑ s, productWeight (profile x y) s * G.toCostGame.cost false (update s false (ULift.up i))
      = ∑ s, productWeight (profile x y) s *
          (fun c : PureStrategy M N true => -G.A i (ULift.down c)) (s true) :=
        sum_congr rfl fun s _ => by
          simp only [toCostGame, update_self, update_of_ne (show true ≠ false by decide)]
    _ = -(G.A *ᵥ y) i := by
        rw [sum_productWeight_mul_apply hp fun c : PureStrategy M N true => -G.A i (ULift.down c),
          sum_pureStrategy_true]
        simp only [profile_true, mulVec, dotProduct, ← sum_neg_distrib, mul_neg, mul_comm]

/-- If `y` is a probability vector, the expected cost of the column player's pure strategy `j`
against `x` is its negated expected payoff `-(x B)ⱼ`. -/
theorem deviationCost_toCostGame_column (G : BimatrixGame M N) (x : M → ℝ) {y : N → ℝ}
    (hy : ∑ j, y j = 1) (j : N) :
    G.toCostGame.deviationCost (profile x y) true (ULift.up j) = -(x ᵥ* G.B) j := by
  have hp : ∀ b, b ≠ false → ∑ a, profile x y b a = 1 := by
    rintro (_ | _) hb
    · exact absurd rfl hb
    · rw [sum_pureStrategy_true]
      exact hy
  rw [CostGame.deviationCost_def]
  calc ∑ s, productWeight (profile x y) s * G.toCostGame.cost true (update s true (ULift.up j))
      = ∑ s, productWeight (profile x y) s *
          (fun c : PureStrategy M N false => -G.B (ULift.down c) j) (s false) :=
        sum_congr rfl fun s _ => by
          simp only [toCostGame, update_self, update_of_ne (show false ≠ true by decide)]
    _ = -(x ᵥ* G.B) j := by
        rw [sum_productWeight_mul_apply hp fun c : PureStrategy M N false => -G.B (ULift.down c) j,
          sum_pureStrategy_false]
        simp only [profile_false, vecMul, dotProduct, ← sum_neg_distrib, mul_neg]

/-- The row player's expected cost under `profile x y` is its negated payoff. -/
theorem expectedCost_toCostGame_false (G : BimatrixGame M N) {x : M → ℝ} (y : N → ℝ)
    (hx : ∑ i, x i = 1) : G.toCostGame.expectedCost (profile x y) false = -G.payoff₁ x y := by
  have hx' : ∑ a, profile x y false a = 1 := by rw [sum_pureStrategy_false]; exact hx
  rw [← G.toCostGame.sum_mul_deviationCost_eq_expectedCost _ hx', sum_pureStrategy_false]
  simp only [profile_false, deviationCost_toCostGame_row G y hx, payoff₁_eq_dotProduct,
    dotProduct, mul_neg, sum_neg_distrib]

/-- The column player's expected cost under `profile x y` is its negated payoff. -/
theorem expectedCost_toCostGame_true (G : BimatrixGame M N) (x : M → ℝ) {y : N → ℝ}
    (hy : ∑ j, y j = 1) : G.toCostGame.expectedCost (profile x y) true = -G.payoff₂ x y := by
  have hy' : ∑ a, profile x y true a = 1 := by rw [sum_pureStrategy_true]; exact hy
  rw [← G.toCostGame.sum_mul_deviationCost_eq_expectedCost _ hy', sum_pureStrategy_true]
  simp only [profile_true, deviationCost_toCostGame_column G x hy, payoff₂_eq_dotProduct,
    dotProduct, mul_neg, sum_neg_distrib]

/-- **Bimatrix Nash equilibria are mixed Nash equilibria of the cost game**: `(x, y)` is a Nash
equilibrium of `G` exactly when `profile x y` is a mixed Nash equilibrium of `G.toCostGame`. -/
theorem isNash_iff_isMixedNash {G : BimatrixGame M N} {x : M → ℝ} {y : N → ℝ} :
    G.IsNash x y ↔ G.toCostGame.IsMixedNash (profile x y) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
    have hx := h₁.isMixedStrategy
    have hy := h₂.isMixedStrategy
    refine ⟨fun b => ?_, fun b a => ?_⟩
    · cases b
      exacts [isMixedStrategy_profile_false_iff.2 hx, isMixedStrategy_profile_true_iff.2 hy]
    · cases b
      · obtain ⟨i⟩ := a
        rw [expectedCost_toCostGame_false G y hx.sum_eq_one,
          deviationCost_toCostGame_row G y hx.sum_eq_one i]
        exact neg_le_neg (h₁.le_payoff₁ i)
      · obtain ⟨j⟩ := a
        rw [expectedCost_toCostGame_true G x hy.sum_eq_one,
          deviationCost_toCostGame_column G x hy.sum_eq_one j]
        exact neg_le_neg (h₂.le_payoff₂ j)
  · intro h
    have hx := isMixedStrategy_profile_false_iff.1 (h.1 false)
    have hy := isMixedStrategy_profile_true_iff.1 (h.1 true)
    refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨hx, fun i hi => isPureBestResponse₁_iff.2
      fun i' => ?_⟩, isBestResponse₂_iff.2 ⟨hy, fun j hj => isPureBestResponse₂_iff.2
      fun j' => ?_⟩⟩
    · have hle := h.2 false (ULift.up i')
      rw [← h.deviationCost_eq_of_pos false (a := ULift.up i) hi] at hle
      simp only [deviationCost_toCostGame_row G y hx.sum_eq_one] at hle
      linarith
    · have hle := h.2 true (ULift.up j')
      rw [← h.deviationCost_eq_of_pos true (a := ULift.up j) hj] at hle
      simp only [deviationCost_toCostGame_column G x hy.sum_eq_one] at hle
      linarith

end Cslib.GameTheory.BimatrixGame
