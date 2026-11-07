/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Minimax
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# The value of a finite zero-sum game

In the finite zero-sum game with loss matrix `M : I → J → ℝ`, the row player picks `i`, the column
player picks `j`, and the row player pays `M i j` to the column player. A real number `v` is the
*value* of the game (`IsMinimaxValue M v`) if the row player has a mixed strategy `p` paying at
most `v` against every column and the column player has a mixed strategy `q` collecting at least
`v` against every row. By von Neumann's minimax theorem [vonNeumann1928] every game with finitely
many rows and columns has a value (`exists_isMinimaxValue`), and it is unique
(`IsMinimaxValue.unique`): `min_p max_j ∑ i, p i M i j = max_q min_i ∑ j, q j M i j = v`.

Existence is derived from the minimax theorem in the form
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le` (from Sion's theorem). Let
`v` be the supremum of the guarantees of the column player's mixed strategies. Some row pays at
most `v` against each mixed column strategy, so some mixed row strategy pays at most `v` against
every column. Applied to `-Mᵀ`, the same theorem gives a mixed column strategy collecting at least
`v`.

## Main definitions

* `Cslib.Probability.IsMinimaxValue`: `v` is the value of a finite zero-sum game.

## Main results

* `Cslib.Probability.exists_isMinimaxValue`: every finite zero-sum game has a value.
* `Cslib.Probability.IsMinimaxValue.unique`: the value is unique.
* `Cslib.Probability.IsMinimaxValue.exists_le`, `Cslib.Probability.IsMinimaxValue.exists_ge`:
  against any mixed strategy, the opponent has a pure strategy doing at least as well as the value.

## References

* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

@[expose] public section

namespace Cslib.Probability

open Finset Convexity

variable {I J : Type*} [Fintype I] [Fintype J]

/-- `v` is the *value* of the finite zero-sum game with loss matrix `M` (the row player pays
`M i j`): some mixed row strategy pays at most `v` against every column, and some mixed column
strategy collects at least `v` against every row. -/
def IsMinimaxValue (M : I → J → ℝ) (v : ℝ) : Prop :=
  (∃ p : StdSimplex ℝ I, ∀ j, ∑ i, p.weights i * M i j ≤ v) ∧
    ∃ q : StdSimplex ℝ J, ∀ i, v ≤ ∑ j, q.weights j * M i j

/-- If `p` pays at most `c` against every column, it pays at most `c` against every mixed column
strategy. -/
private theorem sum_mul_sum_le {M : I → J → ℝ} {c : ℝ} {p : I → ℝ} (q : J → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (hp : ∀ j, ∑ i, p i * M i j ≤ c) :
    ∑ i, p i * ∑ j, q j * M i j ≤ c := by
  calc ∑ i, p i * ∑ j, q j * M i j = ∑ j, q j * ∑ i, p i * M i j := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring
    _ ≤ ∑ j, q j * c := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) (hq0 j)
    _ = c := by rw [← sum_mul, hq1, one_mul]

/-- If `q` collects at least `c` against every row, it collects at least `c` against every mixed
row strategy. -/
private theorem le_sum_mul_sum {M : I → J → ℝ} {c : ℝ} (p : I → ℝ) {q : J → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hq : ∀ i, c ≤ ∑ j, q j * M i j) :
    c ≤ ∑ i, p i * ∑ j, q j * M i j :=
  calc c = ∑ i, p i * c := by rw [← sum_mul, hp1, one_mul]
    _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq i) (hp0 i)

/-- Some column does at least as well against `p` as the mixed column strategy `q`. -/
private theorem exists_sum_mul_sum_le [Nonempty J] (M : I → J → ℝ) (p : I → ℝ) {q : J → ℝ}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) :
    ∃ j, ∑ i, p i * ∑ j', q j' * M i j' ≤ ∑ i, p i * M i j := by
  obtain ⟨j, hj⟩ := Finite.exists_max fun j => ∑ i, p i * M i j
  exact ⟨j, sum_mul_sum_le q hq0 hq1 hj⟩

/-- The value of a game is unique. -/
theorem IsMinimaxValue.unique {M : I → J → ℝ} {v w : ℝ} (hv : IsMinimaxValue M v)
    (hw : IsMinimaxValue M w) : v = w := by
  obtain ⟨⟨p, hp⟩, q, hq⟩ := hv
  obtain ⟨⟨p', hp'⟩, q', hq'⟩ := hw
  have h₁ := sum_mul_sum_le _ q'.weights_nonneg q'.total_of_fintype hp
  have h₂ := le_sum_mul_sum _ p.weights_nonneg p.total_of_fintype hq'
  have h₃ := sum_mul_sum_le _ q.weights_nonneg q.total_of_fintype hp'
  have h₄ := le_sum_mul_sum _ p'.weights_nonneg p'.total_of_fintype hq
  linarith

/-- **Every finite zero-sum game has a value** [vonNeumann1928]. -/
theorem exists_isMinimaxValue [Nonempty I] [Nonempty J] (M : I → J → ℝ) :
    ∃ v, IsMinimaxValue M v := by
  classical
  -- the guarantees of the column player's mixed strategies
  set S : Set ℝ := {c | ∃ q : StdSimplex ℝ J, ∀ i, c ≤ ∑ j, q.weights j * M i j} with hS
  have key : ∀ (p : I → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) → ∀ c ∈ S,
      ∃ j, c ≤ ∑ i, p i * M i j := by
    intro p hp0 hp1 c ⟨q, hq⟩
    obtain ⟨j, hj⟩ := exists_sum_mul_sum_le M p q.weights_nonneg q.total_of_fintype
    exact ⟨j, (le_sum_mul_sum p hp0 hp1 hq).trans hj⟩
  have hne : S.Nonempty := by
    let q : StdSimplex ℝ J := .single (Classical.arbitrary J)
    obtain ⟨i, hi⟩ := Finite.exists_min fun i => ∑ j, q.weights j * M i j
    exact ⟨_, q, hi⟩
  set p₀ : StdSimplex ℝ I := .single (Classical.arbitrary I)
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => ∑ i, p₀.weights i * M i j
  have hbdd : BddAbove S := ⟨∑ i, p₀.weights i * M i j₀, fun c hc => by
    obtain ⟨j, hj⟩ := key _ p₀.weights_nonneg p₀.total_of_fintype c hc
    exact hj.trans (hj₀ j)⟩
  refine ⟨sSup S, ?_, ?_⟩
  · refine StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le M fun q => ?_
    obtain ⟨i, hi⟩ := Finite.exists_min fun i => ∑ j, q.weights j * M i j
    exact ⟨i, le_csSup hbdd ⟨q, hi⟩⟩
  · obtain ⟨q, hq⟩ := StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le
      (fun j i => -M i j) (c := -sSup S) fun p => by
        obtain ⟨j, hj⟩ := Finite.exists_max fun j => ∑ i, p.weights i * M i j
        refine ⟨j, ?_⟩
        have : sSup S ≤ ∑ i, p.weights i * M i j := csSup_le hne fun c hc => by
          obtain ⟨j', hj'⟩ := key _ p.weights_nonneg p.total_of_fintype c hc
          exact hj'.trans (hj j')
        simp only [mul_neg, sum_neg_distrib]
        linarith
    refine ⟨q, fun i => ?_⟩
    have := hq i
    simp only [mul_neg, sum_neg_distrib] at this
    linarith

/-- Against any mixed row strategy `p`, some column collects at least the value. -/
theorem IsMinimaxValue.exists_le {M : I → J → ℝ} {v : ℝ} (hv : IsMinimaxValue M v) {p : I → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) : ∃ j, v ≤ ∑ i, p i * M i j := by
  obtain ⟨-, q, hq⟩ := hv
  have := q.nonempty
  obtain ⟨j, hj⟩ := exists_sum_mul_sum_le M p q.weights_nonneg q.total_of_fintype
  exact ⟨j, (le_sum_mul_sum p hp0 hp1 hq).trans hj⟩

/-- Against any mixed column strategy `q`, some row pays at most the value. -/
theorem IsMinimaxValue.exists_ge {M : I → J → ℝ} {v : ℝ} (hv : IsMinimaxValue M v) {q : J → ℝ}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) : ∃ i, ∑ j, q j * M i j ≤ v := by
  obtain ⟨⟨p, hp⟩, -⟩ := hv
  have := p.nonempty
  obtain ⟨i, hi⟩ := Finite.exists_min fun i => ∑ j, q j * M i j
  refine ⟨i, ?_⟩
  calc ∑ j, q j * M i j = ∑ i', p.weights i' * ∑ j, q j * M i j := by
        rw [← sum_mul, p.total_of_fintype, one_mul]
    _ ≤ ∑ i', p.weights i' * ∑ j, q j * M i' j :=
        sum_le_sum fun i' _ => mul_le_mul_of_nonneg_left (hi i') (p.weights_nonneg i')
    _ ≤ v := sum_mul_sum_le q hq0 hq1 hp

end Cslib.Probability
