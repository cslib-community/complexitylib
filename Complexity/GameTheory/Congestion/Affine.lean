/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Congestion.Basic
public import Complexity.GameTheory.Strategic.Smooth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The price of anarchy of congestion games with affine latencies

An atomic congestion game has **affine latencies** if every latency has the form
`latency e k = a e * k + b e` with `a e, b e ≥ 0`. Such games are `(5/3, 1/3)`-smooth
([Roughgarden2015], Example 2.5), by the inequality `y (z + 1) ≤ 5/3 y² + 1/3 z²` for natural
numbers `y` and `z` of Christodoulou and Koutsoupias [ChristodoulouKoutsoupias2005], as cited in
[Roughgarden2015], Example 2.5. By the smoothness bound `λ / (1 - μ) = 5/2`, the social cost of
every pure Nash equilibrium, and the expected social cost of every coarse correlated equilibrium,
is at most `5/2` times the social cost of every profile [AwerbuchAzarEpstein2005]
[ChristodoulouKoutsoupias2005]. The bound is attained: `exists_socialCost_eq_five_halves_mul`
gives a three-player game with latencies `latency e k = k` and a pure Nash equilibrium whose social
cost is exactly `5/2` times that of another profile.

## Main definitions

* `Cslib.GameTheory.CongestionGame.HasAffineLatencies`: nonnegative affine latencies.

## Main results

* `Cslib.GameTheory.CongestionGame.HasAffineLatencies.monotone_latency`: nonnegative affine
  latencies are nondecreasing.
* `Cslib.GameTheory.CongestionGame.mul_add_one_le_five_thirds_sq_add_one_third_sq`: the
  Christodoulou–Koutsoupias inequality `y (z + 1) ≤ 5/3 y² + 1/3 z²` on natural numbers.
* `Cslib.GameTheory.CongestionGame.isSmooth_of_hasAffineLatencies` ([Roughgarden2015],
  Example 2.5): affine congestion games are `(5/3, 1/3)`-smooth.
* `Cslib.GameTheory.CongestionGame.socialCost_le_of_isPureNash`
  ([AwerbuchAzarEpstein2005], [ChristodoulouKoutsoupias2005]): the pure price of anarchy of
  affine congestion games is at most `5/2`.
* `Cslib.GameTheory.CongestionGame.expected_socialCost_le`: the same bound for coarse correlated
  equilibria ([Roughgarden2015], Theorem 3.2 with Example 2.5).
* `Cslib.GameTheory.CongestionGame.exists_socialCost_eq_five_halves_mul`: the bound `5/2` is
  attained.

## References

* [AwerbuchAzarEpstein2005]
* [ChristodoulouKoutsoupias2005]
* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory.CongestionGame

variable {ι : Type*} {S : ι → Type*} {E : Type*} [Fintype ι] [DecidableEq E]
  (C : CongestionGame ι S E)

/-- `C` has **affine latencies**: there are `a e, b e ≥ 0` with `latency e k = a e * k + b e` for
every resource `e` and load `k`. -/
@[expose] def HasAffineLatencies : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e (k : ℕ), C.latency e k = a e * k + b e

omit [Fintype ι] [DecidableEq E] in
/-- Nonnegative affine latencies are nondecreasing. -/
theorem HasAffineLatencies.monotone_latency {C : CongestionGame ι S E} (h : C.HasAffineLatencies)
    (e : E) : Monotone (C.latency e) := by
  obtain ⟨a, b, ha, -, hl⟩ := h
  intro k l hkl
  rw [hl, hl]
  have : (k : ℝ) ≤ l := by exact_mod_cast hkl
  nlinarith [ha e]

/-- The inequality of Christodoulou and Koutsoupias [ChristodoulouKoutsoupias2005], as cited in
[Roughgarden2015], Example 2.5: `y (z + 1) ≤ 5/3 y² + 1/3 z²` for all natural numbers `y`, `z`. -/
theorem mul_add_one_le_five_thirds_sq_add_one_third_sq (y z : ℕ) :
    (y : ℝ) * (z + 1) ≤ 5 / 3 * (y : ℝ) ^ 2 + 1 / 3 * (z : ℝ) ^ 2 := by
  rcases Nat.lt_or_ge y 2 with hy | hy
  · interval_cases y
    · norm_num
    · have : ((z : ℝ) - 1) * ((z : ℝ) - 2) ≥ 0 := by
        rcases Nat.lt_or_ge z 2 with hz | hz
        · interval_cases z <;> norm_num
        · have : (2 : ℝ) ≤ z := by exact_mod_cast hz
          nlinarith
      push_cast
      nlinarith
  · have : (2 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith [sq_nonneg ((3 : ℝ) * y - 2 * z)]

variable [DecidableEq ι] [Finite E]

/-- Congestion games with affine latencies are **`(5/3, 1/3)`-smooth** ([Roughgarden2015],
Example 2.5). -/
theorem isSmooth_of_hasAffineLatencies (h : C.HasAffineLatencies) :
    C.toCostGame.IsSmooth (5 / 3) (1 / 3) := by
  have := Fintype.ofFinite E
  obtain ⟨a, b, ha, hb, hl⟩ := h
  intro s s'
  have hdev : ∀ i, C.toCostGame.cost i (Function.update s i (s' i))
      ≤ ∑ e ∈ C.resources i (s' i), C.latency e (C.load s e + 1) := by
    intro i
    rw [toCostGame_cost, Function.update_self]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [hl, hl]
    have hle : (C.load (Function.update s i (s' i)) e : ℝ) ≤ C.load s e + 1 := by
      exact_mod_cast C.load_update_le s i (s' i) e
    push_cast
    nlinarith [ha e]
  calc ∑ i, C.toCostGame.cost i (Function.update s i (s' i))
      ≤ ∑ i, ∑ e ∈ C.resources i (s' i), C.latency e (C.load s e + 1) :=
        Finset.sum_le_sum fun i _ => hdev i
    _ = ∑ e, (C.load s' e : ℝ) * C.latency e (C.load s e + 1) :=
        C.sum_sum_resources_eq_sum_load_mul s' _
    _ ≤ ∑ e, (5 / 3 * ((C.load s' e : ℝ) * C.latency e (C.load s' e))
          + 1 / 3 * ((C.load s e : ℝ) * C.latency e (C.load s e))) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [hl, hl, hl]
        have hk := mul_add_one_le_five_thirds_sq_add_one_third_sq (C.load s' e) (C.load s e)
        have : (0 : ℝ) ≤ C.load s e := Nat.cast_nonneg _
        have : (0 : ℝ) ≤ C.load s' e := Nat.cast_nonneg _
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hk (ha e), hb e]
    _ = 5 / 3 * C.toCostGame.socialCost s' + 1 / 3 * C.toCostGame.socialCost s := by
        rw [socialCost_toCostGame, socialCost_toCostGame, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.mul_sum]

/-- **The price of anarchy of affine congestion games is at most `5/2`**
([AwerbuchAzarEpstein2005], [ChristodoulouKoutsoupias2005]): every pure Nash equilibrium `s` of an
atomic congestion game with affine latencies satisfies `socialCost s ≤ 5/2 * socialCost s'` for
every profile `s'`. -/
theorem socialCost_le_of_isPureNash (h : C.HasAffineLatencies) {s : ∀ i, S i}
    (hs : C.toCostGame.IsPureNash s) (s' : ∀ i, S i) :
    C.toCostGame.socialCost s ≤ 5 / 2 * C.toCostGame.socialCost s' := by
  have h' := (C.isSmooth_of_hasAffineLatencies h).socialCost_le_of_isPureNash (by norm_num) hs s'
  norm_num at h' ⊢
  linarith

/-- **The robust price of anarchy of affine congestion games is at most `5/2`**
([Roughgarden2015], Theorem 3.2 with Example 2.5): the expected social cost of every coarse
correlated equilibrium is at most `5/2` times the social cost of every profile `s'`. -/
theorem expected_socialCost_le (h : C.HasAffineLatencies)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (hσ : C.toCostGame.IsCoarseCorrelatedEquilibrium σ)
    (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * C.toCostGame.socialCost s)
      ≤ 5 / 2 * C.toCostGame.socialCost s' := by
  have h' := (C.isSmooth_of_hasAffineLatencies h).expected_socialCost_le (by norm_num) hσ s'
  norm_num at h' ⊢
  linarith

end Cslib.GameTheory.CongestionGame

namespace Cslib.GameTheory.CongestionGame

/-- Resource sets of a three-player game with six resources: the resources `0, 1, 2` are shared,
and the resource `i + 3` is private to player `i`. Player `i`'s strategy `true` uses `{i, i + 3}`;
its strategy `false` uses the two shared resources other than `i` and the private resource of
player `i + 1`. -/
private def tightResources : ∀ _ : Fin 3, Bool → Finset (Fin 6)
  | 0, true => {0, 3}
  | 0, false => {1, 2, 4}
  | 1, true => {1, 4}
  | 1, false => {2, 0, 5}
  | 2, true => {2, 5}
  | 2, false => {0, 1, 3}

/-- A three-player congestion game with latencies `latency e k = k` whose pure price of anarchy
is exactly `5/2`. -/
private def tightGame : CongestionGame (Fin 3) (fun _ => Bool) (Fin 6) where
  resources := tightResources
  latency _ k := k

private theorem tightGame_socialCost_false :
    tightGame.toCostGame.socialCost (fun _ => false) = 15 := by
  rw [socialCost_toCostGame]
  have h : ∑ e, tightGame.load (fun _ => false) e * tightGame.load (fun _ => false) e = 15 := by
    decide
  change ∑ e, (tightGame.load (fun _ => false) e : ℝ) * (tightGame.load (fun _ => false) e : ℝ)
    = 15
  exact_mod_cast h

private theorem tightGame_socialCost_true :
    tightGame.toCostGame.socialCost (fun _ => true) = 6 := by
  rw [socialCost_toCostGame]
  have h : ∑ e, tightGame.load (fun _ => true) e * tightGame.load (fun _ => true) e = 6 := by
    decide
  change ∑ e, (tightGame.load (fun _ => true) e : ℝ) * (tightGame.load (fun _ => true) e : ℝ) = 6
  exact_mod_cast h

private theorem tightGame_isPureNash : tightGame.toCostGame.IsPureNash (fun _ => false) := by
  intro i t
  simp only [toCostGame_cost, tightGame]
  rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le]
  revert i t
  decide

/-- **The bound `5/2` is attained**: there is a three-player atomic congestion game with six
resources and latencies `latency e k = k` that has a pure Nash equilibrium `s` and a profile `s'`
with `socialCost s = 5/2 * socialCost s' > 0`. So the constant in `socialCost_le_of_isPureNash`
cannot be improved. -/
theorem exists_socialCost_eq_five_halves_mul :
    ∃ (C : CongestionGame (Fin 3) (fun _ => Bool) (Fin 6)) (s s' : Fin 3 → Bool),
      C.HasAffineLatencies ∧ C.toCostGame.IsPureNash s ∧ 0 < C.toCostGame.socialCost s' ∧
        C.toCostGame.socialCost s = 5 / 2 * C.toCostGame.socialCost s' := by
  refine ⟨tightGame, fun _ => false, fun _ => true,
    ⟨fun _ => 1, fun _ => 0, fun _ => zero_le_one, fun _ => le_rfl, fun e k => ?_⟩,
    tightGame_isPureNash, ?_, ?_⟩
  · change (k : ℝ) = 1 * k + 0
    rw [one_mul, add_zero]
  · rw [tightGame_socialCost_true]
    norm_num
  · rw [tightGame_socialCost_false, tightGame_socialCost_true]
    norm_num

end Cslib.GameTheory.CongestionGame
