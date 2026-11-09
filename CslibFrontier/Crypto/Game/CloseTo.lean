/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Probability.StatisticalDistance.CloseTo

/-!
# Bridging Boolean game advantage and all-events statistical closeness

`Cslib.Probability.CloseTo` measures total variation distance in `ℝ≥0∞` on an arbitrary discrete
type `α : Type` without `Fintype` or measurability assumptions, while `Cslib.Crypto.Game.advantage`
measures the distinguishing advantage in `ℝ≥0` between two Boolean experiments (`Game = PMF Bool`).

This module connects the two interfaces in both directions:

* On `Bool` itself, `CloseTo game1 game2 ε` is equivalent to `(advantage game1 game2 : ℝ≥0∞) ≤ ε`
  (`closeTo_iff_coe_advantage_le`, `closeTo_iff_advantage_le`).
* On any `α : Type`, `CloseTo μ ν ε` is equivalent to uniform `ε`-bounded advantage under every
  deterministic Boolean predicate `f : α → Bool` (`closeTo_iff_forall_coe_advantage_map_le`,
  `closeTo_iff_forall_advantage_map_le`) and under every randomized distinguisher `test : α → Game`
  (`closeTo_iff_forall_coe_advantage_bind_le`, `closeTo_iff_forall_advantage_bind_le`).

Unlike `CslibFrontier.Crypto.Game.Statistical`, which identifies `Game.advantage` with the
finite-PMF
metric `nndist`, these bridges require no `Fintype` instance on `α` and apply directly to word
ensembles `PMF (List Bool)` and protocol transcripts.

## Main results

* `Cslib.Crypto.Game.closeTo_iff_coe_advantage_le`, `Cslib.Crypto.Game.closeTo_iff_advantage_le`:
  statistical closeness of Boolean games is bounded distinguishing advantage.
* `Cslib.Crypto.Game.coe_advantage_map_le_of_closeTo`,
  `Cslib.Crypto.Game.advantage_map_le_of_closeTo`,
  `Cslib.Crypto.Game.coe_advantage_bind_le_of_closeTo`,
  `Cslib.Crypto.Game.advantage_bind_le_of_closeTo`: postprocessing `CloseTo` by a deterministic or
  randomized Boolean distinguisher bounds `Game.advantage`.
* `Cslib.Crypto.Game.closeTo_of_coe_advantage_decide_le`,
  `Cslib.Crypto.Game.closeTo_of_advantage_decide_le`: indicator-event tests suffice for `CloseTo`.
* `Cslib.Crypto.Game.closeTo_iff_forall_coe_advantage_map_le`,
  `Cslib.Crypto.Game.closeTo_iff_forall_advantage_map_le`,
  `Cslib.Crypto.Game.closeTo_iff_forall_coe_advantage_bind_le`,
  `Cslib.Crypto.Game.closeTo_iff_forall_advantage_bind_le`: variational characterizations of
  `CloseTo` via deterministic and randomized Boolean distinguishers.
* `Cslib.Probability.CloseTo.bind_right_tsum`: input-dependent error bounds on mixtures
  under `CloseTo`.
-/

@[expose] public section

namespace Cslib.Crypto.Game

open Probability
open scoped ENNReal NNReal

private theorem coe_succProbability_ennreal (game : Game) :
    (succProbability game : ℝ≥0∞) = game true :=
  ENNReal.coe_toNNReal (game.apply_ne_top true)

/-- On Boolean experiments, `ε`-closeness in `ℝ≥0∞` is equivalent to `(advantage : ℝ≥0∞) ≤ ε`. -/
theorem closeTo_iff_coe_advantage_le {game1 game2 : Game} {ε : ℝ≥0∞} :
    CloseTo game1 game2 ε ↔ (advantage game1 game2 : ℝ≥0∞) ≤ ε := by
  have hadv : (advantage game1 game2 : ℝ≥0∞) =
      max (game1 true - game2 true) (game2 true - game1 true) := by
    rw [advantage, NNReal.nndist_eq, ENNReal.coe_max, ENNReal.coe_sub, ENNReal.coe_sub,
      coe_succProbability_ennreal, coe_succProbability_ennreal]
  constructor
  · intro h
    rw [hadv]
    have h1 : game1 true ≤ game2 true + ε := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using h {true}
    have h2 : game2 true ≤ game1 true + ε := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using h.symm {true}
    exact max_le (tsub_le_iff_left.mpr h1) (tsub_le_iff_left.mpr h2)
  · intro hadv_le event
    rw [hadv, max_le_iff] at hadv_le
    have ht1 : game1 true ≤ game2 true + ε := tsub_le_iff_left.mp hadv_le.1
    have ht2 : game2 true ≤ game1 true + ε := tsub_le_iff_left.mp hadv_le.2
    have hsum1 : game1 true + game1 false = 1 := by
      simpa only [tsum_bool, add_comm] using game1.tsum_coe
    have hsum2 : game2 true + game2 false = 1 := by
      simpa only [tsum_bool, add_comm] using game2.tsum_coe
    have hf1 : game1 false ≤ game2 false + ε := by
      refine WithTop.le_of_add_le_add_left (game2.apply_ne_top true) ?_
      calc
        game2 true + game1 false ≤ (game1 true + ε) + game1 false :=
          add_le_add ht2 le_rfl
        _ = (game1 true + game1 false) + ε := by ac_rfl
        _ = (game2 true + game2 false) + ε := by rw [hsum1, hsum2]
        _ = game2 true + (game2 false + ε) := by ac_rfl
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, tsum_bool, tsum_bool]
    by_cases h0 : false ∈ event <;> by_cases h1 : true ∈ event
    · simp only [Set.indicator_of_mem h0, Set.indicator_of_mem h1]
      rw [add_comm (game1 false), hsum1, add_comm (game2 false), hsum2]
      exact le_self_add
    · simp only [Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
      exact hf1
    · simp only [Set.indicator_of_notMem h0, Set.indicator_of_mem h1, zero_add]
      exact ht1
    · simp [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]

/-- On Boolean experiments, `ε`-closeness for `ε : ℝ≥0` is equivalent to `advantage ≤ ε`. -/
theorem closeTo_iff_advantage_le {game1 game2 : Game} {ε : ℝ≥0} :
    CloseTo game1 game2 ε ↔ advantage game1 game2 ≤ ε :=
  closeTo_iff_coe_advantage_le.trans ENNReal.coe_le_coe

/-- Deterministic Boolean postprocessing of `ε`-close distributions has `(advantage : ℝ≥0∞) ≤ ε`. -/
theorem coe_advantage_map_le_of_closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CloseTo μ ν ε) (f : α → Bool) :
    (advantage (μ.map f) (ν.map f) : ℝ≥0∞) ≤ ε :=
  closeTo_iff_coe_advantage_le.mp (h.map f)

/-- Deterministic Boolean postprocessing of `ε`-close distributions has `advantage ≤ ε`. -/
theorem advantage_map_le_of_closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0}
    (h : CloseTo μ ν ε) (f : α → Bool) :
    advantage (μ.map f) (ν.map f) ≤ ε :=
  closeTo_iff_advantage_le.mp (h.map f)

/-- Running any randomized Boolean distinguisher `test : α → Game` on `ε`-close distributions has
`(advantage : ℝ≥0∞) ≤ ε`, without finiteness assumptions on `α`. -/
theorem coe_advantage_bind_le_of_closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CloseTo μ ν ε) (test : α → Game) :
    (advantage (μ.bind test) (ν.bind test) : ℝ≥0∞) ≤ ε :=
  closeTo_iff_coe_advantage_le.mp (h.bind_left test)

/-- Running any randomized Boolean distinguisher `test : α → Game` on `ε`-close distributions has
`advantage ≤ ε`, without finiteness assumptions on `α`. -/
theorem advantage_bind_le_of_closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0}
    (h : CloseTo μ ν ε) (test : α → Game) :
    advantage (μ.bind test) (ν.bind test) ≤ ε :=
  closeTo_iff_advantage_le.mp (h.bind_left test)

open Classical in
/-- A bound in `ℝ≥0∞` on the advantage of every indicator test gives `CloseTo`. -/
theorem closeTo_of_coe_advantage_decide_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : ∀ E : Set α, (advantage (μ.map fun a => decide (a ∈ E))
      (ν.map fun a => decide (a ∈ E)) : ℝ≥0∞) ≤ ε) :
    CloseTo μ ν ε := fun E => by
  have hmap (p : PMF α) : (p.map fun a => decide (a ∈ E)) true = p.toOuterMeasure E := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext a
    simp
  have hclose := closeTo_iff_coe_advantage_le.mpr (h E) {true}
  simpa only [PMF.toOuterMeasure_apply_singleton, hmap] using hclose

open Classical in
/-- A bound in `ℝ≥0` on the advantage of every indicator test gives `CloseTo`. -/
theorem closeTo_of_advantage_decide_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0}
    (h : ∀ E : Set α, advantage (μ.map fun a => decide (a ∈ E))
      (ν.map fun a => decide (a ∈ E)) ≤ ε) :
    CloseTo μ ν ε :=
  closeTo_of_coe_advantage_decide_le fun E => ENNReal.coe_le_coe.mpr (h E)

/-- Variational characterization of `CloseTo` in `ℝ≥0∞` via deterministic Boolean tests. -/
theorem closeTo_iff_forall_coe_advantage_map_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} :
    CloseTo μ ν ε ↔ ∀ f : α → Bool, (advantage (μ.map f) (ν.map f) : ℝ≥0∞) ≤ ε := by
  classical
  exact ⟨coe_advantage_map_le_of_closeTo, fun h => closeTo_of_coe_advantage_decide_le fun E => h _⟩

/-- Variational characterization of `CloseTo` for `ε : ℝ≥0` via deterministic Boolean tests. -/
theorem closeTo_iff_forall_advantage_map_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0} :
    CloseTo μ ν ε ↔ ∀ f : α → Bool, advantage (μ.map f) (ν.map f) ≤ ε := by
  classical
  exact ⟨advantage_map_le_of_closeTo, fun h => closeTo_of_advantage_decide_le fun E => h _⟩

/-- Variational characterization of `CloseTo` in `ℝ≥0∞` via randomized Boolean distinguishers. -/
theorem closeTo_iff_forall_coe_advantage_bind_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} :
    CloseTo μ ν ε ↔ ∀ test : α → Game, (advantage (μ.bind test) (ν.bind test) : ℝ≥0∞) ≤ ε := by
  rw [closeTo_iff_forall_coe_advantage_map_le]
  refine ⟨fun h test => coe_advantage_bind_le_of_closeTo
      (closeTo_iff_forall_coe_advantage_map_le.mpr h) test, fun h f => ?_⟩
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact h _

/-- Variational characterization of `CloseTo` for `ε : ℝ≥0` via randomized Boolean
distinguishers. -/
theorem closeTo_iff_forall_advantage_bind_le {α : Type} {μ ν : PMF α} {ε : ℝ≥0} :
    CloseTo μ ν ε ↔ ∀ test : α → Game, advantage (μ.bind test) (ν.bind test) ≤ ε := by
  rw [closeTo_iff_forall_advantage_map_le]
  refine ⟨fun h test => advantage_bind_le_of_closeTo
      (closeTo_iff_forall_advantage_map_le.mpr h) test, fun h f => ?_⟩
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact h _

end Cslib.Crypto.Game

namespace Cslib.Probability

open scoped ENNReal

/-- Pointwise statistical closeness of continuations on `μ.support` with input-dependent error
`err : α → ℝ≥0∞` bounds the mixture distance by `∑' a, μ a * err a`. -/
theorem CloseTo.bind_right_tsum {α β : Type} (μ : PMF α) {f g : α → PMF β} {err : α → ℝ≥0∞}
    (h : ∀ a ∈ μ.support, CloseTo (f a) (g a) (err a)) :
    CloseTo (μ.bind f) (μ.bind g) (∑' a, μ a * err a) := fun event => by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, μ a * (f a).toOuterMeasure event
      ≤ ∑' a, μ a * ((g a).toOuterMeasure event + err a) := by
        refine tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_of_nonneg_left (h a ha event) zero_le
        · simp [(PMF.apply_eq_zero_iff μ a).mpr ha]
    _ = ∑' a, μ a * (g a).toOuterMeasure event + ∑' a, μ a * err a := by
        simp only [mul_add, tsum_add]

end Cslib.Probability
