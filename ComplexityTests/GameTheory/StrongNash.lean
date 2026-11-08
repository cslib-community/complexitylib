/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Congestion.StrongNash
import ComplexityTests.GameTheory.Stability

/-!
# Strong Nash equilibria

* The coordination game of `ComplexityTests.GameTheory.Stability`: the pure Nash equilibrium
  "both `false`" is not strong (both players gain by switching together to "both `true`"), and
  "both `true`" is strong.
* The VHS-or-Betamax fair cost-sharing game: the bad pure Nash equilibrium "all VHS" is not strong
  ([Roughgarden2013CS364A], Lecture #15, Section 3), directly and through the common-strategy-set
  correspondence `isStrongNash_fairCostSharing_iff` (it is not of minimum cost), while
  "all Betamax" is strong, as the common-strategy-set theorems predict; and every strong Nash
  equilibrium is optimal.
* The opt-out game: for `ε = 1/10` and three players, everyone opting out is a strong Nash
  equilibrium of cost `H 3 = 11/6`, within the `H 3` bound of the optimum `11/10`; everyone sharing
  is not strong. Separately, the tightness theorem refutes the factor `9/5 < H 3` for some
  three-player opt-out game.
* The two notions of strong equilibrium differ: with `ε = 0` and two players, everyone opting out is
  a pure Nash equilibrium and a strong equilibrium (`IsStrongEquilibrium`), but not a strong Nash
  equilibrium (`IsStrongNash`). In particular `isStrongNash_optOut_true` needs `0 < ε`.
* The nonincreasing-latency hypothesis of `socialCost_le_rosenthalPotential_of_isStrongEquilibrium`
  is needed: with two players forced onto one resource of latency `n ↦ n`, the only profile is a
  strong Nash equilibrium of social cost `4`, above its Rosenthal potential `3`.
-/

namespace ComplexityTests.GameTheory.StrongNash

open Cslib.GameTheory Cslib.GameTheory.CongestionGame ComplexityTests.GameTheory.Stability

/-! ### The coordination game -/

/-- "Both `false`" is a pure Nash equilibrium that is not strong: the grand coalition switches to
"both `true`", and each player's cost drops from `2` to `1`. -/
example : coord.IsPureNash (fun _ => false) ∧ ¬ coord.IsStrongNash fun _ => false := by
  refine ⟨coord_isPureNash_false, fun h => h.not_pareto (fun _ => true) ⟨fun i => ?_, 0, ?_⟩⟩
  · change coordCost (fun _ => true) ≤ coordCost (fun _ => false)
    norm_num [coordCost]
  · change coordCost (fun _ => true) < coordCost (fun _ => false)
    norm_num [coordCost]

/-- "Both `true`" is a strong Nash equilibrium: its common cost `1` is the least possible. -/
example : coord.IsStrongNash fun _ => true := by
  rintro A t ⟨-, i, -, hlt⟩
  change coordCost (A.piecewise t fun _ => true) < coordCost (fun _ => true) at hlt
  have h1 : coordCost (fun _ => true) = 1 := by norm_num [coordCost]
  have h2 : 1 ≤ coordCost (A.piecewise t fun _ => true) := by
    unfold coordCost
    split_ifs <;> norm_num
  linarith

/-! ### VHS or Betamax -/

/-- The bad equilibrium "all VHS" is not strong: switching together to Betamax lowers each player's
cost from `1` to `3/4`. -/
example :
    vhs.toCostGame.IsPureNash (fun _ => false) ∧ ¬ vhs.toCostGame.IsStrongNash fun _ => false := by
  refine ⟨vhs_isPureNash false, fun h => h.not_pareto (fun _ => true) ⟨fun i => ?_, 0, ?_⟩⟩
  · rw [vhs_cost, vhs_cost]
    have hc : ∀ b : Bool, (Finset.univ.filter fun j : Fin 2 => (fun _ => b) j = b).card = 2 := by
      decide
    rw [hc, hc]
    norm_num
  · rw [vhs_cost, vhs_cost]
    have hc : ∀ b : Bool, (Finset.univ.filter fun j : Fin 2 => (fun _ => b) j = b).card = 2 := by
      decide
    rw [hc, hc]
    norm_num

/-- Betamax is the cheaper technology, so "all Betamax" is a strong Nash equilibrium and every
strong Nash equilibrium is optimal (both players have the strategy set `Bool` and the resource map
`b ↦ {b}`). -/
example : vhs.toCostGame.IsStrongNash (fun _ => true) ∧
    ∀ s t, vhs.toCostGame.IsStrongNash s →
      vhs.toCostGame.socialCost s ≤ vhs.toCostGame.socialCost t := by
  have hp : ∀ q : Bool,
      ∑ e ∈ ({true} : Finset Bool), (fun b : Bool => if b then (3 / 2 : ℝ) else 2) e
        ≤ ∑ e ∈ ({q} : Finset Bool), (fun b : Bool => if b then (3 / 2 : ℝ) else 2) e := by
    intro q
    cases q <;> norm_num
  exact ⟨isStrongNash_fairCostSharing_const (R := fun b => {b}) vhs_cost_nonneg hp,
    fun s t hs => socialCost_fairCostSharing_le_of_isStrongNash (R := fun b => {b}) vhs_cost_nonneg
      hs t⟩

/-- Through the common-strategy-set correspondence: "all VHS" costs `2`, more than the `3/2` of
"all Betamax", so it is not a strong Nash equilibrium. -/
example : ¬ vhs.toCostGame.IsStrongNash fun _ => false := by
  rw [vhs, isStrongNash_fairCostSharing_iff (R := fun b => {b}) vhs_cost_nonneg]
  intro h
  have h' := h fun _ => true
  rw [socialCost_fairCostSharing_const, socialCost_fairCostSharing_const] at h'
  norm_num at h'

/-- The `H 2 = 3/2` strong price-of-anarchy bound applies to the VHS-or-Betamax game. -/
example (s : Fin 2 → Bool) (hs : vhs.toCostGame.IsStrongNash s) (t : Fin 2 → Bool) :
    vhs.toCostGame.socialCost s ≤ 3 / 2 * vhs.toCostGame.socialCost t := by
  have h := socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash vhs_cost_nonneg hs t
  have h2 : ((harmonic (Fintype.card (Fin 2)) : ℚ) : ℝ) = 3 / 2 := by
    rw [Fintype.card_fin, harmonic_succ, harmonic_succ, harmonic_zero]
    norm_num
  rwa [h2] at h

/-! ### The opt-out game -/

/-- With three players and `ε = 1/10`, everyone opting out is the strong Nash equilibrium, and
everyone sharing is not one. -/
example : (optOut 3 (1 / 10)).toCostGame.IsStrongNash (fun _ => true) ∧
    ¬ (optOut 3 (1 / 10)).toCostGame.IsStrongNash fun _ => false := by
  refine ⟨isStrongNash_optOut_true (by norm_num), fun h => ?_⟩
  rw [isStrongNash_optOut_iff (by norm_num)] at h
  simpa using congrFun h 0

/-- The strong price-of-anarchy theorem at the opt-out game: the strong Nash equilibrium of cost
`H 3 = 11/6` is within the factor `H 3` of the optimum `11/10`. -/
example : (optOut 3 (1 / 10)).toCostGame.socialCost (fun _ => true)
    ≤ harmonic 3 * (optOut 3 (1 / 10)).toCostGame.socialCost fun _ => false := by
  have h := socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash
    (optOutCost_nonneg (k := 3) (by norm_num : (0 : ℝ) ≤ 1 / 10))
    (isStrongNash_optOut_true (by norm_num)) (fun _ => false)
  rwa [Fintype.card_fin, ← optOut_def] at h

/-- The tightness theorem: the factor `9/5 < H 3` fails for strong Nash equilibria, and for strong
equilibria, of some three-player opt-out game. -/
example : ∃ ε > 0, (optOut 3 ε).toCostGame.IsStrongNash (fun _ => true) ∧
    ∀ s, (optOut 3 ε).toCostGame.IsStrongEquilibrium s →
      9 / 5 * (optOut 3 ε).toCostGame.socialCost (fun _ => false)
        < (optOut 3 ε).toCostGame.socialCost s :=
  exists_isStrongNash_optOut_mul_lt (by norm_num) (by rw [harmonic_three]; norm_num)

/-- With `ε = 0` and two players, everyone opting out is still a pure Nash equilibrium (a lone
deviator pays the whole shared cost `1`), but it is not strong: the grand coalition shares, and
player `0` pays `1/2` instead of `1` while player `1` pays `1/2` as before. So
`isStrongNash_optOut_true` needs `0 < ε`. -/
example : (optOut 2 0).toCostGame.IsPureNash (fun _ => true) ∧
    ¬ (optOut 2 0).toCostGame.IsStrongNash fun _ => true := by
  have hc : (Finset.univ.filter fun j => (fun _ : Fin 2 => false) j = false).card = 2 := by
    decide
  refine ⟨fun i a => ?_, fun h => h.not_pareto (fun _ => false) ⟨fun i => ?_, 0, ?_⟩⟩
  · cases a
    · rw [optOut_cost, optOut_cost, Function.update_self]
      have h1 : (Finset.univ.filter fun j =>
          Function.update (fun _ : Fin 2 => true) i false j = false).card = 1 := by
        revert i
        decide
      rw [h1]
      fin_cases i <;> norm_num
    · rw [Function.update_eq_self]
  · rw [optOut_cost, optOut_cost, hc]
    fin_cases i <;> norm_num
  · rw [optOut_cost, optOut_cost, hc]
    norm_num

/-- With `ε = 0` and two players, everyone opting out is nevertheless a strong equilibrium: no
nonempty coalition has a joint deviation from which *every* member strictly gains. Player `1` pays
`1/2` when opting out and at least `1/2` at every profile, and if player `1` keeps opting out then
player `0` pays `1` whatever it does. With the previous example, this separates
`IsStrongEquilibrium` from `IsStrongNash`. -/
example : (optOut 2 0).toCostGame.IsStrongEquilibrium fun _ => true := by
  rw [CostGame.isStrongEquilibrium_iff]
  intro A hA t
  by_cases h1 : (1 : Fin 2) ∈ A
  · refine ⟨1, h1, ?_⟩
    simp only [optOut_cost, Finset.card_filter, Fin.sum_univ_two]
    generalize A.piecewise t (fun _ => true) 0 = a
    generalize A.piecewise t (fun _ => true) 1 = b
    cases a <;> cases b <;> norm_num
  · have h0 : (0 : Fin 2) ∈ A := by
      obtain ⟨j, hj⟩ := hA
      fin_cases j
      · exact hj
      · exact absurd hj h1
    have hu1 : A.piecewise t (fun _ => true) 1 = true := Finset.piecewise_eq_of_notMem _ _ _ h1
    refine ⟨0, h0, ?_⟩
    simp only [optOut_cost, Finset.card_filter, Fin.sum_univ_two, hu1]
    generalize A.piecewise t (fun _ => true) 0 = a
    cases a <;> norm_num

/-! ### The nonincreasing-latency hypothesis is needed -/

/-- Two players, each with a single strategy that uses the single resource, of latency `n ↦ n`. -/
noncomputable def crowded : CongestionGame (Fin 2) (fun _ => Unit) Unit where
  resources _ _ := {()}
  latency _ n := n

theorem crowded_load (s : Fin 2 → Unit) : crowded.load s () = 2 := by
  have hs : s = fun _ => () := funext fun _ => rfl
  subst hs
  decide

/-- The only profile is trivially a strong Nash equilibrium, but its social cost `4` exceeds its
Rosenthal potential `1 + 2 = 3`: the latency `n ↦ n` is increasing. -/
example : crowded.toCostGame.IsStrongNash (fun _ => ()) ∧
    crowded.rosenthalPotential (fun _ => ()) < crowded.toCostGame.socialCost fun _ => () := by
  refine ⟨fun A t ⟨_, i, _, hlt⟩ => ?_, ?_⟩
  · have ht : A.piecewise t (fun _ => ()) = fun _ => () := funext fun _ => rfl
    rw [ht] at hlt
    exact lt_irrefl _ hlt
  · rw [rosenthalPotential_def, socialCost_toCostGame, Fintype.sum_unique, Fintype.sum_unique,
      crowded_load]
    norm_num [crowded, Finset.sum_range_succ]

end ComplexityTests.GameTheory.StrongNash
