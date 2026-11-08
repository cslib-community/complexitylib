/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.GameTheory.Congestion.CostSharing
import Complexity.GameTheory.Congestion.Stability
import Complexity.GameTheory.Strategic.Stability
import ComplexityTests.GameTheory.Congestion

/-!
# The price of stability by the potential method

* A two-player coordination game with a common cost: both players on `true` costs `1` each,
  both on `false` costs `2` each, and a mismatch costs `3` each. The common cost is an exact
  potential with `socialCost = 2 * Φ`, so the potential function method with `A * B = 1` gives an
  optimal pure Nash equilibrium, although the equilibrium "both `false`" costs twice the optimum.
* The affine game `twoLinks` of `ComplexityTests.GameTheory.Congestion`: Rosenthal's potential
  sits strictly between `socialCost / 2` and `socialCost` at the profile "both on link `0`", and
  the price-of-stability bound `2` applies.
* A two-player VHS-or-Betamax fair cost-sharing game ([Roughgarden2013CS364A], Lecture #15,
  Section 1.3, with `k = 2` and `ε = 1/2`): both "all Betamax" (cost `3/2`) and "all VHS"
  (cost `2`) are pure Nash equilibria, and the `H 2` price-of-stability bound applies.
* The opt-out game with three players. With `ε = 1/10`, everyone sharing is not an equilibrium
  and everyone opting out is, at social cost `H 3 = 11/6` against `11/10`, a ratio of `5/3`.
  Separately, with `ε = 1/108` every equilibrium costs more than `9/5` times the optimum, so the
  factor `9/5 < H 3` fails; `exists_forall_isPureNash_optOut_mul_lt` gives this for every
  `r < H 3`. With `ε = 0` the hypothesis `0 < ε` of `isPureNash_optOut_iff` is needed: for two
  players, everyone sharing is then an equilibrium.
-/

namespace ComplexityTests.GameTheory.Stability

open Cslib.GameTheory Cslib.GameTheory.CongestionGame

/-! ### The potential function method on a coordination game -/

/-- The common cost of the coordination game. -/
noncomputable def coordCost (s : Fin 2 → Bool) : ℝ :=
  if s 0 = s 1 then (if s 0 then 1 else 2) else 3

/-- A two-player coordination game in which both players pay the common cost `coordCost`. -/
noncomputable def coord : CostGame (Fin 2) (fun _ => Bool) where
  cost _ s := coordCost s

theorem coord_isExactPotential : coord.IsExactPotential coordCost := fun _ _ _ => rfl

theorem coord_socialCost (s : Fin 2 → Bool) : coord.socialCost s = 2 * coordCost s := by
  rw [CostGame.socialCost, Fin.sum_univ_two, two_mul]
  rfl

/-- "Both `false`" is a pure Nash equilibrium: a unilateral deviation creates a mismatch. -/
theorem coord_isPureNash_false : coord.IsPureNash fun _ => false := by
  intro i a
  change coordCost (fun _ => false) ≤ coordCost (Function.update (fun _ => false) i a)
  fin_cases i <;> cases a <;> simp [coordCost] <;> norm_num

/-- "Both `false`" costs twice the optimum "both `true`": the price of anarchy is at least `2`. -/
example : coord.socialCost (fun _ => false) = 2 * coord.socialCost (fun _ => true) := by
  rw [coord_socialCost, coord_socialCost]
  norm_num [coordCost]

/-- The potential function method with `A = 2` and `B = 1/2` gives an equilibrium within the
factor `A * B = 1` of every profile: the price of stability is `1`. -/
example : ∃ s, coord.IsPureNash s ∧ ∀ s', coord.socialCost s ≤ 1 * coord.socialCost s' := by
  have h := coord_isExactPotential.isGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le
    zero_le_two (B := 1 / 2) (fun s => (coord_socialCost s).le)
    (fun s => by rw [coord_socialCost]; linarith)
  norm_num at h ⊢
  exact h

/-- Better-response dynamics started at the optimum "both `true`" reach an equilibrium that is
also optimal. -/
example : ∃ t, Relation.ReflTransGen (flip coord.Improves) (fun _ => true) t ∧ coord.IsPureNash t ∧
    coord.socialCost t ≤ 2 := by
  have hpot := coord_isExactPotential.isGeneralizedOrdinalPotential
  obtain ⟨t, hpath, ht, hle⟩ := hpot.exists_reflTransGen_isPureNash_socialCost_le
    zero_le_two (B := 1 / 2) (fun s => (coord_socialCost s).le)
    (fun s => by rw [coord_socialCost]; linarith) (fun _ => true)
  refine ⟨t, hpath, ht, ?_⟩
  have h1 : coord.socialCost (fun _ => true) = 2 := by
    rw [coord_socialCost]
    norm_num [coordCost]
  rw [h1] at hle
  linarith

/-! ### Affine congestion games -/

open ComplexityTests.GameTheory.Congestion

theorem twoLinks_rosenthalPotential_zero : twoLinks.rosenthalPotential (fun _ => 0) = 3 := by
  rw [rosenthalPotential_def]
  have h : twoLinks.load (fun _ => 0) 0 = 2 ∧ twoLinks.load (fun _ => 0) 1 = 0 := by decide
  rw [Fin.sum_univ_two, h.1, h.2]
  norm_num [twoLinks, Finset.sum_range_succ]

/-- At "both on link `0`", `socialCost / 2 < Φ < socialCost`: `2 < 3 < 4`. -/
example : twoLinks.toCostGame.socialCost (fun _ => 0) / 2 < twoLinks.rosenthalPotential (fun _ => 0)
    ∧ twoLinks.rosenthalPotential (fun _ => 0) < twoLinks.toCostGame.socialCost (fun _ => 0) := by
  rw [twoLinks_rosenthalPotential_zero, twoLinks_socialCost_zero]
  norm_num

/-- The general bounds at the same profile. -/
example : twoLinks.rosenthalPotential (fun _ => 0) ≤ twoLinks.toCostGame.socialCost (fun _ => 0)
    ∧ twoLinks.toCostGame.socialCost (fun _ => 0) ≤ 2 * twoLinks.rosenthalPotential (fun _ => 0) :=
  ⟨twoLinks.rosenthalPotential_le_socialCost twoLinks_hasAffineLatencies.monotone_latency _,
    twoLinks.socialCost_le_two_mul_rosenthalPotential twoLinks_hasAffineLatencies _⟩

/-- The price of stability of `twoLinks` is at most `2`. -/
example : ∃ s, twoLinks.toCostGame.IsPureNash s ∧
    ∀ s', twoLinks.toCostGame.socialCost s ≤ 2 * twoLinks.toCostGame.socialCost s' :=
  twoLinks.exists_isPureNash_socialCost_le_two_mul twoLinks_hasAffineLatencies

/-- Better-response dynamics from "both on link `0`" reach an equilibrium of social cost at most
`8`. -/
example : ∃ t, Relation.ReflTransGen (flip twoLinks.toCostGame.Improves) (fun _ => 0) t ∧
    twoLinks.toCostGame.IsPureNash t ∧ twoLinks.toCostGame.socialCost t ≤ 8 := by
  obtain ⟨t, hpath, ht, hle⟩ :=
    twoLinks.exists_reflTransGen_isPureNash_socialCost_le_two_mul twoLinks_hasAffineLatencies
      (fun _ => 0)
  refine ⟨t, hpath, ht, ?_⟩
  rw [twoLinks_socialCost_zero] at hle
  linarith

/-! ### Fair cost sharing: VHS or Betamax -/

/-- Two players adopt Betamax (`true`, cost `3/2`) or VHS (`false`, cost `2`). -/
noncomputable def vhs : CongestionGame (Fin 2) (fun _ => Bool) Bool :=
  fairCostSharing (fun _ b => {b}) fun b => if b then 3 / 2 else 2

theorem vhs_cost_nonneg : ∀ b, 0 ≤ (fun b : Bool => if b then (3 / 2 : ℝ) else 2) b := by
  intro b
  cases b <;> norm_num

theorem vhs_load (s : Fin 2 → Bool) (b : Bool) :
    vhs.load s b = (Finset.univ.filter fun i => s i = b).card := by
  rw [vhs, CongestionGame.load, fairCostSharing_resources]
  simp only [Finset.mem_singleton, eq_comm]

theorem vhs_cost (s : Fin 2 → Bool) (i : Fin 2) :
    vhs.toCostGame.cost i s
      = (if s i then 3 / 2 else 2) / (Finset.univ.filter fun j => s j = s i).card := by
  have hr : vhs.resources i (s i) = {s i} := by
    rw [vhs, fairCostSharing_resources]
  rw [toCostGame_cost, hr, Finset.sum_singleton, vhs_load, vhs, fairCostSharing_latency]

/-- Every player adopting `b` is a pure Nash equilibrium, for either technology `b`. -/
theorem vhs_isPureNash (b : Bool) : vhs.toCostGame.IsPureNash fun _ => b := by
  intro i a
  rw [vhs_cost, vhs_cost]
  have hc : ∀ (b a : Bool), (Finset.univ.filter fun j => (fun _ : Fin 2 => b) j = b).card = 2 ∧
      (Finset.univ.filter fun j => Function.update (fun _ : Fin 2 => b) i a j
        = Function.update (fun _ : Fin 2 => b) i a i).card = if a = b then 2 else 1 := by
    revert i
    decide
  obtain ⟨h1, h2⟩ := hc b a
  rw [h1, h2, Function.update_self]
  cases a <;> cases b <;> norm_num

theorem vhs_socialCost (b : Bool) :
    vhs.toCostGame.socialCost (fun _ => b) = if b then 3 / 2 else 2 := by
  rw [CostGame.socialCost, Fin.sum_univ_two, vhs_cost, vhs_cost]
  cases b <;> norm_num

/-- The bad equilibrium "all VHS" costs `4/3` times the good one "all Betamax". -/
example : vhs.toCostGame.socialCost (fun _ => false)
    = 4 / 3 * vhs.toCostGame.socialCost (fun _ => true) := by
  rw [vhs_socialCost, vhs_socialCost]
  norm_num

/-- The `H 2 = 3/2` price-of-stability bound applies to the VHS-or-Betamax game. -/
example : ∃ s, vhs.toCostGame.IsPureNash s ∧
    ∀ s', vhs.toCostGame.socialCost s ≤ 3 / 2 * vhs.toCostGame.socialCost s' := by
  have h := exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul (ι := Fin 2)
    (fun _ (b : Bool) => {b}) _ vhs_cost_nonneg
  have h2 : ((harmonic (Fintype.card (Fin 2)) : ℚ) : ℝ) = 3 / 2 := by
    rw [Fintype.card_fin, harmonic_succ, harmonic_succ, harmonic_zero]
    norm_num
  rw [h2] at h
  exact h

/-! ### The opt-out game -/

theorem harmonic_three : ((harmonic 3 : ℚ) : ℝ) = 11 / 6 := by
  rw [harmonic_succ, harmonic_succ, harmonic_succ, harmonic_zero]
  norm_num

/-- With three players and `ε = 1/10`, everyone sharing is not a pure Nash equilibrium. -/
example : ¬ (optOut 3 (1 / 10)).toCostGame.IsPureNash fun _ => false := by
  rw [isPureNash_optOut_iff (by norm_num)]
  intro h
  simpa using congrFun h 0

/-- Everyone opting out is the pure Nash equilibrium. -/
example : (optOut 3 (1 / 10)).toCostGame.IsPureNash fun _ => true :=
  (isPureNash_optOut_iff (by norm_num) _).2 rfl

/-- The equilibrium costs `H 3 = 11/6`, the optimum `11/10`. -/
example : (optOut 3 (1 / 10)).toCostGame.socialCost (fun _ => true) = 11 / 6 ∧
    (optOut 3 (1 / 10)).toCostGame.socialCost (fun _ => false) = 11 / 10 := by
  rw [socialCost_optOut_true, harmonic_three, socialCost_optOut_false (by norm_num)]
  norm_num

/-- With `ε = 1/108`, every pure Nash equilibrium of the three-player opt-out game costs more than
`9/5` times the profile in which everyone shares: `9/5 * 109/108 < 11/6`. -/
example (s : Fin 3 → Bool) (hs : (optOut 3 (1 / 108)).toCostGame.IsPureNash s) :
    9 / 5 * (optOut 3 (1 / 108)).toCostGame.socialCost (fun _ => false)
      < (optOut 3 (1 / 108)).toCostGame.socialCost s := by
  rw [(isPureNash_optOut_iff (by norm_num) s).1 hs, socialCost_optOut_true, harmonic_three,
    socialCost_optOut_false (by norm_num)]
  norm_num

/-- The tightness theorem: the factor `9/5 < H 3` fails for some three-player opt-out game. -/
example : ∃ ε > 0, ∀ s, (optOut 3 ε).toCostGame.IsPureNash s →
    9 / 5 * (optOut 3 ε).toCostGame.socialCost (fun _ => false)
      < (optOut 3 ε).toCostGame.socialCost s :=
  exists_forall_isPureNash_optOut_mul_lt (by norm_num) (by rw [harmonic_three]; norm_num)

/-- With `ε = 0` and two players, everyone sharing *is* a pure Nash equilibrium: each pays `1/2`,
and opting out costs `1` or `1/2`. So `isPureNash_optOut_iff` needs `0 < ε`. -/
example : (optOut 2 0).toCostGame.IsPureNash fun _ => false := by
  intro i a
  rw [optOut_cost, optOut_cost, Function.update_self]
  have hc : (Finset.univ.filter fun j => (fun _ : Fin 2 => false) j = false).card = 2 ∧
      (Finset.univ.filter fun j => Function.update (fun _ : Fin 2 => false) i false j = false).card
        = 2 := by
    revert i
    decide
  rw [hc.1]
  cases a
  · rw [hc.2]
  · fin_cases i <;> norm_num

end ComplexityTests.GameTheory.Stability
