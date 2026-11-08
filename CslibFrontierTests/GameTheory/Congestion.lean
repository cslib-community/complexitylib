/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Congestion.Affine
import CslibFrontier.GameTheory.Congestion.Hedge
import CslibFrontier.GameTheory.Congestion.PigouBound

/-!
# Congestion games and the price of anarchy

An atomic Pigou-style game: two players and two links, with latency `k` on link `0` at load `k`
and constant latency `2` on link `1`. Both players on link `0` is a pure Nash equilibrium of
social cost `4`, while splitting costs `3`, so the pure price of anarchy of this affine instance
is at least `4/3`, within the `5/2` bound. Quadratic latencies are not affine. The bounds `5/2`
and `4/3` are sharp: no smaller constant bounds the price of anarchy over all affine instances.
A nonatomic network with linear latencies `x` and `2 x` has a Wardrop equilibrium that is also
optimal, and a feasible flow that is not a Wardrop equilibrium. Hedge dynamics on `twoLinks` start
uniform, and the price-of-anarchy bound for Hedge dynamics applies to it for every horizon.
-/

namespace ComplexityTests.GameTheory.Congestion

open Cslib.GameTheory

/-- Two players choose one of two links: link `0` has latency `k` at load `k`, link `1` has
constant latency `2`. -/
def twoLinks : CongestionGame (Fin 2) (fun _ => Fin 2) (Fin 2) where
  resources _ a := {a}
  latency e k := if e = 0 then k else 2

theorem twoLinks_hasAffineLatencies : twoLinks.HasAffineLatencies :=
  ⟨![1, 0], ![0, 2], fun e => by fin_cases e <;> norm_num, fun e => by fin_cases e <;> norm_num,
    fun e k => by fin_cases e <;> simp [twoLinks]⟩

theorem twoLinks_socialCost_zero : twoLinks.toCostGame.socialCost (fun _ => 0) = 4 := by
  rw [CongestionGame.socialCost_toCostGame]
  have h : twoLinks.load (fun _ => 0) 0 = 2 ∧ twoLinks.load (fun _ => 0) 1 = 0 := by decide
  rw [Fin.sum_univ_two, h.1, h.2]
  norm_num [twoLinks]

theorem twoLinks_socialCost_split : twoLinks.toCostGame.socialCost ![0, 1] = 3 := by
  rw [CongestionGame.socialCost_toCostGame]
  have h : twoLinks.load ![0, 1] 0 = 1 ∧ twoLinks.load ![0, 1] 1 = 1 := by decide
  rw [Fin.sum_univ_two, h.1, h.2]
  norm_num [twoLinks]

/-- Both players on the variable link is a pure Nash equilibrium: moving to the constant link
costs `2`, the same as staying. -/
theorem twoLinks_isPureNash : twoLinks.toCostGame.IsPureNash fun _ => 0 := by
  intro i a
  have h0 : twoLinks.load (fun _ => 0) 0 = 2 := by decide
  have hu : twoLinks.load (Function.update (fun _ => 0) i a) a = if a = 0 then 2 else 1 := by
    revert i a
    decide
  rw [CongestionGame.toCostGame_cost, CongestionGame.toCostGame_cost, Function.update_self]
  change ∑ e ∈ ({0} : Finset (Fin 2)), twoLinks.latency e (twoLinks.load (fun _ => 0) e)
    ≤ ∑ e ∈ ({a} : Finset (Fin 2)),
      twoLinks.latency e (twoLinks.load (Function.update (fun _ => 0) i a) e)
  rw [Finset.sum_singleton, Finset.sum_singleton, h0, hu]
  fin_cases a <;> norm_num [twoLinks]

/-- The pure price of anarchy of `twoLinks` is `4/3 > 1`. -/
example : twoLinks.toCostGame.socialCost (fun _ => 0)
    = 4 / 3 * twoLinks.toCostGame.socialCost ![0, 1] := by
  rw [twoLinks_socialCost_zero, twoLinks_socialCost_split]
  norm_num

/-- The general bound applied to the instance. -/
example : twoLinks.toCostGame.socialCost (fun _ => 0)
    ≤ 5 / 2 * twoLinks.toCostGame.socialCost ![0, 1] :=
  twoLinks.socialCost_le_of_isPureNash twoLinks_hasAffineLatencies twoLinks_isPureNash _

/-- Rosenthal's theorem gives an equilibrium without computing one. -/
example : ∃ s, twoLinks.toCostGame.IsPureNash s := twoLinks.exists_isPureNash

example : twoLinks.toCostGame.HasFIP := twoLinks.hasFIP

/-- The robust bound for the equilibrium as a point mass. -/
example : (Convexity.StdSimplex.single (fun _ => (0 : Fin 2))).weights.sum
      (fun s w => w * twoLinks.toCostGame.socialCost s)
    ≤ 5 / 2 * twoLinks.toCostGame.socialCost ![0, 1] :=
  twoLinks.expected_socialCost_le twoLinks_hasAffineLatencies
    twoLinks_isPureNash.isCoarseCorrelatedEquilibrium _

/-- The costs of `twoLinks` are bounded by `2`. -/
theorem twoLinks_abs_cost_le (i : Fin 2) (s : Fin 2 → Fin 2) :
    |twoLinks.toCostGame.cost i s| ≤ 2 := by
  have hload : twoLinks.load s (s i) ≤ 2 :=
    (Finset.card_filter_le _ _).trans (by simp)
  rw [CongestionGame.toCostGame_cost]
  change |∑ e ∈ ({s i} : Finset (Fin 2)), twoLinks.latency e (twoLinks.load s e)| ≤ 2
  rw [Finset.sum_singleton]
  simp only [twoLinks]
  split_ifs
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hload
  · norm_num

/-- In the first round of Hedge dynamics both players split evenly. -/
example (M : ℝ) (T : ℕ) (i : Fin 2) (a : Fin 2) :
    twoLinks.toCostGame.hedgeProb M T 0 i a = 1 / 2 := by
  rw [CostGame.hedgeProb_zero, Fintype.card_fin, Nat.cast_ofNat]

/-- The price-of-anarchy bound for Hedge dynamics applies to `twoLinks` for every horizon `T ≥ 1`:
the time-averaged expected social cost is at most `5/2 · 3 + 12 √(ln 2 / T)`. -/
example (T : ℕ) (hT0 : 0 < T) :
    (timeAverage (twoLinks.toCostGame.hedgeDist 2 T) T hT0).weights.sum
        (fun s w => w * twoLinks.toCostGame.socialCost s)
      ≤ 5 / 2 * 3 + 12 * √(Real.log 2 / T) := by
  have hlog : Real.log 2 ≤ T := by
    have h1 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT0
    linarith
  have h := twoLinks.timeAverage_hedgeDist_socialCost_le twoLinks_hasAffineLatencies
    (by norm_num : (0 : ℝ) < 2) twoLinks_abs_cost_le hT0
    (fun _ => by rw [Fintype.card_fin, Nat.cast_ofNat]; exact hlog) ![0, 1]
  rw [twoLinks_socialCost_split] at h
  simp only [Fintype.card_fin, Nat.cast_ofNat, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  linarith

/-- A quadratic latency is not affine. -/
example : ¬ (⟨fun _ _ => {()}, fun _ k => (k : ℝ) ^ 2⟩ :
    CongestionGame (Fin 1) (fun _ => Unit) Unit).HasAffineLatencies := by
  rintro ⟨a, b, -, -, h⟩
  have h0 := h () 0
  have h1 := h () 1
  have h2 := h () 2
  norm_num at h0 h1 h2
  linarith

/-- The constant `5/2` is sharp: no `c < 5/2` bounds the pure price of anarchy of all affine
congestion games. -/
example (c : ℝ) (hc : c < 5 / 2) : ¬ ∀ (C : CongestionGame (Fin 3) (fun _ => Bool) (Fin 6))
    (s s' : Fin 3 → Bool), C.HasAffineLatencies → C.toCostGame.IsPureNash s →
      C.toCostGame.socialCost s ≤ c * C.toCostGame.socialCost s' := by
  intro h
  obtain ⟨C, s, s', hC, hs, hpos, heq⟩ := CongestionGame.exists_socialCost_eq_five_halves_mul
  have := h C s s' hC hs
  nlinarith

/-- Two parallel links with latencies `x` and `2 x` and three units of traffic. -/
def linear : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := 3
  latency e x := if e = 0 then x else 2 * x

theorem linear_pathLatency (f : Fin 2 → ℝ) (p : Fin 2) :
    linear.pathLatency f p = if p = 0 then f 0 else 2 * f 1 := by
  have hflow : ∀ e, linear.edgeFlow f e = f e := fun e => by
    simp [NonatomicCongestionGame.edgeFlow, linear, Finset.filter_eq]
  simp only [NonatomicCongestionGame.pathLatency, hflow]
  fin_cases p <;> simp [linear]

theorem linear_cost (f : Fin 2 → ℝ) : linear.cost f = f 0 * f 0 + f 1 * (2 * f 1) := by
  simp only [NonatomicCongestionGame.cost, linear_pathLatency]
  simp [Fin.sum_univ_two]

theorem linear_hasAffineLatencies : linear.HasAffineLatencies :=
  ⟨![1, 2], fun _ => 0, fun e => by fin_cases e <;> norm_num, fun _ => le_rfl,
    fun e x => by fin_cases e <;> simp [linear]⟩

theorem linear_isWardrop : linear.IsWardrop ![2, 1] := by
  refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun k => ?_⟩, fun p q _ _ => ?_⟩
  · norm_num [linear, Fin.sum_univ_two]
  · fin_cases p <;> fin_cases q <;> norm_num [linear_pathLatency]

/-- The flow `(3, 0)` is feasible but not a Wardrop equilibrium. -/
example : linear.IsFeasible ![3, 0] ∧ ¬ linear.IsWardrop ![3, 0] := by
  refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun k => ?_⟩, fun h => ?_⟩
  · norm_num [linear, Fin.sum_univ_two]
  · have := h.2 0 1 rfl (by norm_num)
    norm_num [linear_pathLatency] at this

/-- The Wardrop equilibrium is optimal here: by the `4/3` bound and directly. -/
example (g : Fin 2 → ℝ) (hg : linear.IsFeasible g) :
    linear.cost ![2, 1] ≤ 4 / 3 * linear.cost g :=
  linear_isWardrop.cost_le linear_hasAffineLatencies hg

example (g : Fin 2 → ℝ) (hg : linear.IsFeasible g) : linear.cost ![2, 1] ≤ linear.cost g := by
  have hsum := hg.2 ()
  simp only [linear] at hsum
  norm_num at hsum
  rw [linear_cost, linear_cost]
  norm_num
  nlinarith [sq_nonneg (g 1 - 1)]

/-- The constant `4/3` is sharp for selfish routing with affine latencies. -/
example (c : ℝ) (hc : c < 4 / 3) : ¬ ∀ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2))
    (f g : Fin 2 → ℝ), G.HasAffineLatencies → G.IsWardrop f → G.IsFeasible g →
      G.cost f ≤ c * G.cost g := by
  intro h
  obtain ⟨G, f, g, hG, hf, hg, hpos, heq⟩ := NonatomicCongestionGame.exists_cost_eq_four_thirds_mul
  have := h G f g hG hf hg
  nlinarith

end ComplexityTests.GameTheory.Congestion
