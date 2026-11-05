/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Rational
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The sharp ten-point rounding gap

Proposition 3.6 of [XuGaoHu2027], PDF pp. 7–8 (printed pp. 5–6).
The ten observations have distinct regressors. Every deletion of at most one
observation leaves a positive slope; deleting the final two reverses it.
A concrete rational witness retaining weight `5101/10000` on each of the last
two points gives deleted mass `4899/5000 < 0.98` and a negative slope.
This strengthens the manuscript's weight `51/100` witness by making its
continuity argument explicit. `fractionalStability` takes the infimum over
all feasible **real** weights, not just rational certificates.

The slope includes an intercept and is certified by the weighted normal equations
in `Simple.normal_equations`. Positivity of regressor scatter is required in
both the fractional and integral feasible sets; the target is an inequality.
-/

public section

namespace Cslib.LeastSquares.SharpGap

open Simple

/-- The ten rational observations, with the anti-monotone eight-point backbone first. -/
@[expose] def point (i : Fin 10) : ℚ × ℚ :=
  ![(1/2, -1/2), (-1/2, 1/2), (1, -1), (-1, 1),
    (3/2, -3/2), (-3/2, 3/2), (2, -2), (-2, 2), (13/2, 13/5), (13/5, 13/2)] i

/-- Delete exactly the final two points. -/
@[expose] def retained : Finset (Fin 10) := Finset.univ.erase 8 |>.erase 9

/-- A rational feasible fractional witness strictly better than deleted mass `0.98`. -/
@[expose] def witness (i : Fin 10) : ℚ := if i < 8 then 1 else 5101/10000

/-- Distinct regressors give general position for simple regression with an intercept. -/
theorem general_position : ∀ i j, (point i).1 = (point j).1 → i = j := by
  decide +kernel

/-- Kernel-checked exact certificates for all zero- and one-deletion sets and the two-deletion
witness. The variance condition is checked independently of the target. -/
theorem integral_certificates :
    (∀ s : Finset (Fin 10), 9 ≤ s.card →
      0 < crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep s) ∧
      0 < xNumerator (fun i => (point i).1) (keep s)) ∧
    retained.card = 8 ∧
    crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep retained) = -120 ∧
    xNumerator (fun i => (point i).1) (keep retained) = 120 := by
  decide +kernel

/-- The strict fractional witness, including its weight bounds, actual mass and nonsingularity. -/
theorem fractional_certificate :
    (∀ i, witness i ∈ Set.Icc (0 : ℚ) 1) ∧
    10 - mass witness = 4899/5000 ∧
    crossNumerator (fun i => (point i).1) (fun i => (point i).2) witness < 0 ∧
    0 < xNumerator (fun i => (point i).1) witness := by
  decide +kernel

/-- Real regressors for the ten-point instance. -/
@[expose] def x : Fin 10 → ℝ := realVector (fun i => (point i).1)

/-- Real responses for the ten-point instance. -/
@[expose] def y : Fin 10 → ℝ := realVector (fun i => (point i).2)

/-- Real fractional feasibility, requiring a well-defined regression and an inequality target. -/
@[expose] def Feasible (w : Fin 10 → ℝ) : Prop :=
  (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) ∧ 0 < xNumerator x w ∧ slope x y w ≤ 0

/-- Infimum of deleted mass over all feasible real reweightings. -/
@[expose] noncomputable def fractionalStability : ℝ :=
  sInf {r : ℝ | ∃ w, Feasible w ∧ r = 10 - mass w}

/-- The fractional witness is feasible for actual real least squares. -/
theorem witness_feasible : Feasible (realVector witness) := by
  have hv : 0 < xNumerator x (realVector witness) := by
    rw [x, xNumerator_realVector]
    exact_mod_cast fractional_certificate.2.2.2
  refine ⟨?_, hv, (slope_nonpos_iff x y _ hv).mpr ?_⟩
  · intro i
    change (0 : ℝ) ≤ (witness i : ℝ) ∧ (witness i : ℝ) ≤ 1
    exact_mod_cast fractional_certificate.1 i
  · rw [x, y, crossNumerator_realVector]
    exact_mod_cast fractional_certificate.2.2.1.le

/-- The paper's strict fractional upper bound, with a concrete stronger rational bound. -/
theorem fractionalStability_lt : fractionalStability ≤ 4899/5000 ∧
    fractionalStability < 98/100 := by
  have hmass : 10 - mass (realVector witness) = (4899/5000 : ℝ) := by
    rw [mass_realVector]
    rw [show (mass witness : ℚ) = 10 - 4899/5000 by linarith [fractional_certificate.2.1]]
    norm_num
  have hbound : BddBelow {r : ℝ | ∃ w, Feasible w ∧ r = 10 - mass w} := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, hw, rfl⟩
    have hs : mass w ≤ (10 : ℝ) := by
      calc
        mass w ≤ ∑ _i : Fin 10, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hw.1 i).2
        _ = 10 := by simp
    linarith
  have hle : fractionalStability ≤ 4899/5000 :=
    csInf_le hbound ⟨realVector witness, witness_feasible, hmass.symm⟩
  exact ⟨hle, lt_of_le_of_lt hle (by norm_num)⟩

/-- Exact integral stability: two deletions are feasible and every feasible integral
regression deletes at least two observations. This quantifies over every retained set. -/
theorem integralStability_eq_two :
    Feasible (realVector (keep retained)) ∧ 10 - retained.card = 2 ∧
    ∀ s : Finset (Fin 10), Feasible (realVector (keep s)) → 2 ≤ 10 - s.card := by
  have hv : 0 < xNumerator x (realVector (keep retained)) := by
    rw [x, xNumerator_realVector, integral_certificates.2.2.2]
    norm_num
  refine ⟨⟨?_, hv, (slope_nonpos_iff x y _ hv).mpr ?_⟩, ?_, ?_⟩
  · intro i
    simp only [realVector, keep]
    split <;> norm_num
  · rw [x, y, crossNumerator_realVector, integral_certificates.2.2.1]
    norm_num
  · rw [integral_certificates.2.1]
  · intro s hs
    by_contra h
    have hcard : 9 ≤ s.card := by omega
    have hc : 0 < crossNumerator x y (realVector (keep s)) := by
      rw [x, y, crossNumerator_realVector]
      exact_mod_cast (integral_certificates.1 s hcard).1
    have := (slope_nonpos_iff x y _ hs.2.1).mp hs.2.2
    linarith

/-- The full-data real regression has positive slope, so this is a sign-reversal audit. -/
theorem initial_slope_pos : 0 < slope x y (realVector (keep Finset.univ)) := by
  have hc := integral_certificates.1 Finset.univ (by decide)
  have hv : 0 < xNumerator x (realVector (keep Finset.univ)) := by
    rw [x, xNumerator_realVector]
    exact_mod_cast hc.2
  apply div_pos ?_ hv
  rw [x, y, crossNumerator_realVector]
  exact_mod_cast hc.1

/-- Proposition 3.6: a positive full-data slope, fractional stability below `0.98`,
and exact integral stability two, all for the actual real regression. -/
theorem sharp_gap :
    0 < slope x y (realVector (keep Finset.univ)) ∧ fractionalStability < 98/100 ∧
    IsLeast {k : ℕ | ∃ s : Finset (Fin 10),
      Feasible (realVector (keep s)) ∧ k = 10 - s.card} 2 := by
  refine ⟨initial_slope_pos, fractionalStability_lt.2, ?_⟩
  refine ⟨⟨retained, integralStability_eq_two.1, integralStability_eq_two.2.1.symm⟩, ?_⟩
  rintro k ⟨s, hs, rfl⟩
  exact integralStability_eq_two.2.2 s hs

end Cslib.LeastSquares.SharpGap
