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
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import all Mathlib.Data.Finset.Defs -- Reduce the bounded quantifiers in kernel certificates.

/-!
# Lifted-plane ranges overestimate integral stability

Theorem 5.5 of [XuGaoHu2027], PDF p. 13 (printed p. 11): the twelve-point
instance has integral stability two but no feasible lifted-plane range with
fewer than three deletions. `range_witness` additionally supplies an exact
separating plane and a feasible nine-set, proving that the best range audit is
exactly three. This explicit plane certificate is an original addition.

The finite target and nonsingularity certificates use rational arithmetic.
The range obstruction quantifies over every real affine plane, via the
manuscript's affine dependence of the first five saddle lifts.
-/

public section

namespace Cslib.LeastSquares.RangeAudit

open Simple

/-- The twelve observations in the manuscript's order. -/
@[expose] def point (i : Fin 12) : ℚ × ℚ :=
  ![(2082/1000, 240/1000), (3235/1000, -14/1000), (189/1000, 1636/1000),
    (-4066/1000, 2816/1000), (6438/1000, -320/1000),
    (-1749/1000, -1697/1000), (-1757/1000, -1703/1000),
    (-1744/1000, -1692/1000), (-1739/1000, -1695/1000),
    (-1752/1000, -1702/1000), (-1730/1000, -1678/1000),
    (-1761/1000, -1678/1000)] i

/-- Retain all observations except the first and fifth. -/
@[expose] def retained : Finset (Fin 12) := Finset.univ.erase 0 |>.erase 4

/-- Exact centered cross-scatter. -/
@[expose] def scatter (s : Finset (Fin 12)) : ℚ :=
  crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep s) / s.card

/-- Exact mass-scaled regressor scatter; positivity excludes singular designs. -/
@[expose] def variance (s : Finset (Fin 12)) : ℚ :=
  xNumerator (fun i => (point i).1) (keep s)

/-- The actual slope-sign audit, with an intercept and nonsingularity. -/
@[expose] def Feasible (s : Finset (Fin 12)) : Prop :=
  0 < variance s ∧ scatter s ≤ 0

/-- The rational scatter test is equivalent to the nonsingular actual real OLS target.
The slope is the unique normal-equation slope, including an intercept. -/
theorem feasible_iff_real (s : Finset (Fin 12)) :
    Feasible s ↔
      0 < xNumerator (realVector (fun i => (point i).1)) (realVector (keep s)) ∧
      slope (realVector (fun i => (point i).1)) (realVector (fun i => (point i).2))
        (realVector (keep s)) ≤ 0 := by
  have hcard (hv : 0 < variance s) : (0 : ℚ) < s.card := by
    have hne : s ≠ ∅ := by
      intro he
      subst s
      norm_num [variance, xNumerator, crossNumerator, mass, keep] at hv
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hvar : xNumerator (realVector (fun i => (point i).1)) (realVector (keep s)) =
      ((variance s : ℚ) : ℝ) := xNumerator_realVector _ _
  have hcross : crossNumerator (realVector (fun i => (point i).1))
      (realVector (fun i => (point i).2)) (realVector (keep s)) =
      ((crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep s) : ℚ) : ℝ) :=
    crossNumerator_realVector _ _ _
  constructor
  · rintro ⟨hv, hc⟩
    have hv' : 0 < xNumerator (realVector (fun i => (point i).1))
        (realVector (keep s)) := by rw [hvar]; exact_mod_cast hv
    refine ⟨hv', (slope_nonpos_iff _ _ _ hv').mpr ?_⟩
    rw [hcross]
    have hc' : crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep s) ≤ 0 :=
      by simpa only [scatter, div_le_iff₀ (hcard hv), zero_mul] using hc
    exact_mod_cast hc'
  · rintro ⟨hv', hc⟩
    have hv : 0 < variance s := by rw [hvar] at hv'; exact_mod_cast hv'
    refine ⟨hv, ?_⟩
    have hc' := (slope_nonpos_iff _ _ _ hv').mp hc
    rw [hcross] at hc'
    have hnum : crossNumerator (fun i => (point i).1) (fun i => (point i).2) (keep s) ≤ 0 :=
      by exact_mod_cast hc'
    exact (div_le_iff₀ (hcard hv)).mpr (by simpa using hnum)

/-- Oriented volume of four saddle lifts. -/
@[expose] def volume (i j k l : Fin 12) : ℚ :=
  let x := fun t => (point t).1 - (point i).1
  let y := fun t => (point t).2 - (point i).2
  let z := fun t => (point t).1 * (point t).2 - (point i).1 * (point i).2
  x j * (y k * z l - z k * y l) - y j * (x k * z l - z k * x l) +
    z j * (x k * y l - y k * x l)

/-- The design satisfies both ordinary and lifted general position. -/
theorem general_position :
    (∀ i j, (point i).1 = (point j).1 → i = j) ∧
    (∀ i j k l, i < j → j < k → k < l → volume i j k l ≠ 0) := by
  decide +kernel

private theorem eleven_certificates :
    ∀ s ∈ (Finset.univ : Finset (Fin 12)).powersetCard 11, 0 < scatter s := by
  exact @of_decide_eq_true _ Finset.decidableDforallFinset (by decide +kernel)

private theorem ten_certificates :
    retained.card = 10 ∧ Feasible retained ∧
    (∀ s ∈ (Finset.univ : Finset (Fin 12)).powersetCard 10,
      scatter s ≤ 0 → s = retained) := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · unfold Feasible
    decide +kernel
  · exact @of_decide_eq_true _ Finset.decidableDforallFinset (by decide +kernel)

/-- All zero/one-deletion sets fail, and the unique feasible ten-set is `retained`. -/
theorem audit_certificates :
    scatter Finset.univ = 31413143/6000000 ∧
    (∀ s : Finset (Fin 12), 11 ≤ s.card → 0 < scatter s) ∧
    retained.card = 10 ∧ Feasible retained ∧
    (∀ s : Finset (Fin 12), s.card = 10 → scatter s ≤ 0 → s = retained) := by
  have hfull : scatter Finset.univ = 31413143/6000000 := by
    norm_num [scatter, crossNumerator, mass, keep, point, Fin.sum_univ_succ]
  refine ⟨hfull, ?_, ten_certificates.1, ten_certificates.2.1, ?_⟩
  · intro s hs
    by_cases heq : s.card = 12
    · have heq' : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using heq)
      rw [heq', hfull]
      norm_num
    · have hcard : s.card = 11 := by have := Finset.card_le_univ s; simp at this; omega
      exact eleven_certificates s (by simp [hcard])
  · intro s hs
    exact ten_certificates.2.2 s (by simp [hs])

/-- Evaluation of an arbitrary real plane on the saddle lift `(x,y,xy)`. -/
@[expose] noncomputable def planeValue (c : Fin 4 → ℝ) (i : Fin 12) : ℝ :=
  c 0 * ((point i).1 : ℝ) * ((point i).2 : ℝ) +
    c 1 * ((point i).1 : ℝ) + c 2 * ((point i).2 : ℝ) + c 3

/-- A strict lifted-plane range, allowing boundary points among excluded observations. -/
@[expose] def IsRange (s : Finset (Fin 12)) : Prop :=
  ∃ c : Fin 4 → ℝ, ∀ i, i ∈ s ↔ planeValue c i < 0

/-- Exact affine dependence given in the proof of Theorem 5.5. -/
theorem affine_dependence (c : Fin 4 → ℝ) :
    1842745643040 * planeValue c 0 - 2125100095440 * planeValue c 1 -
      191841337352 * planeValue c 2 - 2045687193 * planeValue c 3 +
      476241476945 * planeValue c 4 = 0 := by
  norm_num [planeValue, point]
  ring

/-- No real lifted plane selects the unique feasible ten-set. -/
theorem not_range : ¬ IsRange retained := by
  rintro ⟨c, hc⟩
  have h0 : 0 ≤ planeValue c 0 := le_of_not_gt fun h => by
    have := (hc 0).mpr h
    norm_num [retained] at this
  have h4 : 0 ≤ planeValue c 4 := le_of_not_gt fun h => by
    have := (hc 4).mpr h
    norm_num [retained] at this
  have h1 : planeValue c 1 < 0 := (hc 1).mp (by decide)
  have h2 : planeValue c 2 < 0 := (hc 2).mp (by decide)
  have h3 : planeValue c 3 < 0 := (hc 3).mp (by decide)
  have := affine_dependence c
  linarith

/-- Every feasible retained set needs at least two deletions. -/
theorem deletions_ge_two (s : Finset (Fin 12)) (hs : Feasible s) : 2 ≤ 12 - s.card := by
  by_contra h
  have hcard : 11 ≤ s.card := by omega
  have := audit_certificates.2.1 s hcard
  exact (not_lt_of_ge hs.2) this

/-- Every feasible range needs at least three deletions, including exhaustive range searches. -/
theorem range_deletions_ge_three (s : Finset (Fin 12)) (hs : Feasible s)
    (hr : IsRange s) : 3 ≤ 12 - s.card := by
  have htwo := deletions_ge_two s hs
  by_contra h
  have hcard : s.card = 10 := by omega
  have heq := audit_certificates.2.2.2.2 s hcard hs.2
  exact not_range (heq ▸ hr)

/-- An exact feasible range with three deletions, found independently of the manuscript. -/
@[expose] def rangeRetained : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 11}

/-- The three-deletion witness is nonsingular and reverses the slope. -/
theorem range_certificate : rangeRetained.card = 9 ∧ Feasible rangeRetained := by
  simp only [Feasible, scatter, variance, xNumerator, crossNumerator, mass, keep]
  decide +kernel

/-- A concrete real plane selects exactly the three-deletion witness. -/
theorem range_witness : IsRange rangeRetained := by
  refine ⟨![-1672435000000, -118286024000, -5403741271000, -4415259807429], ?_⟩
  intro i
  fin_cases i <;> norm_num [rangeRetained, planeValue, point]

/-- Complete audit endpoint: exact stability two, exact best lifted-range stability three. -/
theorem range_audit_gap :
    IsLeast {k : ℕ | ∃ s, Feasible s ∧ k = 12 - s.card} 2 ∧
    IsLeast {k : ℕ | ∃ s, Feasible s ∧ IsRange s ∧ k = 12 - s.card} 3 := by
  constructor
  · refine ⟨⟨retained, audit_certificates.2.2.2.1, ?_⟩, ?_⟩
    · rw [audit_certificates.2.2.1]
    · rintro k ⟨s, hs, rfl⟩
      exact deletions_ge_two s hs
  · refine ⟨⟨rangeRetained, range_certificate.2, range_witness, ?_⟩, ?_⟩
    · rw [range_certificate.1]
    · rintro k ⟨s, hs, hr, rfl⟩
      exact range_deletions_ge_three s hs hr

end Cslib.LeastSquares.RangeAudit
