/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Spread.Basic

/-!
# Nonnegative selector processes

A selector takes the supremum of coordinate sums over a family of nonnegative vectors. Extended
nonnegative values retain arbitrary (possibly unbounded or empty) vector families. Bounded real
families recover the source's real-valued supremum; the empty-family value here is zero.

## Main definitions

* `selectorProcess`: the set-indexed nonnegative selector supremum.
* `selectorMean`: its product-Bernoulli expectation.

## Main results

* `selectorProcess_mono`, `selectorProcess_union_le`: monotonicity and source subadditivity.
* `selectorProcess_singleton`: a single vector recovers its coordinate sum.
* `selectorMean_empty`: the empty vector family has zero selector expectation.

## References

[Talagrand2010Small], (5.16) and (7.1)–(7.2) (author PDF pp.5,8).
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators ENNReal
variable {ι : Type*} [DecidableEq ι]

/-- Supremum of selected coordinate sums, with arbitrary nonnegative vector family T. -/
noncomputable def selectorProcess (T : Set (ι → ℝ≥0∞)) (X : Finset ι) : ℝ≥0∞ :=
  ⨆ t ∈ T, ∑ i ∈ X, t i

/-- Finite product-Bernoulli expectation; it is a probability expectation for p in [0,1]. -/
noncomputable def selectorMean [Fintype ι] (p : ℝ) (T : Set (ι → ℝ≥0∞)) : ℝ≥0∞ :=
  ∑ x : ι → Bool, ENNReal.ofReal (BitString.bernoulliWeight p x) *
    selectorProcess T (univ.filter fun i => x i)

/-- The empty vector family has zero expectation, including at the boundary densities. -/
@[simp] theorem selectorMean_empty [Fintype ι] (p : ℝ) :
    selectorMean p (∅ : Set (ι → ℝ≥0∞)) = 0 := by
  simp [selectorMean, selectorProcess]

omit [DecidableEq ι] in
/-- Selecting more coordinates increases every nonnegative selector process. -/
theorem selectorProcess_mono (T : Set (ι → ℝ≥0∞)) : Monotone (selectorProcess T) := by
  intro X Y hXY
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact le_iSup_of_le t (le_iSup_of_le ht (sum_le_sum_of_subset hXY))

/-- Equation (7.2): a union's selector value is at most the sum of the two selector values. -/
theorem selectorProcess_union_le (T : Set (ι → ℝ≥0∞)) (X Y : Finset ι) :
    selectorProcess T (X ∪ Y) ≤ selectorProcess T X + selectorProcess T Y := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hu : (∑ i ∈ X ∪ Y, t i) ≤ (∑ i ∈ X, t i) + ∑ i ∈ Y, t i :=
    (le_self_add : (∑ i ∈ X ∪ Y, t i) ≤
      (∑ i ∈ X ∪ Y, t i) + ∑ i ∈ X ∩ Y, t i).trans sum_union_inter.le
  exact hu.trans (add_le_add
    (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    (le_iSup_of_le t (le_iSup_of_le ht le_rfl)))

omit [DecidableEq ι] in
/-- A singleton family has no optimization or measurability side condition. -/
@[simp] theorem selectorProcess_singleton (t : ι → ℝ≥0∞) (X : Finset ι) :
    selectorProcess {t} X = ∑ i ∈ X, t i := by simp [selectorProcess]

end Cslib.Probability.Spread
