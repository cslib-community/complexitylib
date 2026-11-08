/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Sparse solutions of box-constrained linear equations

A nonempty intersection of a finite unit box with a linear fiber has a
mass-maximizing extreme point. Its strictly fractional columns are linearly
independent, so their number is at most the dimension of the equation space.
This is the finite linear-programming argument used in [XuGaoHu2027], Lemma 3.2.
-/

public section

open Set Filter

namespace Cslib

variable {ι d : Type*} [Fintype ι] [Fintype d]

omit [Fintype d] in
/-- A vertex of a box-constrained linear fiber has independent fractional columns. -/
theorem linearIndependent_fractional_of_extreme
    (a : ι → d → ℝ) (b : d → ℝ) (w : ι → ℝ)
    (hw : w ∈ ({u : ι → ℝ | (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧
      ∑ i, u i • a i = b}).extremePoints ℝ) :
    LinearIndependent ℝ (fun i : {i // 0 < w i ∧ w i < 1} => a i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let v : ι → ℝ := fun j => if hj : 0 < w j ∧ w j < 1 then c ⟨j, hj⟩ else 0
  have hv : ∑ j, v j • a j = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 < w j ∧ w j < 1)]
    have hz : (∑ j ∈ Finset.univ.filter (fun j => ¬ (0 < w j ∧ w j < 1)), v j • a j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [v, dite_eq_right hj, zero_smul]
    rw [hz, add_zero, Finset.sum_subtype _ (p := fun j => 0 < w j ∧ w j < 1) (by simp)]
    calc
      _ = ∑ j : {j // 0 < w j ∧ w j < 1}, c j • a j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show v j = c j from dite_eq_left j.property]
      _ = 0 := hc
  have hnear : ∀ᶠ t : ℝ in nhds 0, ∀ j, w j + t * v j ∈ Icc (0 : ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : 0 < w j ∧ w j < 1
    · have hcont : Continuous (fun t : ℝ => w j + t * v j) := by fun_prop
      have h : ∀ᶠ t : ℝ in nhds 0, w j + t * v j ∈ Ioo (0 : ℝ) 1 :=
        hcont.continuousAt (isOpen_Ioo.mem_nhds
          (show w j + 0 * v j ∈ Ioo (0 : ℝ) 1 by simpa using hj))
      exact h.mono fun _ ht => ⟨ht.1.le, ht.2.le⟩
    · filter_upwards [] with t
      simpa [v, hj] using hw.1.1 j
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let t := ε / 2
  have ht : 0 < t := half_pos hε
  have hplus : ∀ j, w j + t * v j ∈ Icc (0 : ℝ) 1 :=
    hball (by
      simp only [Real.dist_eq, sub_zero, t, abs_div, abs_of_pos hε,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)
  have hminus : ∀ j, w j - t * v j ∈ Icc (0 : ℝ) 1 := by
    have h := hball (y := -t) (by
      simp only [Real.dist_eq, sub_zero, t, abs_neg, abs_div, abs_of_pos hε,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)
    simpa only [neg_mul, ← sub_eq_add_neg] using h
  have hsum (r : ℝ) : ∑ j, (w j + r * v j) • a j = b := by
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hv,
      smul_zero, add_zero, hw.1.2]
  have heq : (fun j => w j + t * v j) = w := by
    apply hw.2 ⟨hplus, hsum t⟩ ⟨hminus, by simpa [sub_eq_add_neg] using hsum (-t)⟩
    refine ⟨(1 / 2 : ℝ), 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hci := congrFun heq i
  have hvi : v i = c i := dite_eq_left i.property
  rw [hvi] at hci
  nlinarith

/-- Maximize retained mass subject to finitely many linear equations and unit box
constraints. The optimizer has at most `d` strictly fractional coordinates. This
is an existence theorem, not a certified implementation of an LP solver. -/
theorem exists_sparse_box_solution (a : ι → d → ℝ) (w : ι → ℝ)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) :
    ∃ u : ι → ℝ, (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧
      (∑ i, u i • a i) = ∑ i, w i • a i ∧
      (∑ i, w i) ≤ ∑ i, u i ∧
      Fintype.card {i // 0 < u i ∧ u i < 1} ≤ Fintype.card d := by
  classical
  let P := {u : ι → ℝ | (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧
    ∑ i, u i • a i = ∑ i, w i • a i}
  have hP : IsCompact P := by
    have heq : P = Icc (0 : ι → ℝ) 1 ∩
        {u : ι → ℝ | ∑ i, u i • a i = ∑ i, w i • a i} := by
      ext u
      simp only [P, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def]
      aesop
    rw [heq]
    exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  let l : (ι → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
  have hl (u : ι → ℝ) : l u = ∑ i, u i := by simp [l]
  obtain ⟨v, hv, hmax⟩ := hP.exists_isMaxOn ⟨w, hw, rfl⟩ l.continuous.continuousOn
  let Q := {u ∈ P | ∀ z ∈ P, l z ≤ l u}
  have hexposed : IsExposed ℝ P Q := fun _ => ⟨l, rfl⟩
  obtain ⟨u, hu⟩ := (hexposed.isCompact hP).extremePoints_nonempty ⟨v, hv, hmax⟩
  have hue := hexposed.isExtreme.extremePoints_subset_extremePoints hu
  refine ⟨u, hue.1.1, hue.1.2, ?_, ?_⟩
  · simpa only [hl] using hu.1.2 w ⟨hw, rfl⟩
  · have hi := linearIndependent_fractional_of_extreme a (∑ i, w i • a i) u hue
    simpa using hi.fintype_card_le_finrank

end Cslib
