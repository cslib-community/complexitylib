/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.MeasureTheory.Measure.TotalVariation.Mixture
import CslibFrontier.Foundations.MeasureTheory.Measure.TotalVariation.Map
import CslibFrontier.Probability.PMF
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-! Full-L1 units, sharp unequal masses, empty and zero mixtures, and tagged conditional laws. -/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace ComplexityTests.TotalVariationMixture

private theorem atoms_distance : tvDist (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)) = 2 := by
  have h : Measure.dirac (0 : ℝ) ⟂ₘ Measure.dirac (1 : ℝ) :=
    ⟨{1}, measurableSet_singleton _, by simp, by simp⟩
  rw [tvDist_of_mutuallySingular h]
  norm_num

-- Binary subadditivity holds for extended and full-L1 total variation of finite measures.
example : tvDist (Measure.dirac (0 : ℝ) + Measure.dirac 1)
    (Measure.dirac 1 + Measure.dirac 0) ≤ 4 := by
  refine (tvDist_add_le _ _ _ _).trans ?_
  rw [atoms_distance, tvDist_comm (Measure.dirac 1), atoms_distance]
  norm_num

example (μ₁ μ₂ ν₁ ν₂ : Measure ℝ)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    etvDist (μ₁ + μ₂) (ν₁ + ν₂) ≤ etvDist μ₁ ν₁ + etvDist μ₂ ν₂ :=
  etvDist_add_le μ₁ μ₂ ν₁ ν₂

-- Common weights preserve the full-L1 factor of two, rather than half-distance units.
example : tvDist ((3 : ℝ≥0) • Measure.dirac (0 : ℝ))
    ((3 : ℝ≥0) • Measure.dirac (1 : ℝ)) = 6 := by
  rw [tvDist_nnreal_smul, atoms_distance]
  norm_num

-- The weight-change term is sharp, and the measures need not have equal total masses.
example : tvDist ((3 : ℝ≥0) • Measure.dirac (0 : ℝ))
    ((1 : ℝ≥0) • Measure.dirac (0 : ℝ)) = 2 := by
  rw [tvDist_nnreal_smul_same]
  norm_num

example : tvDist ((2 : ℝ≥0) • ((3 : ℝ≥0) • Measure.dirac (0 : ℝ)))
    ((1 : ℝ≥0) • ((3 : ℝ≥0) • Measure.dirac (0 : ℝ))) = 3 := by
  rw [tvDist_nnreal_smul_same]
  norm_num [Measure.real]

example (a b : ℝ≥0) : tvDist (a • (0 : Measure ℝ)) (b • 0) = 0 := by
  rw [tvDist_nnreal_smul_same]
  simp

example (μ ν : Fin 3 → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (a b : Fin 3 → ℝ≥0) :
    tvDist (∑ i ∈ (∅ : Finset (Fin 3)), a i • μ i)
      (∑ i ∈ (∅ : Finset (Fin 3)), b i • ν i) = 0 := by simp

-- The actual weighted-sum theorem allows unequal weights without a normalization premise.
example : tvDist (∑ _i : Fin 2, (3 : ℝ≥0) • Measure.dirac (0 : ℝ))
    (∑ _i : Fin 2, (1 : ℝ≥0) • Measure.dirac (0 : ℝ)) ≤ 4 := by
  have h := tvDist_finsetSum_smul_le (Finset.univ : Finset (Fin 2))
    (fun _ ↦ (3 : ℝ≥0)) (fun _ ↦ (1 : ℝ≥0))
    (fun _ ↦ Measure.dirac (0 : ℝ)) (fun _ ↦ Measure.dirac (0 : ℝ))
  convert h using 1; norm_num

-- A common-weight probability mixture of disjoint atoms has distance exactly two.
example : tvDist (∑ _i : Fin 2, (1 / 2 : ℝ≥0) • Measure.dirac (0 : ℝ))
    (∑ _i : Fin 2, (1 / 2 : ℝ≥0) • Measure.dirac (1 : ℝ)) = 2 := by
  simp only [Fin.sum_univ_two, ← add_smul]
  norm_num
  exact atoms_distance

-- This is the finite tagged-conditional shape used by the later Regev joint sample theorem.
-- Component error and residue-marginal error are separate, actual hypotheses here.
example (p q : PMF (Fin 6)) (μ ν : Fin 6 → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (ε δ : ℝ) (hcomponent : ∀ i, tvDist (μ i) (ν i) ≤ 4 * ε)
    (hweights : ∑ i, |(p i).toReal - (q i).toReal| ≤ δ) :
    tvDist
      (∑ i, (p i).toNNReal • (μ i).map (fun x ↦ (i, x)))
      (∑ i, (q i).toNNReal • (ν i).map (fun x ↦ (i, x))) ≤ 4 * ε + δ := by
  have hm (i : Fin 6) : Measurable (fun x : ℝ ↦ (i, x)) := by fun_prop
  apply (tvDist_finsetSum_smul_le Finset.univ (fun i ↦ (p i).toNNReal)
    (fun i ↦ (q i).toNNReal) (fun i ↦ (μ i).map (fun x ↦ (i, x)))
    (fun i ↦ (ν i).map (fun x ↦ (i, x)))).trans
  simp only [probReal_univ, mul_one, ENNReal.coe_toNNReal_eq_toReal,
    Finset.sum_add_distrib]
  have hc : ∑ i, (p i).toReal * tvDist ((μ i).map (fun x ↦ (i, x)))
      ((ν i).map (fun x ↦ (i, x))) ≤ 4 * ε := by
    calc
      _ ≤ ∑ i, (p i).toReal * (4 * ε) := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left ((tvDist_map_le (μ i) (ν i) (hm i)).trans (hcomponent i))
          ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.sum_mul, Cslib.Probability.PMF.sum_toReal, one_mul]
  exact add_le_add hc hweights

end ComplexityTests.TotalVariationMixture
