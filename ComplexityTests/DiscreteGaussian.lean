/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.Gaussian.DiscreteTail

/-!
# Discrete Gaussian examples

The integer lattice checks an infinite, nontrivial carrier with an off-lattice center. The
zero lattice checks that full rank is not required. Translation is checked as equality of PMFs.
The exponential moment and tail examples retain the actual ratio of lattice normalizers.
-/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Module ProbabilityTheory ZLattice

noncomputable section

private abbrev integerLattice : Submodule ℤ ℝ :=
  Submodule.span ℤ (Set.range (Basis.singleton Unit ℝ))

private def integerOne : integerLattice :=
  ⟨1, Submodule.subset_span ⟨(), Basis.singleton_apply _ _ _⟩⟩

example : Infinite integerLattice := by
  apply Infinite.of_injective (fun n : ℤ ↦ n • integerOne)
  intro m n h
  have := congrArg Subtype.val h
  simpa [integerOne] using this

example : 0 < gaussianMass integerLattice 1 (1 / 2) :=
  gaussianMass_pos _ _ (by norm_num) _

example : integerOne ∈ (discreteGaussian integerLattice 1 (by norm_num) (1 / 2)).support := by
  simp

example : gaussianWeight 1 (1 : ℝ) = Real.exp (-Real.pi) := by
  simp [gaussianWeight]

-- The width convention is Regev's exp(-π (x / s)²), not a variance parameter.
example (s x : ℝ) : gaussianWeight s x = Real.exp (-Real.pi * (x / s) ^ 2) := by
  simp only [gaussianWeight, Real.norm_eq_abs, sq_abs, div_pow, mul_div_assoc]

example : (discreteGaussian integerLattice 1 (by norm_num) 0).map (· + integerOne) =
    discreteGaussian integerLattice 1 (by norm_num) 1 := by
  simpa [integerOne] using map_add_discreteGaussian integerLattice 1 (by norm_num) 0 integerOne

-- A nontrivial lattice Gaussian is not the point mass at zero.
example : discreteGaussian integerLattice 1 (by norm_num) 0 ≠ PMF.pure 0 := by
  intro h
  have hmem : integerOne ∈ (discreteGaussian integerLattice 1 (by norm_num) 0).support := by
    simp
  rw [h, PMF.mem_support_pure_iff] at hmem
  have := congrArg Subtype.val hmem
  norm_num [integerOne] at this

example : 0 < gaussianMass (⊥ : Submodule ℤ ℝ) 2 3 :=
  gaussianMass_pos _ _ (by norm_num) _

example (s c : ℝ) : gaussianMass (⊥ : Submodule ℤ ℝ) s c = gaussianWeight s (-c) := by
  have hzero : (default : (⊥ : Submodule ℤ ℝ)) = 0 := Subsingleton.elim _ _
  simp [gaussianMass, hzero]

example : discreteGaussian (⊥ : Submodule ℤ ℝ) 2 (by norm_num) 3 = PMF.pure 0 := by
  ext z
  have hz : z = 0 := Subsingleton.elim _ _
  subst z
  rw [PMF.pure_apply_self, PMF.apply_eq_one_iff, support_discreteGaussian]
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨Set.mem_univ _, fun _ _ ↦ Subsingleton.elim _ _⟩

-- A finite exponential moment on the infinite integer lattice, with an off-lattice center.
example : Summable (fun z : integerLattice ↦
    (discreteGaussian integerLattice 1 (by norm_num) (1 / 2) z).toReal *
      Real.exp (Real.pi * (1 / 1 ^ 2 - 1 / 2 ^ 2) * ‖(z : ℝ) - 1 / 2‖ ^ 2)) :=
  summable_discreteGaussian_mul_exp integerLattice 1 (by norm_num) 2 (by norm_num) (1 / 2)

example : (∑' z : integerLattice,
    (discreteGaussian integerLattice 1 (by norm_num) (1 / 2) z).toReal *
      Real.exp (Real.pi * (1 / 1 ^ 2 - 1 / 2 ^ 2) * ‖(z : ℝ) - 1 / 2‖ ^ 2)) =
        gaussianMass integerLattice 2 (1 / 2) / gaussianMass integerLattice 1 (1 / 2) :=
  tsum_toReal_discreteGaussian_mul_exp integerLattice 1 (by norm_num) 2 (by norm_num) (1 / 2)

-- The coefficient of R² is positive, and at radius 2 the decay factor is exp(-3π).
example : 0 < Real.pi * (1 / (1 : ℝ) ^ 2 - 1 / 2 ^ 2) := by
  positivity

example : (discreteGaussian integerLattice 1 (by norm_num) (1 / 2)).toOuterMeasure
    {z : integerLattice | 2 ≤ ‖(z : ℝ) - 1 / 2‖} ≤
      ENNReal.ofReal (Real.exp (-3 * Real.pi) *
        (gaussianMass integerLattice 2 (1 / 2) / gaussianMass integerLattice 1 (1 / 2))) := by
  have hκ : -Real.pi * (1 / (1 : ℝ) ^ 2 - 1 / 2 ^ 2) * 2 ^ 2 = -3 * Real.pi := by ring
  simpa only [hκ] using discreteGaussian_norm_ge_le integerLattice 1 (by norm_num) 2
    (by norm_num) (1 / 2) 2 (by norm_num)

-- The boundary radius zero includes every point, even on a shifted zero lattice.
example : (discreteGaussian (⊥ : Submodule ℤ ℝ) 1 (by norm_num) 3).toOuterMeasure
    {z | 0 ≤ ‖(z : ℝ) - 3‖} = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro z _
  exact norm_nonneg _

-- Its only point lies at distance 3 from the center, so the strict exterior beyond 3 is empty.
example : (discreteGaussian (⊥ : Submodule ℤ ℝ) 1 (by norm_num) 3).toOuterMeasure
    {z | 3 ≤ ‖(z : ℝ) - 3‖} = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro z _
  have hz : z = 0 := Subsingleton.elim _ _
  norm_num [hz]

-- At that exact radius, the decay factor and the off-center normalizer ratio cancel.
example : Real.exp (-Real.pi * (1 / (1 : ℝ) ^ 2 - 1 / 2 ^ 2) * 3 ^ 2) *
    (gaussianMass (⊥ : Submodule ℤ ℝ) 2 3 / gaussianMass (⊥ : Submodule ℤ ℝ) 1 3) = 1 := by
  have hz : (default : (⊥ : Submodule ℤ ℝ)) = 0 := Subsingleton.elim _ _
  simp only [gaussianMass, tsum_fintype, Finset.univ_unique, Finset.sum_singleton, hz,
    Submodule.coe_zero, zero_sub, gaussianWeight]
  rw [← Real.exp_sub, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  norm_num
  ring

example : (discreteGaussian (⊥ : Submodule ℤ ℝ) 1 (by norm_num) 3).toOuterMeasure
    {z | 4 ≤ ‖(z : ℝ) - 3‖} = 0 := by
  have hempty : {z : (⊥ : Submodule ℤ ℝ) | 4 ≤ ‖(z : ℝ) - 3‖} = ∅ := by
    ext z
    have hz : z = 0 := Subsingleton.elim _ _
    norm_num [hz]
  rw [hempty, MeasureTheory.measure_empty]
