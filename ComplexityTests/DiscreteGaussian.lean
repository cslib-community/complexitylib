/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.Gaussian.Discrete

/-!
# Discrete Gaussian examples

The integer lattice checks an infinite, nontrivial carrier with an off-lattice center. The
zero lattice checks that full rank is not required. Translation is checked as equality of PMFs.
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
