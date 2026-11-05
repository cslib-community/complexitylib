/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.Lattice.Schwartz
public import Complexity.Foundations.Probability.Gaussian.Periodization

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Lattice periodization examples

The clients include the infinite integer lattice, a two-dimensional skew basis, a nonzero
Schwartz bump, and a rank-zero lattice on an off-center compact interval. No full-rank or
orthogonal-basis hypothesis is needed by the convergence theorem.
-/

-- This regression module intentionally exports no declarations.
set_option linter.privateModule false

open Module ProbabilityTheory ZLattice TopologicalSpace
open scoped SchwartzMap

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

example : Continuous (gaussianMass integerLattice 1) :=
  continuous_gaussianMass _ _ (by norm_num)

example (K : Compacts ℝ) :
    Summable (fun z : integerLattice ↦
      ‖((⟨gaussianWeight 1, continuous_gaussianWeight 1⟩ : C(ℝ, ℝ)).comp
        (ContinuousMap.addRight (z : ℝ))).restrict K‖) :=
  summable_norm_restrict_gaussianWeight _ _ (by norm_num) K

example : Function.Periodic (fun x : ℝ ↦ ∑' z : integerLattice, gaussianWeight 1 (x + z)) 1 := by
  simpa [integerOne] using periodic_tsum_translate integerLattice (gaussianWeight 1) integerOne

private def skewEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.1 + x.2 / 2, x.2)
  invFun x := (x.1 - x.2 / 2, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> dsimp; ring
  map_smul' c x := by ext <;> dsimp; ring

private def skewBasis : Basis (Unit ⊕ Unit) ℝ (ℝ × ℝ) :=
  ((Basis.singleton Unit ℝ).prod (Basis.singleton Unit ℝ)).map skewEquiv

private abbrev skewLattice : Submodule ℤ (ℝ × ℝ) :=
  Submodule.span ℤ (Set.range skewBasis)

example : skewBasis (Sum.inl ()) = (1, 0) := by simp [skewBasis, skewEquiv]
example : skewBasis (Sum.inr ()) = (1 / 2, 1) := by simp [skewBasis, skewEquiv]

example : IsZLattice ℝ skewLattice := inferInstance
example : DiscreteTopology skewLattice := inferInstance

-- The Gaussian normalizer is continuous for a genuinely skew lattice in dimension two.
example : Continuous (gaussianMass skewLattice 2) :=
  continuous_gaussianMass _ _ (by norm_num)

example : 0 < gaussianMass skewLattice 2 (1 / 3, 1 / 4) :=
  gaussianMass_pos _ _ (by norm_num) _

private def bump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def schwartzBump : 𝓢(ℝ, ℝ) :=
  bump.hasCompactSupport.toSchwartzMap bump.contDiff

example : schwartzBump 0 = 1 := by
  exact bump.one_of_mem_closedBall (by simp [bump])

example : Continuous (fun x : ℝ ↦ ∑' z : integerLattice, schwartzBump (x + z)) :=
  schwartzBump.continuous_tsum_translate integerLattice

example : Continuous
    (QuotientAddGroup.automorphize schwartzBump : ℝ ⧸ integerLattice.toAddSubgroup → ℝ) :=
  schwartzBump.continuous_automorphize integerLattice

-- A compact interval far from zero and a rank-zero lattice are both allowed.
private def offCenterCompact : Compacts ℝ := ⟨Set.Icc 3 4, isCompact_Icc⟩

example :
    Summable (fun z : (⊥ : Submodule ℤ ℝ) ↦
      ‖((⟨gaussianWeight 2, continuous_gaussianWeight 2⟩ : C(ℝ, ℝ)).comp
        (ContinuousMap.addRight (z : ℝ))).restrict offCenterCompact‖) :=
  summable_norm_restrict_gaussianWeight _ _ (by norm_num) _

example : Continuous (gaussianMass (⊥ : Submodule ℤ ℝ) 2) :=
  continuous_gaussianMass _ _ (by norm_num)
