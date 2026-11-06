/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Probability.Gaussian.CoefficientFiber
import Complexity.Foundations.Probability.Gaussian.Smoothing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! A composite-modulus Regev fixture with an actual smoothing bound on the scalar lattice.
The lattice and elementary exponential estimate follow the existing Gaussian regression tests.
-/

open Module ProbabilityTheory MeasureTheory ZLattice
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace ComplexityTests.RegevSample

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ ↦ (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L : Submodule ℤ ℝ := Submodule.span ℤ (Set.range twoBasis)
private def b : Basis Unit ℤ L := twoBasis.restrictScalars ℤ
private abbrev H : Submodule ℤ ℝ := (6 : ℝ) • L
private abbrev D := LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) H

private instance : DiscreteTopology H :=
  DiscreteTopology.of_subset (s := (L : Set ℝ)) (inferInstanceAs (DiscreteTopology ↥L))
    (natCast_smul_le L 6)

private instance : IsZLattice ℝ H := by
  constructor
  exact (congrArg (fun M : Submodule ℤ ℝ ↦ Submodule.span ℝ (M : Set ℝ))
    (ZSpan.smul twoBasis (by norm_num : (6 : ℝ) ≠ 0))).trans (ZSpan.span_top _)

private theorem basis_value : ((b () : L) : ℝ) = 2 := by
  change ((twoBasis.restrictScalars ℤ) () : ℝ) = 2
  rw [Basis.restrictScalars_apply, twoBasis, Basis.isUnitSMul_apply]
  simp

private theorem twelve_mem : (12 : ℝ) ∈ H := by
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  exact ⟨(b () : ℝ), (b ()).property, by norm_num [basis_value]⟩

private theorem dual_gap (w : D) (hw : w ≠ 0) : (1 / 12 : ℝ) ≤ ‖(w : ℝ)‖ := by
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (w.property 12 twelve_mem)
  have hk' : (k : ℝ) = (w : ℝ) * 12 := by
    simpa [real_inner_comm, mul_comm] using hk
  have hkn : k ≠ 0 := by
    intro h
    apply hw
    apply Subtype.ext
    change (w : ℝ) = 0
    rw [h, Int.cast_zero] at hk'
    linarith
  have ha : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hkn
  rw [hk', abs_mul] at ha
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 12)] at ha
  rw [Real.norm_eq_abs]
  linarith

private theorem half_mem_dual :
    (1 / 2 : ℝ) ∈ LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.mem_one.mpr
    exact ⟨1, by norm_num [twoBasis, Basis.isUnitSMul_apply]⟩
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [map_add] using add_mem hx' hy'
  | smul n x hx hx' => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ n hx'

private def w : LinearMap.BilinForm.dualSubmodule (innerₗ ℝ) L := ⟨1 / 2, half_mem_dual⟩

private theorem secret_pairing :
    LinearMap.BilinForm.dualSubmodulePairing (innerₗ ℝ) w (b ()) = 1 := by
  have h := LinearMap.BilinForm.dualSubmodulePairing_spec (innerₗ ℝ) w (b ())
  norm_num [basis_value, w, real_inner_comm] at h
  exact_mod_cast h

example : ((LinearMap.BilinForm.dualSubmodulePairing (innerₗ ℝ) w (b ()) : ℤ) : ZMod 6) = 1 := by
  rw [secret_pairing, Int.cast_one]

example : (13 / 24 : ℝ) ≠ (w : ℝ) := by norm_num [w]

private theorem residual_norm : ‖(13 / 24 : ℝ) - (w : ℝ)‖ = 1 / 24 := by
  norm_num [w, Real.norm_eq_abs]

private theorem residual_bound :
    ‖(13 / 24 : ℝ) - (w : ℝ)‖ ≤ (1 / 2 : ℝ) * 6 / (Real.sqrt 2 * 24) := by
  rw [residual_norm]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

private theorem beta_sq :
    ((24 : ℝ) * ‖(13 / 24 : ℝ) - (w : ℝ)‖ / 6) ^ 2 + (1 / 2) ^ 2 / 2 =
      11 / 72 := by rw [residual_norm]; norm_num

example : (11 / 72 : ℝ) ≤ (1 / 2) ^ 2 := by norm_num
example : (1 / 2 : ℝ) ^ 2 / (4 * Real.pi) = 1 / (16 * Real.pi) := by ring
example : (11 / 72 : ℝ) / (2 * Real.pi) = 11 / (144 * Real.pi) := by ring

private theorem width_bound : (2 : ℝ) * Real.exp (-3 * Real.pi / 2) ≤ 1 / 17 := by
  have hpi : 4 * Real.log 2 < Real.pi := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  have he := Real.exp_lt_exp.mpr
    (show -3 * Real.pi / 2 < -6 * Real.log 2 by linarith)
  have hr : Real.exp (-6 * Real.log 2) = (1 / 64 : ℝ) := by
    rw [show -6 * Real.log 2 = -((6 : ℕ) * Real.log 2) by ring, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hr] at he
  linarith

private theorem numerical_criterion :
    (2 : ℝ) ^ finrank ℝ ℝ * Real.exp
      (-3 * Real.pi * (24 / Real.sqrt 2) ^ 2 * (1 / 12) ^ 2 / 4) ≤
      (1 / 16 : ℝ) / (1 + 1 / 16) := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have he : -3 * Real.pi * (24 / Real.sqrt 2) ^ 2 * (1 / 12) ^ 2 / 4 =
      -3 * Real.pi / 2 := by rw [div_pow, hs2]; ring
  simpa only [he, finrank_self, pow_one,
    show (1 / 16 : ℝ) / (1 + 1 / 16) = 1 / 17 by norm_num] using width_bound

private theorem dual_small : gaussianMass D (1 / (24 / Real.sqrt 2)) 0 - 1 ≤ 1 / 16 :=
  gaussianMass_dual_sub_one_le_of_gap H (24 / Real.sqrt 2) (by positivity)
    (1 / 12) (by norm_num) dual_gap (1 / 16) (by norm_num) numerical_criterion

example : (4 : ℝ) * (1 / 16) + 2 * (1 / 16) / (1 - 1 / 16) = 23 / 60 := by norm_num
example : (23 / 60 : ℝ) ≤ 8 * (1 / 16) := by norm_num

private abbrev Point := EuclideanSpace ℝ (Fin 0)
private abbrev pointBasis := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
private abbrev pointLattice := Submodule.span ℤ (Set.range pointBasis)
private def pointIntegerBasis : Basis (Fin 0) ℤ pointLattice := pointBasis.restrictScalars ℤ
private abbrev pointScalarLattice : Submodule ℤ Point := (6 : ℝ) • pointLattice
private abbrev pointDual := LinearMap.BilinForm.dualSubmodule (innerₗ Point) pointScalarLattice

private instance : DiscreteTopology pointScalarLattice :=
  DiscreteTopology.of_subset (s := (pointLattice : Set Point))
    (inferInstanceAs (DiscreteTopology ↥pointLattice)) (natCast_smul_le pointLattice 6)

private instance : IsZLattice ℝ pointScalarLattice := ⟨Subsingleton.elim _ _⟩

-- In dimension zero the actual dual mass is exactly one, so the error parameter can be zero.
private theorem point_dual_mass (s : ℝ) : gaussianMass pointDual s 0 = 1 := by
  rw [gaussianMass, tsum_eq_single 0]
  · simp [gaussianWeight]
  · intro v hv
    exact (hv (Subsingleton.elim _ _)).elim

example (s : ℝ) : gaussianMass pointDual s 0 - 1 ≤ 0 := by rw [point_dual_mass]; norm_num

-- The zero residual keeps the source's alpha^2/2 target variance, not alpha^2.
example : ((24 : ℝ) * ‖(w : ℝ) - (w : ℝ)‖ / 6) ^ 2 + (1 / 2) ^ 2 / 2 = 1 / 8 := by
  norm_num

end ComplexityTests.RegevSample
