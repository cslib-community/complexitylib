/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.Gaussian.CoefficientFiber

/-! Actual coefficient conditioning on the infinite lattice `2ℤ`, composite modulus six,
a nonzero residue, an off-lattice center, and rank-zero and dimension-zero lattices. -/

open Module ProbabilityTheory ZLattice
open scoped ENNReal Pointwise

noncomputable section

namespace ComplexityTests.DiscreteGaussianCoefficientFiber

private def twoBasis : Basis Unit ℝ ℝ :=
  (Basis.singleton Unit ℝ).isUnitSMul (fun _ ↦ (show (2 : ℝ) ≠ 0 by norm_num).isUnit)

private abbrev L : Submodule ℤ ℝ := Submodule.span ℤ (Set.range twoBasis)
private def b : Basis Unit ℤ L := twoBasis.restrictScalars ℤ
private abbrev H : Submodule ℤ ℝ := ((6 : ℕ) : ℝ) • L

private instance : DiscreteTopology H :=
  DiscreteTopology.of_subset (s := (L : Set ℝ)) (inferInstanceAs (DiscreteTopology ↥L))
    (natCast_smul_le L 6)

private theorem basis_value : ((b () : L) : ℝ) = 2 := by
  change ((twoBasis.restrictScalars ℤ) () : ℝ) = 2
  rw [Basis.restrictScalars_apply]
  rw [twoBasis, Basis.isUnitSMul_apply]
  simp

private theorem lift_one : (coefficientLift L b 6 (fun _ ↦ 1) : ℝ) = 2 := by
  change ((b.equivFun.symm (fun _ ↦ (1 : ℤ)) : L) : ℝ) = 2
  rw [Basis.equivFun_symm_apply]
  simp [basis_value]

example : Infinite L := by
  apply Infinite.of_injective (fun n : ℤ ↦ n • b ())
  intro m n h
  have hc := congrArg (fun z : L ↦ (z : ℝ)) h
  simpa [basis_value] using hc

-- The fiber contains the point 14: its integer coefficient is 7, congruent to 1 modulo 6.
example : coefficientMod L b 6 ((7 : ℤ) • b ()) = (fun _ ↦ 1) := by
  ext i
  cases i
  norm_num [coefficientMod]
  decide

-- Its representative is 2, and its scalar lattice is exactly the image under multiplication by 6.
example : (12 : ℝ) ∈ H := by
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  exact ⟨(b () : ℝ), (b ()).property, by norm_num [basis_value]⟩

example : (2 : ℝ) ∉ H := by
  have hz := (coefficientMod_eq_zero_iff L b 6 (b ())).symm
  rw [basis_value] at hz
  change ¬(2 : ℝ) ∈ (6 : ℝ) • L
  rw [← Nat.cast_ofNat (R := ℝ) (n := 6), hz]
  intro he
  have hc := congrFun he ()
  norm_num [coefficientMod] at hc
  exact (by decide : (1 : ZMod 6) ≠ 0) hc

example : (coefficientFiberEquiv L b 6 (fun _ ↦ 1) 0).val = b () := by
  apply Subtype.ext
  rw [coe_coefficientFiberEquiv, Submodule.coe_zero, zero_add, lift_one, basis_value]

-- Every residue really occurs; this is not a conditional theorem on an empty event.
example (a : Unit → ZMod 6) :
    0 < (discreteGaussian L 3 (by norm_num) (1 / 2)).map (coefficientMod L b 6) a :=
  map_coefficientMod_discreteGaussian_pos L b 6 3 (by norm_num) (1 / 2) a

-- The nonzero residue shifts the center from 1/2 to -3/2, with no extra index factor.
example : (discreteGaussian L 3 (by norm_num) (1 / 2)).map
    (coefficientMod L b 6) (fun _ ↦ 1) =
      ENNReal.ofReal (gaussianMass H 3 (-3 / 2)) /
        ENNReal.ofReal (gaussianMass L 3 (1 / 2)) := by
  simpa only [H, Nat.cast_ofNat, lift_one, show (1 / 2 : ℝ) - 2 = -3 / 2 by norm_num] using
    map_coefficientMod_discreteGaussian_apply L b 6 3 (by norm_num) (1 / 2) (fun _ ↦ 1)

example : (discreteGaussian L 3 (by norm_num) (1 / 2)).filter
    {v | coefficientMod L b 6 v = (fun _ ↦ 1)}
      ⟨coefficientLift L b 6 (fun _ ↦ 1), coefficientMod_coefficientLift L b 6 _, by simp⟩ =
    (discreteGaussian H 3 (by norm_num) (-3 / 2)).map
      (fun w ↦ Submodule.inclusion (natCast_smul_le L 6) w + b ()) := by
  have hu : coefficientLift L b 6 (fun _ ↦ 1) = b () := by
    apply Subtype.ext
    rw [lift_one, basis_value]
  simpa only [H, Nat.cast_ofNat, lift_one, hu, basis_value,
    show (1 / 2 : ℝ) - 2 = -3 / 2 by norm_num] using
    filter_coefficientMod_discreteGaussian L b 6 3 (by norm_num) (1 / 2) (fun _ ↦ 1)

example : (discreteGaussian L 3 (by norm_num) (1 / 2)).map
    (fun v ↦ (coefficientMod L b 6 v, v)) =
    ((discreteGaussian L 3 (by norm_num) (1 / 2)).map (coefficientMod L b 6)).bind
      (fun a ↦ (discreteGaussian H 3 (by norm_num) (1 / 2 - coefficientLift L b 6 a)).map
        (fun w ↦ (a, Submodule.inclusion (natCast_smul_le L 6) w + coefficientLift L b 6 a))) :=
  map_coefficientMod_pair_discreteGaussian L b 6 3 (by norm_num) (1 / 2)

private def zeroBasis : Basis Empty ℤ (⊥ : Submodule ℤ ℝ) := Basis.empty _

-- A rank-zero lattice with an off-lattice center still has a positive, certain residue.
example : (discreteGaussian (⊥ : Submodule ℤ ℝ) 3 (by norm_num) 5).map
    (coefficientMod ⊥ zeroBasis 6) = PMF.pure (fun i ↦ nomatch i) := by
  have hf : (coefficientMod (⊥ : Submodule ℤ ℝ) zeroBasis 6 :
      (⊥ : Submodule ℤ ℝ) → (Empty → ZMod 6)) =
        Function.const _ (fun i ↦ nomatch i) := Subsingleton.elim _ _
  rw [hf, PMF.map_const]

private abbrev ZeroSpace := Fin 0 → ℝ
private def emptyBasis : Basis Empty ℤ (⊥ : Submodule ℤ ZeroSpace) := Basis.empty _

-- The actual dimension-zero marginal is also the point mass, for every positive width.
example (r : ℝ) (hr : 0 < r) :
    (discreteGaussian (⊥ : Submodule ℤ ZeroSpace) r hr 0).map
      (coefficientMod ⊥ emptyBasis 6) = PMF.pure (fun i ↦ nomatch i) := by
  have hf : (coefficientMod (⊥ : Submodule ℤ ZeroSpace) emptyBasis 6 :
      (⊥ : Submodule ℤ ZeroSpace) → (Empty → ZMod 6)) =
        Function.const _ (fun i ↦ nomatch i) := Subsingleton.elim _ _
  rw [hf, PMF.map_const]

end ComplexityTests.DiscreteGaussianCoefficientFiber
