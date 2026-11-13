/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Probability.BilinearFingerprint

/-!
# Ordinary-import clients of the bilinear fingerprint bound

Rectangular matrices, sharpness in characteristic two, zero matrices and empty dimensions.
-/

set_option linter.privateModule false

open Cslib.Probability
open scoped Matrix ENNReal

namespace CslibFrontierTests.BilinearFingerprint

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A rectangular nonzero matrix over the source's prime field.
example :
    (1 - (5 : ℝ≥0∞)⁻¹) ^ 2 ≤
      (PMF.uniformOfFintype ((Fin 3 → ZMod 5) × (Fin 2 → ZMod 5))).toOuterMeasure
        {p | ∑ i, p.2 i * ((!![1, 0, 0; 0, 0, 0] : Matrix (Fin 2) (Fin 3) (ZMod 5))
          *ᵥ p.1) i ≠ 0} := by
  apply toOuterMeasure_bilinear_zmod_ne_zero_ge
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num at this

-- The sharp lower bound is attained in characteristic two.
example :
    (PMF.uniformOfFintype ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 2))).toOuterMeasure
        {p | ∑ i, p.2 i *
          (Matrix.vecMulVec (![1, 0] : Fin 2 → ZMod 2) ![0, 1, 0] *ᵥ p.1) i ≠ 0} =
      (1 - (2 : ℝ≥0∞)⁻¹) ^ 2 := by
  have hu : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hv : (![0, 1, 0] : Fin 3 → ZMod 2) ≠ 0 := by decide
  simpa only [ZMod.card, Nat.cast_ofNat] using toOuterMeasure_bilinear_vecMulVec hu hv

-- Dropping the nonzero-matrix hypothesis would be false.
example :
    (PMF.uniformOfFintype ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 2))).toOuterMeasure
        {p | ∑ i, p.2 i * ((0 : Matrix (Fin 2) (Fin 3) (ZMod 2)) *ᵥ p.1) i ≠ 0} = 0 := by
  simp

example (M : Matrix Empty (Fin 3) (ZMod 2)) : M = 0 := by
  ext i
  exact i.elim

example (M : Matrix (Fin 2) Empty (ZMod 2)) : M = 0 := by
  ext i j
  exact j.elim

end CslibFrontierTests.BilinearFingerprint
