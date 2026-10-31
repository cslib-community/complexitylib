/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Analysis.Fourier.ZModProd
import Complexity.Foundations.Combinatorics.Expander.ShearTranslation
import Complexity.Foundations.Combinatorics.Expander.Mixing
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The shear-translation expander

Concrete rotations of the shear-translation graph, the Fourier transform at the zero frequency,
and clients of the uniform spectral gap: the Poincaré inequality applied to a concrete function,
and a lower bound on the edges leaving every vertex set, for every `n`.
-/

namespace ComplexityTests.ShearTranslationExpander

open Cslib Cslib.RotationMap Finset

-- The four forward moves at `(1, 2)` in `ZMod 5 × ZMod 5`, with their return labels.
example : (shearTranslation 5).rot ((1, 2), (0, false)) = ((3, 2), (0, true)) := by decide
example : (shearTranslation 5).rot ((1, 2), (1, false)) = ((1, 3), (1, true)) := by decide
example : (shearTranslation 5).rot ((1, 2), (2, false)) = ((2, 2), (2, true)) := by decide
example : (shearTranslation 5).rot ((1, 2), (3, false)) = ((1, 3), (3, true)) := by decide
-- The backward shear wraps around: `(1, 2) ↦ (1 - 2, 2) = (4, 2)`.
example : (shearTranslation 5).rot ((1, 2), (0, true)) = ((4, 2), (0, false)) := by decide

-- Iterated shears and their inverses.
example : shearFst (1 : ZMod 7) ^ 3 = shearFst 3 := by
  rw [shearFst_pow]
  norm_num
example : (shearSnd (2 : ZMod 7)).symm (3, 4) = (3, 5) := by decide

-- At the zero frequency the transform is the sum: here `5 * 5 = 25` ones.
example : ZMod.dftProd (fun _ : ZMod 5 × ZMod 5 ↦ (1 : ℂ)) 0 = 25 := by
  simp only [ZMod.dftProd_zero, sum_const, card_univ, Fintype.card_prod, ZMod.card]
  norm_num

/-- A sum-zero test function: `1` at `(0, 0)` and `-1` at `(1, 0)`. -/
private noncomputable def dipole (v : ZMod 3 × ZMod 3) : ℂ :=
  (if v = (0, 0) then 1 else 0) - (if v = (1, 0) then 1 else 0)

-- The Poincaré inequality applies to it: its hypothesis holds for this concrete function.
example : ∑ v, ‖dipole v‖ ^ 2 ≤
    512 * ∑ k, ∑ v, ‖dipole (shearTranslationMove 3 k v) - dipole v‖ ^ 2 :=
  sum_norm_sq_le_shearTranslation dipole (by simp [dipole, sum_sub_distrib])

-- The uniform gap bounds the edges leaving every vertex set, for every `n`.
example (n : ℕ) [NeZero n] (S : Finset (ZMod n × ZMod n)) :
    (1 - (1 - 1 / 4096) : ℝ) * Fintype.card (Fin 4 × Bool) * #S * #Sᶜ /
        Fintype.card (ZMod n × ZMod n) ≤ #((shearTranslation n).interedges S Sᶜ) := by
  refine (shearTranslation n).le_card_interedges_compl_of_expect_mul_walk_le (fun f hf ↦ ?_) S
  refine ((shearTranslation n).expect_mul_walk_le_secondEigenvalue_mul hf).trans ?_
  exact mul_le_mul_of_nonneg_right (secondEigenvalue_shearTranslation_le n)
    (expect_nonneg fun _ _ ↦ sq_nonneg _)

-- The lazy graph has the uniform spectral expansion bound on, for example, `ZMod 1000`.
example : (shearTranslation 1000).lazy.spectralExpansion < 1 :=
  (spectralExpansion_lazy_shearTranslation_le 1000).trans_lt (by norm_num)

end ComplexityTests.ShearTranslationExpander
