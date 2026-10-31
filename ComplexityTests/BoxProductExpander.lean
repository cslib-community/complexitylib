/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.BoxProduct
import Complexity.Foundations.Combinatorics.Expander.ShearTranslation

/-!
# Box products of permutation multigraphs

Concrete moves of a box product, the Poincaré inequality for the box product of two copies of the
two-point walk, and a uniform spectral gap for the box product of two shear-translation graphs of
unrelated sizes, with every hypothesis discharged.
-/

namespace ComplexityTests.BoxProductExpander

open Cslib Cslib.RotationMap Finset
open scoped BigOperators

-- A move of the first factor leaves the second coordinate alone, and vice versa.
example : boxProdPerms (shearTranslationMove 5) (shearTranslationMove 3) (.inl 0)
    ((1, 2), (2, 2)) = ((3, 2), (2, 2)) := by decide
example : boxProdPerms (shearTranslationMove 5) (shearTranslationMove 3) (.inr 1)
    ((1, 2), (2, 2)) = ((1, 2), (2, 1)) := by decide

/-- The flip of `ZMod 2`. -/
abbrev flip : Unit → Equiv.Perm (ZMod 2) := fun _ ↦ Equiv.addRight 1

/-- The two-point walk satisfies the Poincaré inequality with constant `4`, with equality. -/
theorem poincare_flip (f : ZMod 2 → ℝ) (hf : 𝔼 v, f v = 0) :
    4 * 𝔼 v, f v ^ 2 ≤ ∑ k, 𝔼 v, (f (flip k v) - f v) ^ 2 := by
  have hsum (g : ZMod 2 → ℝ) : ∑ v, g v = g 0 + g 1 := Fin.sum_univ_two g
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card, hsum, Fintype.univ_unit, sum_singleton,
    flip, Equiv.coe_addRight] at hf ⊢
  have h1 : f 1 = -f 0 := by linarith [(div_eq_zero_iff.1 hf).resolve_right (by norm_num)]
  have e1 : (1 : ZMod 2) + 1 = 0 := rfl
  rw [zero_add, e1, h1]
  nlinarith [sq_nonneg (f 0)]

/-- The square `ZMod 2 × ZMod 2`, the box product of two edges, inherits the constant `4`. -/
example (f : ZMod 2 × ZMod 2 → ℝ) (hf : 𝔼 p, f p = 0) :
    4 * 𝔼 p, f p ^ 2 ≤ ∑ k, 𝔼 p, (f (boxProdPerms flip flip k p) - f p) ^ 2 :=
  mul_expect_sq_le_boxProdPerms poincare_flip poincare_flip f hf

/-- **A uniform gap for a product of two components**: the lazy box product of the
shear-translation graphs on `ZMod n × ZMod n` and `ZMod m × ZMod m` has spectral expansion at most
`1 - 1 / 16384`, for all `n` and `m`. -/
example (n m : ℕ) [NeZero n] [NeZero m] :
    spectralExpansion
        (ofPerms (boxProdPerms (shearTranslationMove n) (shearTranslationMove m))).lazy ≤
      1 - 1 / 16384 := by
  have h := spectralExpansion_lazy_ofPerms_boxProdPerms_le (shearTranslationMove n)
    (shearTranslationMove m)
  have hn := secondEigenvalue_shearTranslation_le n
  have hm := secondEigenvalue_shearTranslation_le m
  rw [shearTranslation] at hn hm
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  have hmin : 4 * (1 / 4096 : ℝ) ≤
      min (4 * (1 - (ofPerms (shearTranslationMove n)).secondEigenvalue))
        (4 * (1 - (ofPerms (shearTranslationMove m)).secondEigenvalue)) :=
    le_min (by linarith) (by linarith)
  have : 4 * (1 / 4096 : ℝ) / (2 * (4 + 4)) ≤
      min (4 * (1 - (ofPerms (shearTranslationMove n)).secondEigenvalue))
        (4 * (1 - (ofPerms (shearTranslationMove m)).secondEigenvalue)) / (2 * (4 + 4)) := by
    gcongr
  norm_num at this ⊢
  linarith

end ComplexityTests.BoxProductExpander
