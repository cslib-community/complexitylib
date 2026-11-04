/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.BoxProduct
import Complexity.Probability.PairwiseIndependentHash.SliceGap

/-!
# The spectral gap of the affine walk on slice coordinates

Concrete affine moves on `Frame 5 3 1 × ZMod 4 ^ 3`, the action of a transvection on a vector, the
count of frames and generators, conditional averaging on the retention slices of `𝔽₅ ^ 3` with the
gap hypothesis discharged, a client deriving that the action is transitive, and the box product of
two affine walks over unrelated fields.
-/

namespace ComplexityTests.SliceGap

open Cslib Cslib.Probability Cslib.RotationMap Finset Matrix
open scoped BigOperators

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- A transvection adds `c` times one coordinate to another, over any ring.
example : ((SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (2 : ℤ) :
    Matrix (Fin 3) (Fin 3) ℤ) *ᵥ ![1, 5, -3]) = ![-5, 5, -3] := by
  rw [SpecialLinearGroup.transvection_mulVec]
  decide

/-- The frame of length one spanned by `(1, 0, 4)` in `𝔽₅ ^ 3`. -/
def F : Frame 5 3 1 := Frame.equivNeZero.symm ⟨![1, 0, 4], by decide⟩

-- `1 + E_02` adds the coordinate `2` to the coordinate `0`, on the frame modulo `5` and on the box
-- coordinate modulo `4`, wrapping around in both.
example : (affineMove 5 3 4 1 (.inl ⟨(0, 2), by decide⟩) (F, ![3, 1, 2])).1.1 0 = ![0, 0, 4] := by
  rw [affineMove_inl, Frame.mapSL_transvection_apply_zero]
  decide
example : (affineMove 5 3 4 1 (.inl ⟨(0, 2), by decide⟩) (F, ![3, 1, 2])).2 = ![1, 1, 2] := by
  rw [affineMove_inl]
  decide
-- A unit translation moves only the box coordinate.
example : affineMove 5 3 4 1 (.inr 0) (F, ![3, 1, 2]) = (F, ![0, 1, 2]) := by
  rw [affineMove_inr]
  decide

-- There are `5 ^ 3 - 1 = 124` frames of length one, and `3 ^ 2 = 9` generators.
example : Fintype.card (Frame 5 3 1) = 124 := Frame.card_one
example : Fintype.card ({p : Fin 3 × Fin 3 // p.1 ≠ p.2} ⊕ Fin 3) = 9 := by decide

/-- **Conditional averaging with every hypothesis discharged**: on the retention slice of every
identifier of `𝔽₅`, with side `3`, `t` steps of the lazy affine walk contract the conditional
variance by `(1 - 1 / 12607488) ^ (2 t)`. -/
example (y : ZMod 5) (f : RetentionSlice 5 3 1 3 y → ℝ) (t : ℕ) :
    𝔼 A, (((sliceGraph 3 (by norm_num) y (ofPerms (affineMove 5 3 3 1)).lazy).walk ^ t) f A -
      𝔼 B, f B) ^ 2 ≤ (1 - 1 / 12607488) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  have h := expect_walk_pow_sliceGraph_affineMove_sub_expect_sq_le le_rfl (by norm_num) y f t
  norm_num at h ⊢
  exact h

/-- **Transitivity from the gap**: for every prime `P` and side `L`, a real function on the slice
coordinates `Frame P 3 1 × ZMod L ^ 3` invariant under the affine moves is constant. -/
example (P L : ℕ) [Fact P.Prime] [NeZero L] (f : Frame P 3 1 × (Fin 3 → ZMod L) → ℝ)
    (hf : ∀ k p, f (affineMove P 3 L 1 k p) = f p) (p q : Frame P 3 1 × (Fin 3 → ZMod L)) :
    f p = f q := by
  have := Frame.nonempty (P := P) (H := 3) (r := 1) (by norm_num)
  set f₀ := fun p ↦ f p - 𝔼 q, f q
  have h := expect_sq_le_affineMove le_rfl f₀ (by simp [f₀, expect_sub_distrib])
  simp only [f₀, hf, sub_self] at h
  norm_num at h
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg fun p ↦ sq_nonneg (f p - 𝔼 q, f q)).1
    (le_antisymm h (expect_nonneg fun _ _ ↦ sq_nonneg _))
  have e (p) : f p = 𝔼 q, f q := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h0 p))
  rw [e p, e q]

/-- **Two components**: for all primes `P`, `P'` and sides `L`, `L'`, the lazy box product of the
affine walks of two channels has a uniform spectral gap, via `boxProdPerms`. -/
example (P P' L L' : ℕ) [Fact P.Prime] [Fact P'.Prime] [NeZero L] [NeZero L'] :
    (ofPerms (boxProdPerms (affineMove P 3 L 1) (affineMove P' 3 L' 1))).lazy.spectralExpansion ≤
      1 - 1 / 25214976 := by
  have : Nonempty ({p : Fin 3 × Fin 3 // p.1 ≠ p.2} ⊕ Fin 3) := ⟨.inr 0⟩
  refine (spectralExpansion_lazy_ofPerms_boxProdPerms_le _ _).trans ?_
  have h₁ := secondEigenvalue_ofPerms_affineMove_le (P := P) (L := L) le_rfl
  have h₂ := secondEigenvalue_ofPerms_affineMove_le (P := P') (L := L') le_rfl
  rw [card_affineGenerator_index]
  norm_num at h₁ h₂ ⊢
  have : 1 / 700416 ≤ min (9 * (1 - (ofPerms (affineMove P 3 L 1)).secondEigenvalue))
      (9 * (1 - (ofPerms (affineMove P' 3 L' 1)).secondEigenvalue)) :=
    le_min (by linarith) (by linarith)
  linarith

end ComplexityTests.SliceGap
