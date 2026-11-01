/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.PairwiseIndependentHash.ConditionalAveraging
import Complexity.Foundations.Combinatorics.Expander.AffinePlane

/-!
# Frame-conditioned channels and conditional averaging

Frames over `𝔽₃` are counted directly, and a frame-conditioned channel over `𝔽₃` retains an
identifier at rate `2 / 3`, confirmed by a direct count of its six channels.

Over `𝔽₅` with side `L = 3`, the shear `g = [[1, 1], [0, 1]]` and translation `c = (1, 0)` move
the value `w = (2, 2)` to `g w + c = (5, 2)`. The unique valid wrap is `z = (-1, 0)`, and the
variant it selects is the affine move `(5, 2) mod 3 = (2, 2)`. The wrap `z = 0` fails the integer
test even though its variant also lands in the retention box (`5 mod 5 = 0`): the retention test
alone does not identify the move.

The conditional-averaging bound is applied to the affine-plane expander over `𝔽₃`, transported
to slice coordinates, which discharges its spectral hypothesis on every slice.
-/

namespace ComplexityTests.ConditionalAveraging

open Cslib Cslib.Probability Finset Matrix
open scoped BigOperators

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- The nonzero vectors of `𝔽₃ ^ 2` are its frames of length one.
example : Fintype.card (Frame 3 2 1) = 8 := by decide

-- Frame conditioning keeps the exact rate: `2 / 3` over `𝔽₃` with side `2`.
example (y : ZMod 3) : dens {A : FrameChannel 3 1 1 | A.eval y ∈ retentionBox 3 1 2} = 2 / 3 := by
  rw [dens_eval_mem_retentionBox le_rfl (by norm_num)]
  norm_num

-- A direct count: `4` of the `6` channels retain the identifier `2`.
example : #{A : FrameChannel 3 1 1 | A.eval 2 ∈ retentionBox 3 1 2} = 4 := by decide

/-- The shear `[[1, 1], [0, 1]]`. -/
private def shear : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

/-- A frame-conditioned channel over `𝔽₅` with value `(2, 2)` at `y = 1`. -/
private def chan : FrameChannel 5 2 1 :=
  (![1, 2], ⟨![![1, 0]], linearIndependent_unique_iff.2 (by decide)⟩)

example : chan.eval 1 = ![2, 2] := by decide

-- The valid wrap is `-⌊(5, 2) / 3⌋ = (-1, 0)`; it passes the integer test, and `0` does not.
example : wrap 3 shear ![1, 0] (chan.eval 1) = ![-1, 0] := by decide
example : IsValidWrap 3 shear ![1, 0] ![-1, 0] (chan.eval 1) := by decide
example : ¬ IsValidWrap 3 shear ![1, 0] 0 (chan.eval 1) := by decide

-- The valid variant gives the affine move `(5, 2) mod 3 = (2, 2)`.
example : (variantMove 3 shear ![1, 0] ![-1, 0] chan).eval 1 = ![2, 2] := by decide

-- The wrap `0` also lands in the retention box, at the wrong value `(0, 2)`.
example : (variantMove 3 shear ![1, 0] 0 chan).eval 1 = ![0, 2] := by decide
example : (variantMove 3 shear ![1, 0] 0 chan).eval 1 ∈ retentionBox 5 2 3 := by decide

-- Wraps of every side length lie in the box `|zᵢ| ≤ ∑ⱼ |gᵢⱼ| + |cᵢ|`.
example : |wrap 3 shear ![1, 0] (chan.eval 1) 0| ≤ 3 :=
  (abs_wrap_le shear ![1, 0] (by decide) 0).trans (by decide)

/-- With no frame coordinates, slice coordinates in `𝔽₃ ^ 2` are the affine plane over `𝔽₃`. -/
private def planeEquiv : Frame 5 2 0 × (Fin 2 → ZMod 3) ≃ ZMod 3 × ZMod 3 :=
  haveI : Unique (Frame 5 2 0) :=
    { default := ⟨![], linearIndependent_empty_type⟩
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  (Equiv.uniqueProd _ _).trans (finTwoArrowEquiv _)

-- Conditional averaging with the affine-plane gap `√(1 / 3)`: on the slice of every identifier,
-- `t` steps contract the conditional variance by `(1 / 3) ^ t`.
example (y : ZMod 5) (f : RetentionSlice 5 2 0 3 y → ℝ) (t : ℕ) :
    𝔼 A, (((sliceGraph 3 (by norm_num) y
        ((RotationMap.affinePlane (ZMod 3)).reindex planeEquiv.symm)).walk ^ t) f A -
          𝔼 B, f B) ^ 2 ≤ (1 / 3) ^ t * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  have hG : ((RotationMap.affinePlane (ZMod 3)).reindex planeEquiv.symm).spectralExpansion ≤
      Real.sqrt (1 / 3) := by
    rw [RotationMap.spectralExpansion_reindex]
    simpa using RotationMap.spectralExpansion_affinePlane_le (ZMod 3)
  have h := expect_walk_pow_sliceGraph_sub_expect_sq_le (by norm_num) _ hG y f t
  rwa [pow_mul, Real.sq_sqrt (by norm_num)] at h

end ComplexityTests.ConditionalAveraging
