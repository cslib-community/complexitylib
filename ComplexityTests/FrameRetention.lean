/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Probability.PairwiseIndependentHash.FrameRetention
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for frame-conditioned retention estimates

The frame density is evaluated on small cases. Over `𝔽₃` with `H = r = 1`, frame conditioning
breaks pairwise independence: two identifiers are retained jointly with probability `1 / 3`,
not `(2 / 3) ^ 2`, but within the pair bound `(2 / 3) ^ 2 / q_fr = 2 / 3`. Finally the
frame-conditioned channels over `𝔽₅` drive the column detector.
-/

namespace ComplexityTests.FrameRetention

open Finset Matrix Cslib.Probability

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- Eight of the nine vectors of `𝔽₃ ^ 2` are frames of length one.
example : frameDensity 3 2 1 = 8 / 9 := by
  rw [frameDensity_eq_prod (by norm_num)]
  norm_num

-- `(9 - 1) (9 - 3) = 48` of the `81` pairs of vectors in `𝔽₃ ^ 2` are frames.
example : Fintype.card (Frame 3 2 2) = 48 := by
  rw [card_frame le_rfl]
  decide

-- Over `𝔽₃` with `H = 1`, the nonzero scalars are the frames: `q_fr = 2 / 3`.
private theorem frameDensity_three : frameDensity 3 1 1 = 2 / 3 := by
  rw [frameDensity_eq_prod le_rfl]
  norm_num

-- For `r < H`, the frame density is at least `1 / 2`, uniformly in the field.
example : 1 / 2 ≤ frameDensity 5 3 2 := one_div_two_le_frameDensity (by norm_num)

-- Under frame conditioning, only `a₀ = 0, F = 1` and `a₀ = 1, F = 2` retain both `0` and `1` in
-- the box `{0, 1}`: two of the six channels.
private theorem card_both :
    #{A : FrameChannel 3 1 1 | A.eval 0 ∈ retentionBox 3 1 2 ∧ A.eval 1 ∈ retentionBox 3 1 2} =
      2 := by
  decide

-- So the joint probability is `1 / 3`, which differs from `(2 / 3) ^ 2`: frame-conditioned
-- channels are not pairwise independent.
example :
    dens {A : FrameChannel 3 1 1 | A.eval 0 ∈ retentionBox 3 1 2 ∧ A.eval 1 ∈ retentionBox 3 1 2} =
      1 / 3 ∧ (1 / 3 : ℚ≥0) ≠ (2 / 3) ^ 2 := by
  refine ⟨?_, by norm_num⟩
  have hcard : Fintype.card (FrameChannel 3 1 1) = 6 := by decide
  rw [dens, card_both, hcard]
  norm_num

-- The pair bound `(2 / 3) ^ 2 / q_fr = 2 / 3` covers it.
example :
    (dens {A : FrameChannel 3 1 1 |
      A.eval 0 ∈ retentionBox 3 1 2 ∧ A.eval 1 ∈ retentionBox 3 1 2} : ℝ) ≤ 2 / 3 := by
  have h := dens_eval_mem_and_eval_mem_le (P := 3) (H := 1) (r := 1) (L₁ := 2) (L₂ := 2)
    (by norm_num) (by norm_num) (by norm_num) (w := 0) (y := 1) (by decide)
  rw [frameDensity_three] at h
  norm_num at h
  exact h

/-- Frame-conditioned channels on `𝔽₅` with `H = 2`, `r = 1` and `a = 1 / 2`: rate `f = 1 / 4`,
side `L = ⌈5 / 2⌉ = 3`, retention probability `(3 / 5) ^ 2`, and constants `C_pair = C_var = 8`. -/
private theorem channels :
    RetentionChannels
      (fun (s : FrameChannel 5 2 1) (v : ZMod 5) ↦
        frameRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun (s : FrameChannel 5 2 1) (v : ZMod 5) ↦
        frameRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v)) ((1 / 2) ^ 2)
      ((((⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ : ℕ) : ℝ) / (5 : ℕ)) ^ 2) 1 (2 ^ 2) (2 ^ (2 + 1)) 8 :=
  retentionChannels_frameRetains_of_lt Function.injective_id (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- With detector rank `J = 20`, the threshold `J / (4 C_π f) = 5` is the whole vertex set, so on
-- `𝔽₅` the frame-conditioned detector never flags a column, whatever the matrix.
example (G : Matrix (ZMod 5) (ZMod 5) ℝ) (y : ZMod 5) :
    columnDetector
      (fun (s : FrameChannel 5 2 1) (v : ZMod 5) ↦
        frameRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun (s : FrameChannel 5 2 1) (v : ZMod 5) ↦
        frameRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun t ↦ min (max t 0) 1) (fun _ ↦ 1) 20 1 ((1 / 2) ^ 2) G y ≤ 1 / 4 := by
  refine not_lt.mp fun h ↦ ?_
  have := lt_card_of_lt_columnDetector channels (by norm_num)
    (fun t ↦ le_min (le_max_right _ _) zero_le_one) (fun t ↦ min_le_right _ _) (δ₀ := 0)
    (fun t ht ↦ by rw [max_eq_right ht, min_eq_left zero_le_one]) (fun _ ↦ le_rfl)
    (by norm_num) h
  have hcard : (#({x | 0 * (1 / 2) ^ 2 < G x y} : Finset (ZMod 5)) : ℝ) ≤ 5 := by
    exact_mod_cast (card_le_univ _).trans (by simp)
  norm_num at this hcard
  linarith

end ComplexityTests.FrameRetention
