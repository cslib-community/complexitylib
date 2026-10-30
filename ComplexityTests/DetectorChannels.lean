/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for affine channels in the column detector
-/

namespace ComplexityTests.DetectorChannels

open Finset Matrix Cslib.Probability

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The affine channels on `𝔽₅` with `H = 2` and `a = 1 / 2`: rate `f = 1 / 4`, side
`L = ⌈5 / 2⌉ = 3`, retention probability `(3 / 5) ^ 2`. -/
private theorem channels :
    RetentionChannels (fun s (v : ZMod 5) => affineRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun s (v : ZMod 5) => affineRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v)) ((1 / 2) ^ 2)
      ((((⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ : ℕ) : ℝ) / (5 : ℕ)) ^ 2) 1 (2 ^ 2) (2 ^ 2) 4 :=
  retentionChannels_affineRetains Function.injective_id (by norm_num) (by norm_num)

-- With detector rank `J = 20`, the threshold `J / (4 C_π f) = 20 / (4 · 4 · (1 / 4)) = 5` is the
-- whole vertex set, so on `𝔽₅` no column is ever flagged, whatever the matrix.
example (G : Matrix (ZMod 5) (ZMod 5) ℝ) (y : ZMod 5) :
    columnDetector (fun s (v : ZMod 5) => affineRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun s (v : ZMod 5) => affineRetains 5 2 ⌈(5 : ℕ) * (1 / 2 : ℝ)⌉₊ s (id v))
      (fun t => min (max t 0) 1) (fun _ => 1) 20 1 ((1 / 2) ^ 2) G y ≤ 1 / 4 := by
  refine not_lt.mp fun h => ?_
  have := lt_card_of_lt_columnDetector channels (by norm_num)
    (fun t => le_min (le_max_right _ _) zero_le_one) (fun t => min_le_right _ _) (δ₀ := 0)
    (fun t ht => by rw [max_eq_right ht, min_eq_left zero_le_one]) (fun _ => le_rfl)
    (by norm_num) h
  have hcard : (#({x | 0 * (1 / 2) ^ 2 < G x y} : Finset (ZMod 5)) : ℝ) ≤ 5 := by
    exact_mod_cast (card_le_univ _).trans (by simp)
  norm_num at this hcard
  linarith

end ComplexityTests.DetectorChannels
