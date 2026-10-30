/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.PairwiseIndependentHash.RetentionChannel

/-!
# Retention channels over a prime field

A retention channel over `𝔽₅` with one coordinate and side `2` retains each identifier at rate
`2 / 5`. A direct count over its `25` seeds confirms the rate. Two independent channels retain two
given identifiers jointly at rate `(2 / 5) ^ 2`. Over `𝔽₇` in two coordinates, at target rate
`f = (1 / 2) ^ 2`, the channel properties hold with side `L = ⌈7 / 2⌉ = 4`.
-/

namespace ComplexityTests.RetentionChannel

open Cslib Cslib.Probability Finset

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- The box `{0, 1}` in `𝔽₅`, and the exact retention rate `2 / 5`.
example : #(retentionBox 5 1 2) = 2 := card_retentionBox (by norm_num)

example (y : ZMod 5) : dens {s | affineRetains 5 1 2 s y} = 2 / 5 := by
  rw [dens_affineRetains (by norm_num)]
  norm_num

-- A direct count: `10` of the `25` seeds `(A, b)` retain the identifier `3`.
example : #{s | affineRetains 5 1 2 s 3} = 10 := by decide

-- Two independent channels, on the product seed space, retain `3` in the first and `4` in the
-- second with probability `(2 / 5) * (2 / 5)`.
example : dens {z : (Matrix (Fin 1) (Fin 1) (ZMod 5) × (Fin 1 → ZMod 5)) ×
      (Matrix (Fin 1) (Fin 1) (ZMod 5) × (Fin 1 → ZMod 5)) |
      affineRetains 5 1 2 z.1 3 ∧ affineRetains 5 1 2 z.2 4} = 4 / 25 := by
  have h := dens_filter_fst_and_snd (fun s ↦ affineRetains 5 1 2 s 3)
    (fun s ↦ affineRetains 5 1 2 s 4)
  rw [dens_affineRetains (by norm_num), dens_affineRetains (by norm_num)] at h
  convert h using 1
  norm_num

-- At rate `f = (1 / 2) ^ 2` over `𝔽₇`, the side is `L = ⌈7 / 2⌉ = 4`, and the retention rate
-- `(4 / 7) ^ 2` lies within `[f, 4 f]`.
example : (1 / 2 : ℝ) ^ 2 ≤ ((4 : ℝ) / 7) ^ 2 ∧ ((4 : ℝ) / 7) ^ 2 ≤ 2 ^ 2 * (1 / 2 : ℝ) ^ 2 := by
  obtain ⟨-, hlo, hhi, -, -⟩ :=
    affineRetains_rates (P := 7) (H := 2) (a := 1 / 2) (by norm_num) (by norm_num)
  have hceil : ⌈((7 : ℕ) : ℝ) * (1 / 2)⌉₊ = 4 := by norm_num [Nat.ceil_eq_iff]
  rw [hceil] at hlo hhi
  push_cast at hlo hhi
  exact ⟨hlo, hhi⟩

end ComplexityTests.RetentionChannel
