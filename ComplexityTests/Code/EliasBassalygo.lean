/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.EliasBassalygo

/-!
# Tests: the Elias–Bassalygo bound

For binary codes of length ten and minimum distance four, the Hamming bound at radius one gives
`|C| ≤ 1024 / 11`, that is at most `93` codewords. The q-ary Johnson radius allows radius two,
beyond half the minimum distance, where the Elias–Bassalygo bound gives `|C| 56 8 ≤ 1024 40`, that
is at most `91` codewords. The comparison is with the Hamming bound only: at these parameters the
shortened Plotkin bound gives the stronger `64` (`ComplexityTests/Code/Plotkin.lean`). The largest
such code has `40` codewords.
-/

namespace ComplexityTests.Code.EliasBassalygo

open Cslib Cslib.Code Finset

/-- For `q = 2`, `n = 10`, `d = 4` and `e = 2`, the radius is below the q-ary Johnson radius:
`q e ≤ (q - 1) n` and `(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`. -/
example (C : Finset (Fin 10 → Bool)) (hC : ((4 : ℕ) : ℕ∞) ≤ minDist (C : Set (Fin 10 → Bool))) :
    #C ≤ 91 := by
  have h := card_mul_sum_choose_mul_le hC (e := 2) (by decide)
  simp only [Fintype.card_bool, Fintype.card_fin] at h
  have hV : ∑ j ∈ range (2 + 1), (10).choose j * (2 - 1) ^ j = 56 := by decide
  rw [hV] at h
  omega

/-- The averaging step on its own: some Hamming ball of radius two holds at least
`|C| 56 / 1024` codewords. -/
example (C : Finset (Fin 10 → Bool)) :
    ∃ w : Fin 10 → Bool, #C * 56 ≤ 1024 * #{c ∈ C | hammingDist c w ≤ 2} := by
  obtain ⟨w, hw⟩ := exists_card_mul_sum_choose_le_pow_mul C 2
  simp only [Fintype.card_bool, Fintype.card_fin] at hw
  have hV : ∑ j ∈ range (2 + 1), (10).choose j * (2 - 1) ^ j = 56 := by decide
  rw [hV] at hw
  exact ⟨w, hw⟩

end ComplexityTests.Code.EliasBassalygo
