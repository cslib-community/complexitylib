/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.InitialTests

/-! Tests for the initial parity tests of Lemma 6.1. -/

namespace ComplexityTests.InitialTests

open Finset Cslib Cslib.BitString

/-- Four strings of length three have weight at most one, within the bound `(3 + 1) ^ 1`. -/
example : #{w : Fin 3 → Bool | weight w ≤ 1} = 4 := by decide

example : #{w : Fin 3 → Bool | weight w ≤ 2} ≤ (3 + 1) ^ 2 := card_filter_weight_le_le 3 2

/-- With `n = 2` variables and `m = 2` clauses, there are at most six sparse initial tests, and
every nonzero violation vector passing them has at least one violated clause, as it must. -/
example : ∃ rows : List (Fin 2 → Bool), rows.length ≤ 6 ∧
    ∀ z : Fin 2 → Bool, z ≠ 0 → (∀ r ∈ rows, r ⬝ᵥ z = false) → 1 ≤ weight z := by
  obtain ⟨rows, hlen, -, hdist⟩ :=
    exists_initialTests (n := 2) (m := 2) (B := 1) (by norm_num) le_rfl (by norm_num)
  refine ⟨rows, by simpa using hlen, fun z hz hrows => ?_⟩
  have := hdist z hz hrows
  rcases Nat.eq_zero_or_pos (weight z) with h | h
  · rw [h, mul_zero] at this; omega
  · exact h

end ComplexityTests.InitialTests
