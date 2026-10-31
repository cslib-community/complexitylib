/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Schedule

/-!
# Tests for the parameter schedule of the contraction recursion

Concrete values of the schedule at `s = 2 ^ 10`, an active call there, and a nonvacuity check of
the certificate: some root call satisfies `ActiveBounds`.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Schedule

open Cslib.Circuits.Frontier.ContractionSchedule

/-! ### Values at `s = 2 ^ 10`, where `⌊log₂ s⌋ = 10` and `⌊√10⌋ = 3` -/

theorem log_two_1024 : Nat.log 2 1024 = 10 := by
  rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, Nat.log_pow one_lt_two]

theorem sqrt_10 : Nat.sqrt 10 = 3 :=
  (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

example : leafSize 1024 = 341 := by
  rw [leafSize, log_two_1024, sqrt_10]

/-- `ε λ` is far below one at this size, so the taper and the labels are trivial. -/
example (d : ℕ) : taper 1024 d = 0 := by
  rw [taper, log_two_1024]
  exact Nat.div_eq_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos
    (Nat.le_add_right 17 d)))

example : degreeBound 1024 = 2 ^ 11 := by
  rw [degreeBound, log_two_1024]

example : precisionBound 3 1024 0 = 3072 := rfl

/-- One level adds `8 C s (4 · 2 ^ a_0 + a_0 + 1)` with `a_0 = 0`. -/
example : precisionBound 3 1024 1 = 3072 + 8 * 3 * 1024 * 5 := by
  have h : slotBits 1024 0 = 0 := by
    simp [slotBits, prefixBits, taper, log_two_1024]
  simp [precisionBound, h]

example : nodePrecision 5 2 3 7 1 = 5 + 8 * 2 * 4 + 8 * 7 * 4 := rfl

/-- `Δ ^ 10 ≥ s ^ 9` and `Δ ^ 10 ≤ 2 ^ 20 s ^ 9`. -/
example : 1024 ^ 9 ≤ degreeBound 1024 ^ 10 ∧ degreeBound 1024 ^ 10 ≤ 2 ^ 20 * 1024 ^ 9 :=
  ⟨pow_nine_le_degreeBound_pow_ten 1024, degreeBound_pow_ten_le (by norm_num)⟩

/-! ### Active calls -/

/-- A root call with `1000` edges and precision `5` at `s = 1024`, `C = 1`. -/
example : Active 1 1024 0 1000 5 :=
  Active.root (by norm_num) (by rw [show leafSize 1024 = 341 by
    rw [leafSize, log_two_1024, sqrt_10]]; norm_num) (by norm_num)

/-- A child with `62` edges is not active at `s = 1024`: it is a leaf. -/
example : ¬ Active 1 1024 1 62 5 := fun h => by
  have := h.leafSize_lt
  rw [show leafSize 1024 = 341 by rw [leafSize, log_two_1024, sqrt_10]] at this
  omega

/-- **The certificate is not vacuous**: for each `C ≥ 1` some root call satisfies
`ActiveBounds`. -/
example (C : ℕ) (hC : 1 ≤ C) : ∃ s M p, ActiveBounds C s 0 M p := by
  obtain ⟨s₀, h⟩ := exists_activeBounds C
  set s := max s₀ 16
  have hs : 16 ≤ s := le_max_right _ _
  have hlog : 4 ≤ Nat.log 2 s := Nat.le_log_of_pow_le one_lt_two (by simpa using hs)
  have hσ : 2 ≤ Nat.sqrt (Nat.log 2 s) := Nat.le_sqrt.2 (by omega)
  refine ⟨s, s, 0, (h s (le_max_left _ _)).2 0 s 0 (Active.root ?_ ?_ (Nat.zero_le _))⟩
  · exact Nat.le_mul_of_pos_left s hC
  · exact Nat.div_lt_self (by omega) (by omega)

/-- The excess exponents at `s = 1024` and `C = 1` over two levels. -/
example : ∑ d ∈ Finset.range 2, branchExponent 1 1024 d ≤ 245764 * (1024 / Nat.sqrt 10) := by
  have := sum_branchExponent_le 1 (s := 1024) (D := 2) (by norm_num)
    (by rw [log_two_1024]; norm_num)
  rwa [log_two_1024] at this

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.Schedule
