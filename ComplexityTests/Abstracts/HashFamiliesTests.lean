/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.HashFamiliesAbstract

/-!
# Formal Abstract Tests: High-Independence Word-RAM Hash Family

Non-vacuity and concrete evaluation checks for `ComplexityAbstracts.HashFamiliesAbstract`.
-/

namespace ComplexityTests.Abstracts.HashFamiliesTests

open scoped ENNReal
open ComplexityAbstracts.HashFamiliesAbstract

/-! ## Concrete Resource and Epoch Computations -/

lemma lt_pow_16 {N : ℕ} (hN : 4 < N) : 16 < 2 ^ N := by
  change 2 ^ 4 < 2 ^ N
  exact Nat.pow_lt_pow_right (by decide) hN

lemma lt_regimeThreshold_16 : 16 < regimeThreshold :=
  lt_pow_16 (by decide)

example : regimeThreshold = 2 ^ 320000 := rfl

example : chunkBits 16 = 1 := by decide

example : charBits 16 = 2 := by decide

example : trinomialStep 16 4 = 1 := by decide

example : trinomialDeg 16 4 = 6 := by decide

lemma space_4_16 : space 4 16 = 16 := by
  dsimp only [space]
  simp only [lt_regimeThreshold_16, ↓reduceIte]
  decide

example : evalTimeBound 4 = 444943 := by decide

lemma resampleTime_4_16 : resampleTime 4 16 = 33 := by
  rw [resampleTime_eq_of_lt lt_regimeThreshold_16]

lemma initTableSteps_16_16_4 : initTableSteps 16 16 4 = 186 := by
  dsimp only [initTableSteps]
  simp only [lt_regimeThreshold_16, ↓reduceIte]
  decide

lemma initFreshTime_4_16_16_4 : initFreshTime 4 16 16 4 = 220 := by
  dsimp only [initFreshTime]
  rw [initTableSteps_16_16_4, resampleTime_4_16]

lemma initClearTime_4_16_16_4 : initClearTime 4 16 16 4 = 290 := by
  dsimp only [initClearTime]
  rw [initFreshTime_4_16_16_4, space_4_16]

/-- Sample two-epoch operation sequence over `Fin 16` with at most `2` distinct keys per epoch. -/
def sampleOps : List (Op 16) :=
  [.eval ⟨1, by decide⟩, .eval ⟨5, by decide⟩, .eval ⟨1, by decide⟩,
   .resample,
   .eval ⟨3, by decide⟩, .eval ⟨7, by decide⟩]

example : epochCount sampleOps = 2 := rfl

lemma boundedEpochKeys_sampleOps : BoundedEpochKeys 4 sampleOps := by
  intro E hE
  simp only [sampleOps, epochKeys, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl <;> decide

example : failureProbBound 4 16 = 0 :=
  failureProbBound_eq_zero_of_lt lt_regimeThreshold_16

/-! ## Small-Capacity Regime Non-Vacuity (`n_max = 16 < 2 ^ 320000`) -/

/-- Initial register bank for `(k, n_max, U, M, base) = (4, 16, 16, 4, 100)`. -/
def testRegSmall : Fin 23 → ℕ
  | ⟨1, _⟩ => 16
  | ⟨2, _⟩ => 16
  | ⟨3, _⟩ => 4
  | ⟨22, _⟩ => 100
  | _ => 0

lemma wordBounded_testRegSmall : WordBounded 64 testRegSmall (fun _ => 0) := by
  refine ⟨fun i => ?_, fun _ => (by decide : 0 < 2 ^ 64)⟩
  fin_cases i <;> decide

/-- Non-vacuity of `highIndependenceHashFamily_fresh` in the small-capacity regime (`n_max = 16`):
produces `p_init`, `p_op`, initial distribution `ν₀`, and final distribution `ν_final` after
executing `sampleOps`, with exact `4`-wise independence (`failureProbBound 4 16 = 0`). -/
theorem nonvacuous_small_fresh :
    ∃ (p_init p_op : List (Instr 23)) (ν₀ ν_final : PMF (SeqState 16 16)),
      let s₀ : State 23 := ⟨0, testRegSmall, fun _ => 0⟩
      HaltsWithin 64 p_init s₀ 220 ∧
      expectedTime 64 p_init s₀ ≤ 220 ∧
      RunsOps 64 p_op 100 16 444943 33 sampleOps ν₀ ν_final ∧
      WhpKWiseContract 0 sampleOps (ν_final.map SeqState.transcript) := by
  have hU : 16 ≤ max 16 4 ^ 4 := by decide
  have hM : 4 ≤ 4 * Nat.clog 2 (max 16 4) + 5 := by decide
  have hw : 2 * trinomialDeg 16 4 ≤ 64 := by decide
  have hsp : 100 + space 4 16 < 2 ^ 64 := by
    rw [space_4_16]
    decide
  have hn : max 16 2 < 2 ^ 64 := by decide
  have hUfit : max 16 2 + 1 < 2 ^ 64 := by decide
  obtain ⟨p_init, p_op, hexec⟩ :=
    highIndependenceHashFamily_fresh 4 16 16 4 hU hM
  obtain ⟨ν₀, hhalts, hexp, _, _, hops⟩ :=
    hexec 64 100 hw hsp hn hUfit testRegSmall (fun _ => 0)
      wordBounded_testRegSmall rfl rfl rfl rfl (fun _ _ _ => rfl)
  obtain ⟨ν_final, hruns, hcontract⟩ := hops sampleOps
  have hcontract0 := hcontract boundedEpochKeys_sampleOps
  have hfp : failureProbBound 4 16 = 0 := failureProbBound_eq_zero_of_lt lt_regimeThreshold_16
  rw [hfp] at hcontract0
  rw [initFreshTime_4_16_16_4] at hhalts hexp
  rw [space_4_16, resampleTime_4_16] at hruns
  exact ⟨p_init, p_op, ν₀, ν_final, hhalts, hexp, hruns, hcontract0⟩

/-- Non-vacuity of `highIndependenceHashFamily_clear` on dirty initial memory `(fun a => a % 7)`. -/
theorem nonvacuous_small_clear :
    ∃ (p_initClear p_op : List (Instr 23)) (ν₀ ν_final : PMF (SeqState 16 16)),
      let s₀ : State 23 := ⟨0, testRegSmall, fun a => a % 7⟩
      HaltsWithin 64 p_initClear s₀ 290 ∧
      expectedTime 64 p_initClear s₀ ≤ 290 ∧
      RunsOps 64 p_op 100 16 444943 33 sampleOps ν₀ ν_final ∧
      WhpKWiseContract 0 sampleOps (ν_final.map SeqState.transcript) := by
  have hU : 16 ≤ max 16 4 ^ 4 := by decide
  have hM : 4 ≤ 4 * Nat.clog 2 (max 16 4) + 5 := by decide
  have hw : 2 * trinomialDeg 16 4 ≤ 64 := by decide
  have hsp : 100 + space 4 16 < 2 ^ 64 := by
    rw [space_4_16]
    decide
  have hn : max 16 2 < 2 ^ 64 := by decide
  have hUfit : max 16 2 + 1 < 2 ^ 64 := by decide
  have hbdd : WordBounded 64 testRegSmall (fun a => a % 7) := by
    refine ⟨wordBounded_testRegSmall.1, fun a => ?_⟩
    exact (Nat.mod_lt a (by decide)).trans (by decide)
  obtain ⟨p_initClear, p_op, hexec⟩ :=
    highIndependenceHashFamily_clear 4 16 16 4 hU hM
  obtain ⟨ν₀, hhalts, hexp, _, _, hops⟩ :=
    hexec 64 100 hw hsp hn hUfit testRegSmall (fun a => a % 7) hbdd rfl rfl rfl rfl
  obtain ⟨ν_final, hruns, hcontract⟩ := hops sampleOps
  have hcontract0 := hcontract boundedEpochKeys_sampleOps
  have hfp : failureProbBound 4 16 = 0 := failureProbBound_eq_zero_of_lt lt_regimeThreshold_16
  rw [hfp] at hcontract0
  rw [initClearTime_4_16_16_4] at hhalts hexp
  rw [space_4_16, resampleTime_4_16] at hruns
  exact ⟨p_initClear, p_op, ν₀, ν_final, hhalts, hexp, hruns, hcontract0⟩

/-! ## Large-Capacity Double-Tabulation Regime Non-Vacuity (`n_max = 2 ^ 320000`) -/

lemma le_pow_4 {N : ℕ} (hN : 2 ≤ N) : 4 ≤ 2 ^ N := by
  change 2 ^ 2 ≤ 2 ^ N
  exact Nat.pow_le_pow_right (by decide) hN

lemma clog_two_pow (N : ℕ) : Nat.clog 2 (2 ^ N) = N :=
  Nat.clog_pow 2 N (by decide)

lemma two_pow_le_two_pow {m n : ℕ} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by decide) h

/-- At `n_max = regimeThreshold = 2 ^ 320000`, `charBits n_max = 160000` and the non-triviality
condition `2 * codeBound 4 ≤ 2 ^ (3 * charBits regimeThreshold)` holds with a wide margin, so
`failureProbBound_le_inv_cube_of_ge` applies non-vacuously. -/
theorem nonvacuous_large_failureProbBound :
    failureProbBound 4 regimeThreshold ≤
      ((2 * (codeBound 4) ^ 2 : ℕ) : ℝ≥0∞) / ((max regimeThreshold 4 ^ 3 : ℕ) : ℝ≥0∞) := by
  apply failureProbBound_le_inv_cube_of_ge le_rfl
  have hle4 : 4 ≤ regimeThreshold := le_pow_4 (by decide)
  have hmax : max regimeThreshold 4 = regimeThreshold := max_eq_left hle4
  have hclog : Nat.clog 2 (max regimeThreshold 4) = 320000 := by
    rw [hmax]
    exact clog_two_pow 320000
  have hchar : charBits regimeThreshold = 160000 := by
    dsimp only [charBits]
    rw [hclog]
  rw [hchar]
  dsimp only [codeBound]
  have h16 : (2 * 8 : ℕ) = 2 ^ 4 := rfl
  have h32 : (8 * 4 : ℕ) = 2 ^ 5 := rfl
  have h64 : (64 : ℕ) = 2 ^ 6 := rfl
  rw [← mul_assoc, h16, h32, h64, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add]
  exact two_pow_le_two_pow (by decide)

end ComplexityTests.Abstracts.HashFamiliesTests
