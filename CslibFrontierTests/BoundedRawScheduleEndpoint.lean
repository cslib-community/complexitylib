/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.BoundedRawScheduleEndpoint

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.BoundedRawScheduleEndpoint

private def stationary : MultiTapePTM.Schedule 1 2 := fun _ _ => 0

private theorem raw_stationary : RawScheduleEndpoint.word stationary =
    [false, false, false, false, false, false, false, false] := by decide

private theorem column_stationary : RelativeScanSchedule.column stationary 0 = [0, 0] := by decide

/- A valid query returns both validity and success, a binary endpoint, and the signed marker.
The prior output and all eight raw bits survive extraction and both native scans. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (RawScheduleEndpoint.initialConfig [true]
      [false, false, false, false, false, false, false, false] [] [false])
    (tapesCfg [true] ![[false, false, false, false], [true, true, true], [true],
      [false, false, false, false, false, false, false, false], []]
      0 ![0, 1, 0, 0, 0] [false, true, true]) 118 595 := by
  have hr : RelativeScanSchedule.result stationary 0 0 1 = ⟨1, 0, true⟩ := by decide
  have hb : Nat.bits 1 = [true] := by decide
  simpa [finalConfig, RawScheduleEndpoint.finalConfig, raw_stationary, column_stationary, hr,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive, hb] using
    runsBetween [true] [false] stationary 0 1 0

/- Querying the last interval is valid but exhausted; [true,false] differs from an invalid
interval's one-bit [false] output. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (RawScheduleEndpoint.initialConfig []
      [false, false, false, false, false, false, false, false] [true] [])
    (tapesCfg [] ![[false, false, false, false], [true, true, true], [false, true],
      [false, false, false, false, false, false, false, false], []]
      0 ![0, 1, 0, 0, 0] [true, false]) 123 620 := by
  have hr : RelativeScanSchedule.result stationary 1 0 1 = ⟨2, 0, false⟩ := by decide
  have hb₁ : Nat.bits 1 = [true] := by decide
  have hb₂ : Nat.bits 2 = [false, true] := by decide
  simpa [finalConfig, RawScheduleEndpoint.finalConfig, raw_stationary, column_stationary, hr,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive, hb₁, hb₂] using
    runsBetween [] [] stationary 0 1 1

/- At EOF the endpoint scanner is skipped: there is no marker or returned index and the source
head remains at cell four. The binary request word has nevertheless been completely erased. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (RawScheduleEndpoint.initialConfig []
      [false, false, false, false, false, false, false, false] [false, true] [])
    (tapesCfg [] ![[false, false, false, false], [], [],
      [false, false, false, false, false, false, false, false], []]
      0 ![4, 0, 0, 0, 0] [false]) 128 645 := by
  have hb : Nat.bits 2 = [false, true] := by decide
  simpa [finalConfig, raw_stationary, column_stationary, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb] using
    runsBetween [] [] stationary 0 1 2

/- Even an enormous canonical binary index is rejected with a source-length plus bit-width
clock. This includes extraction and the physical branch that skips the endpoint scanner. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (RawScheduleEndpoint.initialConfig []
      [false, false, false, false, false, false, false, false] (Nat.bits (2 ^ 128)) [])
    (tapesCfg [] ![[false, false, false, false], [], [],
      [false, false, false, false, false, false, false, false], []]
      0 ![4, 0, 0, 0, 0] [false]) 763 3820 := by
  have hq : ¬(2 ^ 128 : ℕ) < 2 := by norm_num
  have hl : (Nat.bits (2 ^ 128)).length = 129 := by
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  have ht := runsBetween [] [] stationary 0 1 (2 ^ 128)
  simp only [finalConfig, hq, dite_false, raw_stationary, column_stationary, hl,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive] at ht
  norm_num only at ht
  exact ht

/- The empty schedule safely rejects index zero without constructing any marker. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (RawScheduleEndpoint.initialConfig [] [] [] [])
    (tapesCfg [] ![[], [], [], [], []] 0 ![0, 0, 0, 0, 0] [false]) 40 205 := by
  let σ : MultiTapePTM.Schedule 1 0 := fun _ _ => 0
  have hw : RawScheduleEndpoint.word σ = [] := by decide
  have hc : RelativeScanSchedule.column σ 0 = [] := by decide
  simpa [finalConfig, hw, hc, RelativeScan.encode] using runsBetween [] [] σ 0 1 0

/- No runtime table, horizon or query is hard-coded into the finite controller. -/
example : ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM 5 Bool S),
    ∀ (q : ℕ) (σ : MultiTapePTM.Schedule 1 q) (p : ℕ),
      RunsBetween tm
        (RawScheduleEndpoint.initialConfig [] (RawScheduleEndpoint.word σ) p.bits [])
        (finalConfig [] [] σ 0 1 p)
        (39 * q + 5 * p.bits.length + 40) (5 * (39 * q + 5 * p.bits.length + 41)) := by
  exact ⟨_, inferInstance, machine (0 : Fin 1) 1, fun q σ p => runsBetween [] [] σ 0 1 p⟩
