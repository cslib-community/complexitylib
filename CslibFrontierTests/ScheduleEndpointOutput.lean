/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointOutput

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ScheduleEndpointOutput

private def stationary : MultiTapePTM.Schedule 1 2 := fun _ _ => 0

private theorem raw_stationary : RawScheduleEndpoint.word stationary =
    [false, false, false, false, false, false, false, false] := by decide

private theorem column_stationary : RelativeScanSchedule.column stationary 0 = [0, 0] := by decide

/- A successful native query emits the complete tagged answer after the prior output. The
captured flags and returned binary index remain on their tapes with both heads at the end. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig [true] [false, false, false, false, false, false, false, false] [] [false])
    (tapesCfg [true] ![[false, false, false, false], [true, true, true], [true],
      [false, false, false, false, false, false, false, false], [], [true, true]]
      0 ![0, 1, 1, 0, 0, 2] [false, true, true, true]) 127 768 := by
  have hr : RelativeScanSchedule.result stationary 0 0 1 = ⟨1, 0, true⟩ := by decide
  have hb : Nat.bits 1 = [true] := by decide
  simpa [finalConfig, raw_stationary, column_stationary, hr, RelativeScan.Result.index,
    ScheduleEndpointAnswer.encAnswer, encNat_apply, RelativeScan.encode, RelativeScan.negative,
    RelativeScan.positive, hb] using runsBetween [true] [false] stationary 0 1 0

/- Valid exhaustion serializes [true,false] without reading the retained nonempty index word. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig [] [false, false, false, false, false, false, false, false] [true] [])
    (tapesCfg [] ![[false, false, false, false], [true, true, true], [false, true],
      [false, false, false, false, false, false, false, false], [], [true, false]]
      0 ![0, 1, 0, 0, 0, 2] [true, false]) 132 798 := by
  have hr : RelativeScanSchedule.result stationary 1 0 1 = ⟨2, 0, false⟩ := by decide
  have hb₁ : Nat.bits 1 = [true] := by decide
  have hb₂ : Nat.bits 2 = [false, true] := by decide
  simpa [finalConfig, raw_stationary, column_stationary, hr, RelativeScan.Result.index,
    ScheduleEndpointAnswer.encAnswer, RelativeScan.encode, RelativeScan.negative,
    RelativeScan.positive, hb₁, hb₂] using runsBetween [] [] stationary 0 1 1

/- At EOF the scanner is skipped, and the captured rejection flag is serialized in one step. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig [] [false, false, false, false, false, false, false, false] [false, true] [])
    (tapesCfg [] ![[false, false, false, false], [], [],
      [false, false, false, false, false, false, false, false], [], [false]]
      0 ![4, 0, 0, 0, 0, 1] [false]) 137 828 := by
  have hb : Nat.bits 2 = [false, true] := by decide
  simpa [finalConfig, raw_stationary, column_stationary, RelativeScan.encode,
    RelativeScan.negative, RelativeScan.positive, hb] using runsBetween [] [] stationary 0 1 2

/- The end-to-end native clock remains linear in the table and binary request width, even
when the requested interval is exponentially larger than the table. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig [] [false, false, false, false, false, false, false, false]
      (Nat.bits (2 ^ 128)) [])
    (tapesCfg [] ![[false, false, false, false], [], [],
      [false, false, false, false, false, false, false, false], [], [false]]
      0 ![4, 0, 0, 0, 0, 1] [false]) 772 4638 := by
  have hq : ¬(2 ^ 128 : ℕ) < 2 := by norm_num
  have hl : (Nat.bits (2 ^ 128)).length = 129 := by
    rw [Nat.size_eq_bits_len, Nat.size_pow]
  have ht := runsBetween [] [] stationary 0 1 (2 ^ 128)
  simp only [finalConfig, hq, dite_false, raw_stationary, column_stationary, hl,
    RelativeScan.encode, RelativeScan.negative, RelativeScan.positive] at ht
  norm_num only at ht
  exact ht

/- The empty schedule rejects index zero and leaves only the captured rejection bit. -/
example : RunsBetween (machine (0 : Fin 1) 1)
    (initialConfig [] [] [] [])
    (tapesCfg [] ![[], [], [], [], [], [false]] 0 ![0, 0, 0, 0, 0, 1] [false]) 47 288 := by
  let σ : MultiTapePTM.Schedule 1 0 := fun _ _ => 0
  have hw : RawScheduleEndpoint.word σ = [] := by decide
  have hc : RelativeScanSchedule.column σ 0 = [] := by decide
  simpa [finalConfig, hw, hc, RelativeScan.encode] using runsBetween [] [] σ 0 1 0

/- One finite controller handles every runtime table and index, with no horizon in its type. -/
example : ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM 6 Bool S),
    ∀ (q : ℕ) (σ : MultiTapePTM.Schedule 1 q) (p : ℕ),
      RunsBetween tm (initialConfig [] (RawScheduleEndpoint.word σ) p.bits [])
        (finalConfig [] [] σ 0 1 p)
        (40 * q + 5 * p.bits.length + 47) (6 * (40 * q + 5 * p.bits.length + 48)) := by
  exact ⟨_, inferInstance, machine (0 : Fin 1) 1, fun q σ p => runsBetween [] [] σ 0 1 p⟩
