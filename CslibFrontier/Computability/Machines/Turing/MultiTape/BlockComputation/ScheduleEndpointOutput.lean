/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.BoundedRawScheduleEndpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointAnswer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.OutputCapture
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FinCases

/-!
# Serial output from bounded native schedule endpoints

The bounded endpoint machine's flags are captured on a fresh sixth work tape and rewound.
The finite answer serializer reads those flags and appends the returned binary index exactly
on success. Thus the output itself is the explicit tagged encoding of the endpoint answer.
All six tapes and final head positions remain specified, and the additional time is linear
in the returned index width plus constant-size flag handling.

The raw table still represents a schedule and the work-head/port choice is fixed. This wrapper
does not assume a free read of the write-only output, nor perform raw-input parsing or dispatch.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointOutput

variable {k q : ℕ}

private def answerTapes : Fin 2 ↪ Fin 6 :=
  ⟨![5, 2], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- Capture the native query's flags, rewind that short word, then serialize flags and payload. -/
noncomputable def machine (h : Fin k) (d : Fin 3) :=
  (BoundedRawScheduleEndpoint.machine h d).outputToWord.seq
    (ScheduleEndpointAnswer.machine.extendTapes answerTapes)

/-- The original five-tape endpoint input plus a blank flag-capture tape. -/
@[expose] def initialConfig (input raw index out : List Bool) : Cfg 6 Bool Unit input :=
  tapesCfg input ![[], index, [], raw, [], []] 0 0 out

/-- The represented endpoint answer, with invalid intervals distinct from valid exhaustion. -/
@[expose] def answer (σ : MultiTapePTM.Schedule k q) (h : Fin k) (d : Fin 3) (p : ℕ) :
    Option (Option ℕ) :=
  if hp : p < q then some (RelativeScanSchedule.result σ ⟨p, hp⟩ h d).index else none

/-- The represented answer agrees with the total query semantics at every interval index,
including rejection at and beyond the end of the schedule. -/
theorem answer_eq_query (σ : MultiTapePTM.Schedule k q) (h : Fin k) (d : Fin 3) (p : ℕ) :
    answer σ h d p =
      ScheduleEndpointQuery.query k ⟨RawScheduleEndpoint.word σ, 3 * h.val + d.val, p⟩ := by
  by_cases hp : p < q
  · rw [answer, dite_eq_left hp, RelativeScanSchedule.result_index]
    exact (ScheduleEndpointQuery.query_rows σ ⟨p, hp⟩ h d).symm
  · rw [answer, dite_eq_right hp]
    symm
    apply ScheduleEndpointQuery.query_eq_none_of_not_valid
    simp [ScheduleEndpointQuery.valid, RawScheduleEndpoint.word, hp]

/-- Retained raw/column/marker/index words and captured flags. Successful output leaves the
index head at its end; unsuccessful output does not read that word. -/
@[expose] def finalConfig (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) : Cfg 6 Bool Unit input :=
  if hp : p < q then
    let r := RelativeScanSchedule.result σ ⟨p, hp⟩ h d
    tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h),
      [true, true, true], r.consumed.bits, RawScheduleEndpoint.word σ, [], [true, r.found]]
      0 ![0, r.distance + 1, if r.found then r.consumed.bits.length else 0, 0, 0, 2]
      (out ++ ScheduleEndpointAnswer.encAnswer (some r.index))
  else tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), [], [],
      RawScheduleEndpoint.word σ, [], [false]] 0 ![2 * (q : ℤ), 0, 0, 0, 0, 1]
      (out ++ [false])

private theorem liftAnswer (input column marker index raw flags out out' : List Bool)
    (sourceHead markerHead indexHead flagHead : ℤ) {t s : ℕ}
    (hr : RunsBetween ScheduleEndpointAnswer.machine
      (tapesCfg input ![flags, index] 0 0 out)
      (tapesCfg input ![flags, index] 0 ![flagHead, indexHead] out') t s) :
    RunsBetween (ScheduleEndpointAnswer.machine.extendTapes answerTapes)
      (tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, 0, 0, 0, 0] out)
      (tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, indexHead, 0, 0, flagHead] out') t (s + 4) := by
  have hv : viewCfg answerTapes
      (tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, 0, 0, 0, 0] out) =
      tapesCfg input ![flags, index] 0 0 out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl
  rw [← hv] at hr
  have he := hr.extendTapes answerTapes
  have hf : embed answerTapes (tapesCfg input ![flags, index] 0 ![flagHead, indexHead] out')
      (tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, 0, 0, 0, 0] out).workTapes
      (tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, 0, 0, 0, 0] out).workTapePos =
      tapesCfg input ![column, marker, index, raw, [], flags]
        0 ![sourceHead, markerHead, indexHead, 0, 0, flagHead] out' := by
    apply embed_tapesCfg
    · intro i; fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
    · intro i hi
      fin_cases i <;> try exact ⟨rfl, rfl, rfl⟩
      · exact False.elim (hi ⟨1, rfl⟩)
      · exact False.elim (hi ⟨0, rfl⟩)
  simpa only [hf] using he

private theorem captured_valid (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) (hp : p < q) :
    capturedOutput (BoundedRawScheduleEndpoint.finalConfig input [] σ h d p) out =
      let r := RelativeScanSchedule.result σ ⟨p, hp⟩ h d
      tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h),
        [true, true, true], r.consumed.bits, RawScheduleEndpoint.word σ, [], [true, r.found]]
        0 ![0, r.distance + 1, 0, 0, 0, 0] out := by
  simp only [BoundedRawScheduleEndpoint.finalConfig, hp, dite_true]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | last =>
    simp only [capturedOutput, outCfg, Fin.lastCases_last]
    simp [RawScheduleEndpoint.finalConfig, tapesCfg]
  | cast i => fin_cases i <;> rfl

private theorem captured_invalid (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) (hp : ¬p < q) :
    capturedOutput (BoundedRawScheduleEndpoint.finalConfig input [] σ h d p) out =
      tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), [], [],
        RawScheduleEndpoint.word σ, [], [false]] 0 ![2 * (q : ℤ), 0, 0, 0, 0, 0] out := by
  simp only [BoundedRawScheduleEndpoint.finalConfig, hp, dite_false]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.lastCases with
  | last =>
    simp only [capturedOutput, outCfg, Fin.lastCases_last]
    simp [tapesCfg]
  | cast i => fin_cases i <;> rfl

private theorem runsBetween_serialize (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    RunsBetween (ScheduleEndpointAnswer.machine.extendTapes answerTapes)
      (capturedOutput (BoundedRawScheduleEndpoint.finalConfig input [] σ h d p) out)
      (finalConfig input out σ h d p) (q + 3) (6 * (q + 4)) := by
  by_cases hp : p < q
  · let r := RelativeScanSchedule.result σ ⟨p, hp⟩ h d
    have hc : r.consumed ≤ q := by
      have hb := RelativeScan.consumed_le
        ((RelativeScanSchedule.column σ h).drop (p + 1))
        (1 - (d : ℤ) + (σ ⟨p, hp⟩ (some h) : ℤ))
      simp only [List.length_drop, RelativeScanSchedule.length_column] at hb
      dsimp [r, RelativeScanSchedule.result]
      omega
    have hl : r.consumed.bits.length ≤ q := by
      rw [Nat.size_eq_bits_len, Nat.size_le]
      exact hc.trans_lt Nat.lt_two_pow_self
    rw [captured_valid input out σ h d p hp]
    change RunsBetween _
      (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h),
        [true, true, true], r.consumed.bits, RawScheduleEndpoint.word σ, [], [true, r.found]]
        0 ![0, r.distance + 1, 0, 0, 0, 0] out) _ _ _
    simp only [finalConfig, hp, dite_true]
    change RunsBetween _ _
      (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h),
        [true, true, true], r.consumed.bits, RawScheduleEndpoint.word σ, [], [true, r.found]]
        0 ![0, r.distance + 1, if r.found then r.consumed.bits.length else 0, 0, 0, 2]
        (out ++ ScheduleEndpointAnswer.encAnswer (some r.index))) _ _
    cases hf : r.found with
    | false =>
      have hs := liftAnswer input (RelativeScan.encode (RelativeScanSchedule.column σ h))
        [true, true, true] r.consumed.bits (RawScheduleEndpoint.word σ) [true, false]
        out (out ++ [true, false]) 0 (r.distance + 1) 0 2
        (ScheduleEndpointAnswer.runsBetween_exhausted input r.consumed.bits out)
      have hb := (RunsBetween.of_runFrom hs.1).mono (by omega : 2 ≤ q + 3)
        (Nat.mul_le_mul_left 6 (by omega : 2 + 1 ≤ q + 4))
      simpa [hf, RelativeScan.Result.index, ScheduleEndpointAnswer.encAnswer]
        using hb
    | true =>
      have hs := liftAnswer input (RelativeScan.encode (RelativeScanSchedule.column σ h))
        [true, true, true] r.consumed.bits (RawScheduleEndpoint.word σ) [true, true]
        out (out ++ [true, true] ++ r.consumed.bits) 0 (r.distance + 1) r.consumed.bits.length 2
        (ScheduleEndpointAnswer.runsBetween_found input r.consumed.bits out)
      have hb := (RunsBetween.of_runFrom hs.1).mono (by omega : r.consumed.bits.length + 3 ≤ q + 3)
        (Nat.mul_le_mul_left 6 (by omega : r.consumed.bits.length + 3 + 1 ≤ q + 4))
      simpa [hf, RelativeScan.Result.index, ScheduleEndpointAnswer.encAnswer,
        encNat_apply, List.append_assoc] using hb
  · rw [captured_invalid input out σ h d p hp]
    have hs := liftAnswer input (RelativeScan.encode (RelativeScanSchedule.column σ h))
      [] [] (RawScheduleEndpoint.word σ) [false] out (out ++ [false]) (2 * (q : ℤ)) 0 0 1
      (ScheduleEndpointAnswer.runsBetween_invalid input [] out)
    have hb := (RunsBetween.of_runFrom hs.1).mono (by omega : 1 ≤ q + 3)
      (Nat.mul_le_mul_left 6 (by omega : 1 + 1 ≤ q + 4))
    simpa only [finalConfig, hp, dite_false] using hb

/-- The final output is exactly the tagged encoding of the represented endpoint answer. -/
theorem finalConfig_output (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    (finalConfig input out σ h d p).output =
      out ++ ScheduleEndpointAnswer.encAnswer (answer σ h d p) := by
  by_cases hp : p < q <;> simp [finalConfig, answer, hp, tapesCfg, ScheduleEndpointAnswer.encAnswer]

/-- The machine's final output encodes the total endpoint query on the represented raw table. -/
theorem finalConfig_output_query (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    (finalConfig input out σ h d p).output = out ++ ScheduleEndpointAnswer.encAnswer
      (ScheduleEndpointQuery.query k ⟨RawScheduleEndpoint.word σ, 3 * h.val + d.val, p⟩) := by
  rw [finalConfig_output, answer_eq_query]

/-- Native endpoint computation with its answer fully serialized on the real output tape.
All flag handling, index copying and old output preservation are included in the clock. -/
theorem runsBetween (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    RunsBetween (machine h d)
      (initialConfig input (RawScheduleEndpoint.word σ) p.bits out)
      (finalConfig input out σ h d p)
      ((8 * k + 32) * q + 5 * p.bits.length + 47)
      (6 * ((8 * k + 32) * q + 5 * p.bits.length + 48)) := by
  have hraw := BoundedRawScheduleEndpoint.runsBetween input [] σ h d p
  have hc := hraw.captureOutputWord out
  have hi : (outCfg (RawScheduleEndpoint.initialConfig input
      (RawScheduleEndpoint.word σ) p.bits [])).prependOutput out =
      initialConfig input (RawScheduleEndpoint.word σ) p.bits out := by
    refine Cfg.ext rfl rfl ?_ ?_
      (by simp [outCfg, Cfg.prependOutput, initialConfig, tapesCfg]) <;>
      funext i <;> induction i using Fin.lastCases with
    | last =>
      simp only [Cfg.prependOutput, outCfg, Fin.lastCases_last]
      simp [RawScheduleEndpoint.initialConfig, initialConfig, tapesCfg]
    | cast i => fin_cases i <;> rfl
  rw [hi] at hc
  have hs := runsBetween_serialize input out σ h d p
  have hr := RunsBetween.of_runFrom (hc.seq hs).1
  have hflag : (BoundedRawScheduleEndpoint.finalConfig input [] σ h d p).output.length ≤ 2 := by
    by_cases hp : p < q <;>
      simp [BoundedRawScheduleEndpoint.finalConfig, hp, RawScheduleEndpoint.finalConfig, tapesCfg]
  have ht : (8 * k + 31) * q + 5 * p.bits.length + 40 +
      (BoundedRawScheduleEndpoint.finalConfig input [] σ h d p).output.length + 2 + (q + 3) ≤
      (8 * k + 32) * q + 5 * p.bits.length + 47 := by nlinarith
  exact hr.mono ht (Nat.mul_le_mul_left 6 (Nat.add_le_add_right ht 1))

end Turing.MultiTapeTM.ScheduleEndpointOutput
