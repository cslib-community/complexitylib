/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RawScheduleEndpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BoundedPositionPairs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BranchRunsBetween
import Mathlib.Tactic.FinCases

/-!
# Native endpoint queries with bounded interval positioning

The row-major schedule and binary interval index are runtime data for one finite machine per
fixed head and port. After extracting the selected column, positioning stops at its end even
for arbitrarily large indices. A native branch enters the endpoint scanner only at a nonblank
source cell. Invalid intervals emit `[false]`; valid intervals emit `[true, found]` and return
the endpoint index and marker as in `RawScheduleEndpoint`.

The table and column remain intact. Invalid queries leave the source at EOF, with both scan
auxiliaries empty; valid queries restore the source head to zero and retain the scanner's signed
marker. Every phase is charged in a clock linear in the raw horizon and binary index width.
The raw table is still assumed to represent a schedule, and head/port selection is fixed.
-/

public section

namespace Turing.MultiTapeTM.BoundedRawScheduleEndpoint

variable {k q : ℕ}

private noncomputable def scan (d : Fin 3) :=
  BoundedPositionPairs.machine.seq (branch 0 (RelativeScanDispatch.machine d) (nop 3 Bool))

/-- Extract the selected column, bound positioning by EOF, and dispatch the scanner only for
an existing queried interval. Neither the row count nor index value occurs in finite control. -/
noncomputable def machine (h : Fin k) (d : Fin 3) :=
  (RawScheduleEndpoint.extract h).seq ((scan d).extendTapes (Fin.castAddEmb 2))

private def scanFinal (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) : Cfg 3 Bool Unit input :=
  if hp : p < q then
    RelativeScanIndex.finalConfig input (RelativeScan.encode (RelativeScanSchedule.column σ h))
      (out ++ [true]) (RelativeScanSchedule.result σ ⟨p, hp⟩ h d)
  else PositionPairs.config input (RelativeScan.encode (RelativeScanSchedule.column σ h))
    [] [] (2 * (q : ℤ)) (out ++ [false])

/-- A valid interval returns the native scan result after the validity bit; an invalid interval
emits only `false`, leaves both auxiliaries blank, and leaves the extracted-column head at EOF. -/
@[expose] def finalConfig (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) : Cfg 5 Bool Unit input :=
  if hp : p < q then
    RawScheduleEndpoint.finalConfig input (RawScheduleEndpoint.word σ)
      (RelativeScan.encode (RelativeScanSchedule.column σ h)) (out ++ [true])
      (RelativeScanSchedule.result σ ⟨p, hp⟩ h d)
  else tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), [], [],
      RawScheduleEndpoint.word σ, []] 0 ![2 * (q : ℤ), 0, 0, 0, 0] (out ++ [false])

private theorem runsBetween_scan (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    RunsBetween (scan d)
      (PositionPairs.config input (RelativeScan.encode (RelativeScanSchedule.column σ h))
        p.bits [] 0 out)
      (scanFinal input out σ h d p)
      (21 * q + 5 * p.bits.length + 26) (3 * (21 * q + 5 * p.bits.length + 27)) := by
  let column := RelativeScan.encode (RelativeScanSchedule.column σ h)
  have hlen : column.length = 2 * q := by simp [column]
  have hp := BoundedPositionPairs.runsBetween_bits input column out q p hlen
  by_cases hi : p < q
  · simp only [Nat.min_eq_left hi.le, hi, decide_true] at hp
    have hs := RelativeScanDispatch.runsBetween input (out ++ [true]) σ ⟨p, hi⟩ h d
    have hc : (PositionPairs.config input column [] [] (2 * (p : ℤ))
        (out ++ [true])).workTapeSymbols 0 ≠ none := by
      change tapeOfList column (2 * (p : ℤ)) ≠ none
      simp only [ne_eq, tapeOfList_eq_none_iff]
      omega
    have hb := hs.branch_of_ne_none (tm₂ := nop 3 Bool) hc
    have hr := RunsBetween.of_runFrom (hp.seq hb).1
    have htime : 11 * p + 5 * p.bits.length + 14 + (10 * q + 11 + 1) ≤
        21 * q + 5 * p.bits.length + 26 := by omega
    simpa only [scan, scanFinal, dite_eq_left hi] using
      hr.mono htime (Nat.mul_le_mul_left 3 (Nat.add_le_add_right htime 1))
  · have hle : q ≤ p := by omega
    simp only [Nat.min_eq_right hle, hi, decide_false] at hp
    have hc : (PositionPairs.config input column [] [] (2 * (q : ℤ))
        (out ++ [false])).workTapeSymbols 0 = none := by
      change tapeOfList column (2 * (q : ℤ)) = none
      rw [tapeOfList_eq_none_iff]
      omega
    have hn := RunsBetween.of_runFrom (runFrom_nop_withState
      (PositionPairs.config input column [] [] (2 * (q : ℤ)) (out ++ [false])))
    have hb := hn.branch_of_none (tm₁ := RelativeScanDispatch.machine d) hc
    have hr := RunsBetween.of_runFrom (hp.seq hb).1
    have htime : 11 * q + 5 * p.bits.length + 14 + (1 + 1) ≤
        21 * q + 5 * p.bits.length + 26 := by omega
    simpa only [scan, scanFinal, dite_eq_right hi] using
      hr.mono htime (Nat.mul_le_mul_left 3 (Nat.add_le_add_right htime 1))

private theorem embed_final (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    embed (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5) (scanFinal input out σ h d p)
      (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), p.bits, [],
        RawScheduleEndpoint.word σ, []] 0 0 out).workTapes
      (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), p.bits, [],
        RawScheduleEndpoint.word σ, []] 0 0 out).workTapePos = finalConfig input out σ h d p := by
  rw [embed_castAdd]
  by_cases hi : p < q <;>
    simp only [scanFinal, finalConfig, hi, dite_true, dite_false] <;>
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl

/-- A single native machine answers every binary interval query, including out-of-range ones,
within a bound independent of the numeric value of a rejected index. The interval-validity bit
separates malformed intervals from valid endpoint exhaustion. -/
theorem runsBetween (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : Fin k) (d : Fin 3) (p : ℕ) :
    RunsBetween (machine h d)
      (RawScheduleEndpoint.initialConfig input (RawScheduleEndpoint.word σ) p.bits out)
      (finalConfig input out σ h d p)
      ((8 * k + 31) * q + 5 * p.bits.length + 40)
      (5 * ((8 * k + 31) * q + 5 * p.bits.length + 41)) := by
  have he := RawScheduleEndpoint.runsBetween_extract input out σ h p.bits
  have hs := runsBetween_scan input out σ h d p
  rw [← RawScheduleEndpoint.prepared_view input (RawScheduleEndpoint.word σ) p.bits
    (RelativeScan.encode (RelativeScanSchedule.column σ h)) out] at hs
  have hs' := hs.extendTapes (Fin.castAddEmb 2)
  rw [embed_final] at hs'
  have hr := RunsBetween.of_runFrom (he.seq hs').1
  convert hr using 1 <;> first | rfl | ring

end Turing.MultiTapeTM.BoundedRawScheduleEndpoint
