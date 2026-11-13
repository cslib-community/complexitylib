/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleColumn
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanDispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PositionPairs
import Mathlib.Tactic.FinCases

/-!
# Native endpoint queries from a raw schedule and a binary interval index

The five-tape machine receives a row-major two-bit schedule and a canonical binary interval
index. It extracts one fixed head's column, positions its source head using the runtime index,
reads the actual current movement, and performs the native relative endpoint scan. Only the
simulated head and outgoing port select the finite controller; neither the schedule nor its
horizon or queried interval occurs in the controller.

The final source column and raw table are preserved, the adapter is blank, the source/counter/raw
heads are zero, and the returned flag and binary index agree with the block network's next
appearance. Extraction, positioning, both movement reads, scanning, and rewind/counting are all
charged. The input domain is the canonical two-bit representation; validating an arbitrary word
or converting a packed natural into this format is not claimed by this theorem.
-/

public section

namespace Turing.MultiTapeTM.RawScheduleEndpoint

variable {k q : ℕ}

/-- Input-first row-major table, with two bits per movement. -/
@[expose] def word (σ : MultiTapePTM.Schedule k q) : List Bool :=
  ScheduleBits.rows (List.ofFn σ)

/-- The raw representation has one fixed-width row for every interval. -/
@[simp] theorem length_word (σ : MultiTapePTM.Schedule k q) :
    (word σ).length = 2 * (k + 1) * q := by
  simp [word]

/-- Every represented schedule has complete rows and valid aligned movement pairs. -/
theorem canonical_word (σ : MultiTapePTM.Schedule k q) : ScheduleBits.Canonical k (word σ) :=
  ScheduleBits.canonical_rows _

/-- Extracting a work-head column agrees with the movement list used by the semantic scan. -/
theorem column_eq (σ : MultiTapePTM.Schedule k q) (h : Fin k) :
    ScheduleBits.column h.succ (List.ofFn σ) =
      RelativeScan.encode (RelativeScanSchedule.column σ h) := by
  simp [ScheduleBits.column, RelativeScanSchedule.column, List.map_ofFn, Function.comp_def]

/-- The column extractor uses the destination, raw source, and adapter tapes. -/
@[expose] def columnTapes : Fin 3 ↪ Fin 5 :=
  ⟨![0, 3, 4], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- Extract a work-head column, position from the binary index, read the current movement, and
run the native scanner. The raw source and adapter remain outside the three-tape scan. -/
noncomputable def machine (h : Fin k) (d : Fin 3) :=
  ((ScheduleColumn.machine h.succ).extendTapes columnTapes).seq
    ((PositionPairs.machine.seq (RelativeScanDispatch.machine d)).extendTapes (Fin.castAddEmb 2))

/-- Runtime binary index on tape 1 and raw table on tape 3; all five heads start at zero. -/
@[expose] def initialConfig (input raw index out : List Bool) : Cfg 5 Bool Unit input :=
  tapesCfg input ![[], index, [], raw, []] 0 0 out

/-- The full extracted column, signed marker, absolute binary index, and preserved raw table.
The marker head retains the final distance; all other heads are restored to zero. -/
@[expose] def finalConfig (input raw column out : List Bool) (r : RelativeScan.Result) :
    Cfg 5 Bool Unit input :=
  tapesCfg input ![column, [true, true, true], r.consumed.bits, raw, []]
    0 ![0, r.distance + 1, 0, 0, 0] (out ++ [r.found])

private theorem column_view (input raw index out : List Bool) :
    viewCfg columnTapes (initialConfig input raw index out) =
      tapesCfg input ![[], raw, []] 0 0 out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl

private theorem column_embed (input raw index column out : List Bool) :
    embed columnTapes (tapesCfg input ![column, raw, []] 0 0 out)
      (initialConfig input raw index out).workTapes
      (initialConfig input raw index out).workTapePos =
      tapesCfg input ![column, index, [], raw, []] 0 0 out := by
  have h0 : partialInv columnTapes 0 = some 0 := partialInv_embed columnTapes 0
  have h3 : partialInv columnTapes 3 = some 1 := partialInv_embed columnTapes 1
  have h4 : partialInv columnTapes 4 = some 2 := partialInv_embed columnTapes 2
  have hn (i : Fin 5) (hi : i = 1 ∨ i = 2) : partialInv columnTapes i = none := by
    apply partialInv_eq_none
    rintro ⟨j, hj⟩
    rcases hi with rfl | rfl <;> fin_cases j <;> simp [columnTapes] at hj
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
    simp [embed, h0, h3, h4, hn 1 (Or.inl rfl), hn 2 (Or.inr rfl),
      initialConfig, tapesCfg]

private theorem scan_view (input raw index column out : List Bool) :
    viewCfg (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5)
      (tapesCfg input ![column, index, [], raw, []] 0 0 out) =
      PositionPairs.config input column index [] 0 out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl

private theorem scan_embed (input raw index column out : List Bool) (r : RelativeScan.Result) :
    embed (Fin.castAddEmb 2 : Fin 3 ↪ Fin 5)
      (RelativeScanIndex.finalConfig input column out r)
      (tapesCfg input ![column, index, [], raw, []] 0 0 out).workTapes
      (tapesCfg input ![column, index, [], raw, []] 0 0 out).workTapePos =
      finalConfig input raw column out r := by
  rw [embed_castAdd]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl

/-- A complete physical endpoint query from the raw table and runtime binary interval index.
All source accesses are sequential native steps, including extraction and cursor positioning. -/
theorem runsBetween (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i : Fin q) (h : Fin k) (d : Fin 3) :
    RunsBetween (machine h d) (initialConfig input (word σ) i.val.bits out)
      (finalConfig input (word σ) (RelativeScan.encode (RelativeScanSchedule.column σ h)) out
        (RelativeScanSchedule.result σ i h d))
      ((8 * k + 20) * q + 11 * i.val + 5 * i.val.bits.length + 38)
      ((4 * k + 38) * q + 33 * i.val + 15 * i.val.bits.length + 100) := by
  have he := ScheduleColumn.runsBetween h.succ input out (List.ofFn σ)
  rw [column_eq, List.length_ofFn] at he
  change RunsBetween _ (tapesCfg input ![[], word σ, []] 0 0 out)
    (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h), word σ, []]
      0 0 out) _ _ at he
  rw [← column_view input (word σ) i.val.bits out] at he
  have he' := he.extendTapes columnTapes
  rw [column_embed input (word σ) i.val.bits
    (RelativeScan.encode (RelativeScanSchedule.column σ h)) out] at he'
  have hp := PositionPairs.runsBetween_bits input
    (RelativeScan.encode (RelativeScanSchedule.column σ h)) out i.val
  have hs := RelativeScanDispatch.runsBetween input out σ i h d
  have hi : PositionPairs.config input
      (RelativeScan.encode (RelativeScanSchedule.column σ h)) [] [] (2 * (i.val : ℤ)) out =
      RelativeScanIndex.positionedConfig input
        (RelativeScan.encode (RelativeScanSchedule.column σ h)) i.val out := rfl
  rw [hi] at hp
  have hp' := hp.seq hs
  rw [← scan_view input (word σ) i.val.bits
    (RelativeScan.encode (RelativeScanSchedule.column σ h)) out] at hp'
  have hs' := hp'.extendTapes (Fin.castAddEmb 2)
  rw [scan_embed] at hs'
  have hr := he'.seq hs'
  convert hr using 1 <;> first | rfl | ring

/-- A successful query returns the actual next interval in canonical binary, with the full raw
table and extracted column retained. This is the endpoint consumed by the block network. -/
theorem runsBetween_of_firstAfter (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i j : Fin q) (h : Fin k) (d : Fin 3)
    (hnext : MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
      (MultiTapePTM.portBlock σ i h d)) i = some j) :
    RunsBetween (machine h d) (initialConfig input (word σ) i.val.bits out)
      (tapesCfg input ![RelativeScan.encode (RelativeScanSchedule.column σ h),
        [true, true, true], j.val.bits, word σ, []]
        0 ![0, (RelativeScanSchedule.result σ i h d).distance + 1, 0, 0, 0]
        (out ++ [true]))
      ((8 * k + 20) * q + 11 * i.val + 5 * i.val.bits.length + 38)
      ((4 * k + 38) * q + 33 * i.val + 15 * i.val.bits.length + 100) := by
  have hf : (RelativeScanSchedule.result σ i h d).found = true := by
    rw [RelativeScanSchedule.result_found, hnext]
    rfl
  have hi : (RelativeScanSchedule.result σ i h d).consumed = j.val := by
    simpa only [RelativeScan.Result.index, hf, ite_true, hnext, Option.map_some,
      Option.some.injEq] using RelativeScanSchedule.result_index σ i h d
  simpa only [finalConfig, hf, hi] using runsBetween input out σ i h d

end Turing.MultiTapeTM.RawScheduleEndpoint
