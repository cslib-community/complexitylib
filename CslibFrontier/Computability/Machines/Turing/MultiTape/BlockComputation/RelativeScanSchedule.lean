/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanIndex
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-!
# Native next-appearance search on a prepared schedule column

The full movement column is already on the source tape, with its head at the pair following the
queried interval. The finite initial-distance selector translates the outgoing port and current
movement into one of the five marker positions. The native scanner preserves the complete column,
appends its match flag, rewinds the source, and returns the absolute interval index in binary.

The returned flag and index agree with the existing `firstAfter` endpoint of the block network.
The clock is at most `10*q+9`, including the counted rewind through the preserved prefix.
Column extraction, initial cursor positioning, and selecting the finite-control member from the
current movement and port are explicit prerequisites, not free random-access operations.

## Main results

* `RelativeScanSchedule.result_index`: the computed index is the block network's next appearance.
* `RelativeScanSchedule.runsBetween`: the corresponding physical run on the full column.
-/

public section

namespace Turing.MultiTapeTM.RelativeScanSchedule

variable {k q : ℕ}

/-- All movements of one work-tape column, in interval order. -/
@[expose] def column (σ : MultiTapePTM.Schedule k q) (h : Fin k) : List SignType :=
  List.ofFn fun j => σ j (some h)

@[simp] theorem length_column (σ : MultiTapePTM.Schedule k q) (h : Fin k) :
    (column σ h).length = q := List.length_ofFn

/-- The movement specification is exactly the indicated bounded suffix of the full column. -/
theorem movements_eq_take_drop (σ : MultiTapePTM.Schedule k q) (h : Fin k)
    (fuel cursor : ℕ) :
    RelativeScan.movements σ h fuel cursor = ((column σ h).drop cursor).take fuel := by
  induction fuel generalizing cursor with
  | zero => simp [RelativeScan.movements]
  | succ fuel ih =>
    by_cases hc : cursor < q
    · rw [RelativeScan.movements, dite_eq_left hc, ih,
        List.drop_eq_getElem_cons (i := cursor) (l := column σ h) (by simpa using hc),
        List.take_succ_cons]
      simp [column]
    · rw [RelativeScan.movements, dite_eq_right hc,
        List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hc), List.take_nil]

/-- The remaining horizon gives the whole suffix, with no implicit column recomputation. -/
theorem movements_eq_drop (σ : MultiTapePTM.Schedule k q) (h : Fin k) (cursor : ℕ) :
    RelativeScan.movements σ h (q - cursor) cursor = (column σ h).drop cursor := by
  rw [movements_eq_take_drop]
  exact List.take_of_length_le (by simp)

/-- The initial displacement `1-d+move` lies in `[-2,2]`, represented by five finite states. -/
@[expose] def start (move : SignType) (d : Fin 3) : Fin 5 :=
  ⟨(3 - (d : ℤ) + (move : ℤ)).toNat, by fin_cases d <;> cases move <;> decide⟩

/-- The finite selector has exactly the relative distance required by the block-network port. -/
@[simp] theorem initialDistance_start (move : SignType) (d : Fin 3) :
    RelativeScan.initialDistance (start move d) = 1 - (d : ℤ) + (move : ℤ) := by
  fin_cases d <;> cases move <;> rfl

/-- The suffix scan result, with its consumed offset replaced by the absolute source index. -/
@[expose] def result (σ : MultiTapePTM.Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) :
    RelativeScan.Result :=
  let r := RelativeScan.evaluate ((column σ h).drop (i.val + 1))
    (1 - (d : ℤ) + (σ i (some h) : ℤ))
  { r with consumed := i.val + 1 + r.consumed }

/-- The binary counter paired with its success flag denotes exactly the next block appearance. -/
theorem result_index (σ : MultiTapePTM.Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) :
    (result σ i h d).index =
      (MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
        (MultiTapePTM.portBlock σ i h d)) i).map Fin.val := by
  rw [result, RelativeScanIndex.index_add_consumed, ← movements_eq_drop]
  exact RelativeScan.evaluate_next σ i h d

/-- The appended flag is true precisely when the queried outgoing block appears again. -/
theorem result_found (σ : MultiTapePTM.Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) :
    (result σ i h d).found =
      (MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
        (MultiTapePTM.portBlock σ i h d)) i).isSome := by
  have hindex := congrArg Option.isSome (result_index σ i h d)
  cases hf : (result σ i h d).found <;> simpa [RelativeScan.Result.index, hf] using hindex

/-- The physical scan on the full column, with prefix rewind and suffix scanning separately
charged. The source cursor is prepared at the pair immediately after `i`. -/
theorem runsBetween_exact (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i : Fin q) (h : Fin k) (d : Fin 3) :
    RunsBetween (RelativeScanIndex.machine (start (σ i (some h)) d))
      (RelativeScanIndex.positionedConfig input (RelativeScan.encode (column σ h)) (i.val + 1) out)
      (RelativeScanIndex.finalConfig input (RelativeScan.encode (column σ h)) out (result σ i h d))
      (8 * (i.val + 1) + 10 * (RelativeScan.evaluate ((column σ h).drop (i.val + 1))
        (1 - (d : ℤ) + (σ i (some h) : ℤ))).consumed + 9)
      (16 * (i.val + 1) + 20 * (RelativeScan.evaluate ((column σ h).drop (i.val + 1))
        (1 - (d : ℤ) + (σ i (some h) : ℤ))).consumed + 26) := by
  have hp : ((column σ h).take (i.val + 1)).length = i.val + 1 := by
    rw [List.length_take, length_column, min_eq_left (by omega)]
  have hsource : RelativeScan.encode ((column σ h).take (i.val + 1)) ++
      RelativeScan.encode ((column σ h).drop (i.val + 1)) = RelativeScan.encode (column σ h) := by
    rw [← RelativeScan.encode_append, List.take_append_drop]
  simpa only [hp, hsource, initialDistance_start, result] using
    RelativeScanIndex.runsBetween_fromPrefix input out
      ((column σ h).take (i.val + 1)) ((column σ h).drop (i.val + 1)) (start (σ i (some h)) d)

/-- The prepared-column endpoint query runs in linear time in the horizon. The bound includes
rewinding and counting every source pair before the returned absolute index. -/
theorem runsBetween (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i : Fin q) (h : Fin k) (d : Fin 3) :
    RunsBetween (RelativeScanIndex.machine (start (σ i (some h)) d))
      (RelativeScanIndex.positionedConfig input (RelativeScan.encode (column σ h)) (i.val + 1) out)
      (RelativeScanIndex.finalConfig input (RelativeScan.encode (column σ h)) out (result σ i h d))
      (10 * q + 9) (20 * q + 26) := by
  have hconsumed := RelativeScan.consumed_le ((column σ h).drop (i.val + 1))
    (1 - (d : ℤ) + (σ i (some h) : ℤ))
  simp only [List.length_drop, length_column] at hconsumed
  exact (runsBetween_exact input out σ i h d).mono (by omega) (by omega)

/-- If the outgoing block reappears at `j`, the physical query appends true and writes the
canonical binary encoding of exactly `j`, retaining the full source and previous output. -/
theorem runsBetween_of_firstAfter (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i j : Fin q) (h : Fin k) (d : Fin 3)
    (hnext : MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
      (MultiTapePTM.portBlock σ i h d)) i = some j) :
    RunsBetween (RelativeScanIndex.machine (start (σ i (some h)) d))
      (RelativeScanIndex.positionedConfig input (RelativeScan.encode (column σ h)) (i.val + 1) out)
      (tapesCfg input ![RelativeScan.encode (column σ h), [true, true, true], j.val.bits]
        0 ![0, (result σ i h d).distance + 1, 0] (out ++ [true]))
      (10 * q + 9) (20 * q + 26) := by
  have hfound : (result σ i h d).found = true := by rw [result_found, hnext]; rfl
  have hindex : (result σ i h d).consumed = j.val := by
    simpa only [RelativeScan.Result.index, hfound, ite_true, hnext, Option.map_some,
      Option.some.injEq] using result_index σ i h d
  simpa only [RelativeScanIndex.finalConfig, hfound, hindex] using runsBetween input out σ i h d

end Turing.MultiTapeTM.RelativeScanSchedule
