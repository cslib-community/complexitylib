/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleColumn
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleDecode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanSchedule

/-!
# Total endpoint queries on raw schedule words

The runtime request contains a raw two-bit row-major schedule, an outgoing selector `3*h+d`,
and an interval index. `query` rejects invalid rows, selectors and interval indices. Its outer
option distinguishes an invalid request from a valid request with no later block appearance.

The computation reuses the native column reader's semantic function and the existing relative
scan evaluator. `query_rows` identifies its answer with `firstAfter` on every represented
schedule. These are executable semantics; native parsing, dispatch and time bounds are separate.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointQuery

/-- Runtime request for a work-head outgoing endpoint. -/
structure Input where
  /-- Complete raw table, with the input head first and two bits per movement. -/
  raw : List Bool
  /-- Outgoing selector `3*h+d`, with work-head index `h` and port `d < 3`. -/
  selector : ℕ
  /-- Interval whose outgoing block endpoint is requested. -/
  interval : ℕ
  deriving DecidableEq

/-- A raw request has valid rows, a work-head port selector, and an existing interval. -/
@[expose] def valid (k : ℕ) (a : Input) : Bool :=
  ScheduleBits.validate k a.raw && decide (a.selector < 3 * k) &&
    decide (a.interval < a.raw.length / (2 * (k + 1)))

/-- The guard checks exactly canonical rows and both runtime range conditions. -/
theorem valid_eq_true_iff (k : ℕ) (a : Input) :
    valid k a = true ↔ ScheduleBits.Canonical k a.raw ∧ a.selector < 3 * k ∧
      a.interval < a.raw.length / (2 * (k + 1)) := by
  simp [valid, ScheduleBits.validate_eq_true_iff, and_assoc]

/-- Total endpoint semantics: outer `none` rejects a malformed request; `some none` denotes a
valid outgoing block with no later occurrence, and `some (some j)` gives its next interval. -/
@[expose] def query (k : ℕ) (a : Input) : Option (Option ℕ) :=
  if valid k a then
    let reader := ScheduleColumn.reader (2 * (a.selector / 3 + 1))
      (2 * (k - (a.selector / 3 + 1)))
    do
      let ss ← ScheduleBits.decodePairs (reader.run reader.q₀ a.raw)
      let move ← ss[a.interval]?
      let r := RelativeScan.evaluate (ss.drop (a.interval + 1))
        (1 - ((a.selector % 3 : ℕ) : ℤ) + (move : ℤ))
      return r.index.map (a.interval + 1 + ·)
  else none

/-- A request rejected by the syntactic/range guard has no endpoint answer. -/
theorem query_eq_none_of_not_valid (k : ℕ) (a : Input) (ha : valid k a = false) :
    query k a = none := by simp [query, ha]

/-- Every represented schedule and in-range outgoing selector passes the guard. -/
theorem valid_rows {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (i : Fin q)
    (h : Fin k) (d : Fin 3) :
    valid k ⟨ScheduleBits.rows (List.ofFn σ), 3 * h.val + d.val, i.val⟩ = true := by
  have hsel : 3 * h.val + d.val < 3 * k := by omega
  simp [valid, ScheduleBits.validate_rows, hsel, i.isLt]

/-- On represented schedules, the total query returns the exact next-appearance endpoint.
The enclosing `some` records that the request itself is valid, including on exhaustion. -/
theorem query_rows {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (i : Fin q)
    (h : Fin k) (d : Fin 3) :
    query k ⟨ScheduleBits.rows (List.ofFn σ), 3 * h.val + d.val, i.val⟩ =
      some ((MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
        (MultiTapePTM.portBlock σ i h d)) i).map Fin.val) := by
  have hdiv : (3 * h.val + d.val) / 3 = h.val := by omega
  have hmod : (3 * h.val + d.val) % 3 = d.val := by omega
  rw [query, valid_rows]
  simp only [↓reduceIte]
  rw [hdiv, hmod]
  have hc := ScheduleColumn.run_rows h.succ (List.ofFn σ)
  simp only [Fin.val_succ] at hc
  rw [hc]
  simp only [ScheduleBits.column, ScheduleBits.head_succ, ScheduleBits.decodePairs_encode,
    Option.bind_eq_bind, Option.bind_some]
  have hcol : (List.ofFn σ).map (fun r => r (some h)) =
      RelativeScanSchedule.column σ h := by
    simp [RelativeScanSchedule.column, List.map_ofFn, Function.comp_def]
  rw [hcol]
  have hmove : (RelativeScanSchedule.column σ h)[i.val]? = some (σ i (some h)) := by
    simp [RelativeScanSchedule.column]
  rw [hmove]
  simp only [Option.bind_some]
  rw [← RelativeScanSchedule.movements_eq_drop]
  exact congrArg some (RelativeScan.evaluate_next σ i h d)

/-- The outer option recognizes exactly valid requests, so decoding and extraction introduce
no additional rejection cases. In particular, valid exhaustion is distinct from invalid input. -/
theorem query_isSome (k : ℕ) (a : Input) : (query k a).isSome = valid k a := by
  cases hv : valid k a with
  | false => simp [query_eq_none_of_not_valid k a hv]
  | true =>
    obtain ⟨hc, hs, hi⟩ := (valid_eq_true_iff k a).mp hv
    obtain ⟨rs, hr⟩ := hc.exists_rows
    let σ : MultiTapePTM.Schedule k rs.length := fun j => rs[j.val]
    have hσ : List.ofFn σ = rs := List.ofFn_getElem
    have hraw : ScheduleBits.rows (List.ofFn σ) = a.raw := by rw [hσ]; exact hr
    have hlen : a.raw.length / (2 * (k + 1)) = rs.length := by
      rw [← hr, ScheduleBits.length_rows]
      exact Nat.mul_div_cancel_left rs.length (by omega)
    let i : Fin rs.length := ⟨a.interval, by omega⟩
    let h : Fin k := ⟨a.selector / 3, by omega⟩
    let d : Fin 3 := ⟨a.selector % 3, Nat.mod_lt _ (by decide)⟩
    have he : 3 * h.val + d.val = a.selector := by dsimp [h, d]; omega
    have hq := query_rows σ i h d
    have ha : (⟨ScheduleBits.rows (List.ofFn σ), 3 * h.val + d.val, i.val⟩ : Input) = a := by
      cases a
      simp_all only [i]
    rw [ha] at hq
    simp [hq]

end Turing.MultiTapeTM.ScheduleEndpointQuery
