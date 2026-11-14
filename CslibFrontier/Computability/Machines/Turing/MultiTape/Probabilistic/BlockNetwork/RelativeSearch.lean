/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork

/-!
# Searching block windows by relative displacement

The scanner carries the distance from one fixed block and consumes one schedule entry per
unsuccessful candidate. It never recomputes a prefix sum. The fuel bounds the number of inspected
intervals; this is an algorithmic specification, not a native Turing-machine time certificate.
-/

public section

namespace Turing.MultiTapePTM

namespace RelativeSearch

variable {k q : ℕ}

/-- Search at most `fuel` successive intervals, carrying their signed distance from the queried
block. Schedule entries are read only at the current cursor. -/
@[expose] def scan (σ : Schedule k q) (h : Fin k) : ℕ → ℕ → ℤ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, cursor, distance =>
    if hc : cursor < q then
      if |distance| ≤ 1 then some cursor
      else scan σ h fuel (cursor + 1) (distance + (σ ⟨cursor, hc⟩ (some h) : ℤ))
    else none

/-- Number of candidate intervals inspected by `scan`; excludes machine-level representation
and tape costs. -/
@[expose] def inspections (σ : Schedule k q) (h : Fin k) : ℕ → ℕ → ℤ → ℕ
  | 0, _, _ => 0
  | fuel + 1, cursor, distance =>
    if hc : cursor < q then
      if |distance| ≤ 1 then 1
      else 1 + inspections σ h fuel (cursor + 1) (distance + (σ ⟨cursor, hc⟩ (some h) : ℤ))
    else 0

/-- The scanner inspects at most its fuel many intervals, reading one movement per unsuccessful
candidate. This structural bound makes no claim about a native implementation's clock. -/
theorem inspections_le (σ : Schedule k q) (h : Fin k) (fuel cursor : ℕ) (distance : ℤ) :
    inspections σ h fuel cursor distance ≤ fuel := by
  induction fuel generalizing cursor distance with
  | zero => simp [inspections]
  | succ fuel ih =>
    rw [inspections]
    split_ifs with hc hd
    · omega
    · have := ih (cursor + 1) (distance + (σ ⟨cursor, hc⟩ (some h) : ℤ))
      omega
    · omega

/-- Exact first-match specification. In particular, the returned interval lies among the at
most `fuel` candidates; the carried distance agrees with the schedule throughout the scan. -/
theorem scan_eq_some_iff (σ : Schedule k q) (h : Fin k) (block : ℤ)
    (fuel cursor j : ℕ) :
    scan σ h fuel cursor (scheduleBlock σ cursor (some h) - block) = some j ↔
      cursor ≤ j ∧ j < cursor + fuel ∧ j < q ∧
      |scheduleBlock σ j (some h) - block| ≤ 1 ∧
      ∀ n, cursor ≤ n → n < j → ¬ |scheduleBlock σ n (some h) - block| ≤ 1 := by
  induction fuel generalizing cursor with
  | zero => simp only [scan, reduceCtorEq, false_iff]; omega
  | succ fuel ih =>
    rw [scan]
    split_ifs with hc hd
    · constructor
      · intro he
        cases Option.some.inj he
        exact ⟨le_rfl, by omega, hc, hd, fun n hn hj => by omega⟩
      · rintro ⟨hlo, hhi, hq, hj, hmin⟩
        have : j = cursor := by
          by_contra hn
          exact hmin cursor le_rfl (by omega) hd
        simp [this]
    · have step : scheduleBlock σ cursor (some h) - block +
          (σ ⟨cursor, hc⟩ (some h) : ℤ) =
          scheduleBlock σ (cursor + 1) (some h) - block := by
        rw [scheduleBlock_succ σ hc]
        omega
      rw [step, ih]
      constructor
      · rintro ⟨hlo, hhi, hq, hj, hmin⟩
        refine ⟨by omega, by omega, hq, hj, ?_⟩
        intro n hn hnj
        by_cases he : n = cursor
        · simpa [he] using hd
        · exact hmin n (by omega) hnj
      · rintro ⟨hlo, hhi, hq, hj, hmin⟩
        have hne : j ≠ cursor := by intro he; subst j; exact hd hj
        exact ⟨by omega, by omega, hq, hj, fun n hn hn' => hmin n (by omega) hn'⟩
    · simp only [false_iff]
      omega

/-- The next appearance of an outgoing window block, computed with relative displacement.
There are at most `q - (i + 1)` candidates. -/
@[expose] def next (σ : Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) : Option ℕ :=
  scan σ h (q - (i + 1)) (i + 1) (1 - (d : ℤ) + (σ i (some h) : ℤ))

/-- Relative-distance search computes the existing semantic next-appearance operation. -/
theorem next_eq_firstAfter (σ : Schedule k q) (i : Fin q) (h : Fin k) (d : Fin 3) :
    next σ i h d =
      (firstAfter (InWindow σ h (portBlock σ i h d)) i).map Fin.val := by
  have start : 1 - (d : ℤ) + (σ i (some h) : ℤ) =
      scheduleBlock σ (i + 1) (some h) - portBlock σ i h d := by
    rw [scheduleBlock_succ σ i.isLt]
    simp only [portBlock]
    change 1 - (d : ℤ) + (σ i (some h) : ℤ) =
      scheduleBlock σ i (some h) + (σ i (some h) : ℤ) -
        (scheduleBlock σ i (some h) + (d : ℤ) - 1)
    omega
  have spec (j : Fin q) : next σ i h d = some j.val ↔
      firstAfter (InWindow σ h (portBlock σ i h d)) i = some j := by
    rw [next, start, scan_eq_some_iff, firstAfter_eq_some_iff]
    simp only [InWindow, Fin.lt_def]
    constructor
    · rintro ⟨hlo, _, _, hp, hmin⟩
      exact ⟨by omega, hp, fun n hn hnj => hmin n (by omega) hnj⟩
    · rintro ⟨hlt, hp, hmin⟩
      exact ⟨by omega, by omega, j.isLt, hp,
        fun n hn hnj => hmin ⟨n, by omega⟩ (by simpa using (show i.val < n by omega)) hnj⟩
  cases he : firstAfter (InWindow σ h (portBlock σ i h d)) i with
  | some j => simpa using (spec j).mpr he
  | none =>
    simp only [Option.map_none]
    cases hs : next σ i h d with
    | none => rfl
    | some j =>
      have hj : j < q := (scan_eq_some_iff σ h (portBlock σ i h d)
        (q - (i + 1)) (i + 1) j).mp (by simpa only [next, start] using hs) |>.2.2.1
      have := (spec ⟨j, hj⟩).mp hs
      simp [he] at this

end RelativeSearch

end Turing.MultiTapePTM
