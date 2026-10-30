/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Paying for the native catalogue traversal

The remaining potential reserves one successful scan in total. A failed call consumes only
its own distinct failed occurrences; a successful call consumes that reserve and terminates
the traversal. These internal arithmetic lemmas do not provide an execution or cost oracle.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

/-- One actual return consumes its failed occurrences and, only on success, the single reserve.
The base charge includes this iteration's real call/controller/loop overhead. -/
theorem pay_return {T base C scans failures flag restBase restFailures : ℕ}
    (hT : T + 2 ≤ base + C * scans) (hscans : scans ≤ failures + flag)
    (hflag : flag ≤ 1) :
    T + 2 + (restBase + C * (restFailures + 1 - flag)) ≤
      base + restBase + C * (failures + restFailures + 1) := by
  have he : failures + flag + (restFailures + 1 - flag) =
      failures + restFailures + 1 := by omega
  have hpaid := Nat.mul_le_mul_left C hscans
  calc
    _ ≤ base + C * (failures + flag) +
        (restBase + C * (restFailures + 1 - flag)) := by omega
    _ = base + restBase + C * (failures + flag + (restFailures + 1 - flag)) := by ring
    _ = _ := by rw [he]

/-- Nonnegative charges in a visited prefix are bounded by those in the complete range. -/
theorem sum_prefix_le (charge : ℕ → ℕ) {i M : ℕ} (hi : i ≤ M) :
    ∑ j ∈ Finset.range i, charge j ≤ ∑ j ∈ Finset.range M, charge j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hi)

/-- Reserve potential for a concrete finite sequence of base and failed-occurrence charges. -/
@[expose] def remainingCharge (base failures : ℕ → ℕ) (C M i flag : ℕ) : ℕ :=
  ((∑ j ∈ Finset.range M, base j) - (∑ j ∈ Finset.range i, base j)) +
    C * (((∑ j ∈ Finset.range M, failures j) -
      (∑ j ∈ Finset.range i, failures j)) + 1 - flag)

/-- The actual per-call bound decreases the potential by the charged body and loop work.
The loop invariant establishes zero prior success whenever its guard still holds. -/
theorem remainingCharge_step {base failures : ℕ → ℕ} {C M i T scans flag : ℕ}
    (hi : i < M) (hT : T + 2 ≤ base i + C * scans)
    (hscans : scans ≤ failures i + flag) (hflag : flag ≤ 1) :
    T + 2 + remainingCharge base failures C M (i + 1) flag ≤
      remainingCharge base failures C M i 0 := by
  have hB := sum_prefix_le base (Nat.succ_le_of_lt hi)
  have hF := sum_prefix_le failures (Nat.succ_le_of_lt hi)
  rw [Finset.sum_range_succ] at hB hF
  have eqB : (∑ j ∈ Finset.range M, base j) - (∑ j ∈ Finset.range i, base j) =
      base i + ((∑ j ∈ Finset.range M, base j) -
        ((∑ j ∈ Finset.range i, base j) + base i)) := by omega
  have eqF : (∑ j ∈ Finset.range M, failures j) - (∑ j ∈ Finset.range i, failures j) =
      failures i + ((∑ j ∈ Finset.range M, failures j) -
        ((∑ j ∈ Finset.range i, failures j) + failures i)) := by omega
  unfold remainingCharge
  rw [Finset.sum_range_succ, Finset.sum_range_succ, eqB, eqF]
  simpa only [Nat.sub_zero, Nat.add_assoc] using pay_return hT hscans hflag

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
