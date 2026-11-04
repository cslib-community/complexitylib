/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleRead
public import
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph

/-!
# Correctness of streaming schedule digit counts

The streamed counter agrees with the existing numeric schedule semantics `digitCount`. Its
remaining suffix never exceeds the original schedule number, and its counter never exceeds the
number of processed rows, including when the schedule number is zero.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

/-- The remaining schedule is the original number with exactly `i` rows discarded. This
identity specifies the stream; its runtime implementation does not construct the power. -/
theorem iterate_fst (k c δ σ i : ℕ) :
    ((step k c δ)^[i] (σ, 0)).1 = σ / 3 ^ ((k + 1) * i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change ((step k c δ)^[i] (σ, 0)).1 / 3 ^ (k + 1) = _
    rw [ih, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]

/-- Counting streamed rows gives the existing schedule digit count. -/
theorem iterate_snd (k c δ σ i : ℕ) :
    ((step k c δ)^[i] (σ, 0)).2 = digitCount k σ c δ i := by
  induction i with
  | zero => simp [digitCount]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change ((step k c δ)^[i] (σ, 0)).2 +
      (if ((step k c δ)^[i] (σ, 0)).1 / 3 ^ c % 3 = δ then 1 else 0) = _
    rw [ih, iterate_fst]
    have hd : σ / 3 ^ ((k + 1) * i) / 3 ^ c = σ / 3 ^ (c + (k + 1) * i) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm ((k + 1) * i) c]
    simp only [hd, digitCount, List.range_succ, List.countP_append, List.countP_singleton,
      decide_eq_true_eq]

/-- Streamed counting uses the library's existing numeric schedule interpretation. -/
theorem read_eq_digitCount (k c δ σ i : ℕ) :
    read k c δ (σ, i) = digitCount k σ c δ i :=
  iterate_snd k c δ σ i

/-- Discarding rows cannot enlarge the stored schedule number. -/
theorem iterate_fst_le (k c δ σ i : ℕ) :
    ((step k c δ)^[i] (σ, 0)).1 ≤ σ := by
  rw [iterate_fst]
  exact Nat.div_le_self _ _

/-- The counter grows by at most one per processed row. -/
theorem iterate_snd_le (k c δ σ i : ℕ) :
    ((step k c δ)^[i] (σ, 0)).2 ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change ((step k c δ)^[i] (σ, 0)).2 +
      (if ((step k c δ)^[i] (σ, 0)).1 / 3 ^ c % 3 = δ then 1 else 0) ≤ i + 1
    split_ifs <;> omega

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
