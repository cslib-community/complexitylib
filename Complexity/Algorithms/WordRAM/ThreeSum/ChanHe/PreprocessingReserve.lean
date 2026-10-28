/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram

/-!
# Executing the native ternary reservation

The forest controller computes its output reservation by actual multiplications and a native
countdown. The loop has no supplied exponentiation instruction or resource oracle.

## Main results

* `reserve_exec`: exact native power, loop count, memory frame and register frame.

The controller proof and its charged bound are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- The power loop changes only its accumulator and countdown. -/
theorem reserve_preserves : ∀ i : Fin 128, i ≠ power → i ≠ remaining → reserve.Preserves i :=
  by decide

/-- Actual multiplication and subtraction compute the complete ternary-tree reservation. -/
theorem reserve_exec {w F : ℕ} (x : Data 128)
    (hp : x.regs power = 1) (hr : x.regs remaining = F + 1)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hs : x.regs scalar = 3)
    (hfit : Fits w (3 ^ (F + 1))) :
    ∃ y, ExecWithin w reserve x y (4 * (F + 1) + 2) ∧
      y.regs power = 3 ^ (F + 1) ∧ y.regs remaining = 0 ∧ y.mem = x.mem ∧
      ∀ i : Fin 128, i ≠ power → i ≠ remaining → y.regs i = x.regs i := by
  let I (y : Data 128) : Prop :=
    y.regs remaining ≤ F + 1 ∧ y.regs power = 3 ^ (F + 1 - y.regs remaining) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧ y.regs scalar = 3 ∧ y.mem = x.mem
  have hbody (y : Data 128) (hy : I y) (hc : (Cond.lt zero remaining).Holds y) :
      ∃ z, ExecWithin w powerBody y z 2 ∧ I z ∧
        z.regs remaining < y.regs remaining := by
    rcases hy with ⟨hle, hpow, hzero, hone, hscalar, hmem⟩
    have hpos : 0 < y.regs remaining := by
      simpa only [Cond.holds_lt, hzero] using hc
    have hmul : Fits w (y.regs power * y.regs scalar) := by
      rw [hpow, hscalar, ← pow_succ]
      exact hfit.of_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hsub : Fits w (y.regs remaining - 1) := hfit.of_le (by
      have hp : F + 1 < 3 ^ (F + 1) := Nat.lt_pow_self (by decide)
      omega)
    let z := (y.set power (y.regs power * y.regs scalar)).set remaining
      (y.regs remaining - 1)
    have he : Exec w powerBody y z 2 := by
      ram_eval [powerBody, z, hone, hmul, hsub, power, remaining, scalar, one]
    refine ⟨z, he.within, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, hmem⟩
      · change y.regs remaining - 1 ≤ F + 1
        omega
      · change y.regs power * y.regs scalar = 3 ^ (F + 1 - (y.regs remaining - 1))
        rw [hpow, hscalar, ← pow_succ]
        congr 1
        omega
      · simpa +decide [z, Data.set, zero, power, remaining] using hzero
      · simpa +decide [z, Data.set, one, power, remaining] using hone
      · simpa +decide [z, Data.set, scalar, power, remaining] using hscalar
    · change y.regs remaining - 1 < y.regs remaining
      omega
  have hx : I x := by
    refine ⟨by omega, ?_, hz, ho, hs, rfl⟩
    rw [hp, hr, Nat.sub_self, pow_zero]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => y.regs remaining) hbody hx
  have hend : y.regs remaining = 0 := by
    have hzero := hy.2.2.1
    simpa only [Cond.holds_lt, hzero, not_lt, Nat.le_zero] using hc
  refine ⟨y, ?_, ?_, hend, hy.2.2.2.2.2, ?_⟩
  · simpa only [reserve, hr, Nat.reduceAdd, Nat.mul_comm] using he
  · simpa only [hend, Nat.sub_zero] using hy.2.1
  · intro i hi hj
    exact he.regs_eq (reserve_preserves i hi hj)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
