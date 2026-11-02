/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Input
import Complexity.Foundations.Data.Nat.Log

/-!
# Logarithmic admission and polynomial prefixes for parameter preparation

These original-scalar bounds include all fixed constants, the input header and both actual
power calls. They hold for every n, including zero and the small regime.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM

private theorem budget_le_pow (n : ℕ) : wordBudget n + 1 ≤ (n + 2) ^ 12 := by
  have hconst : 1329 ≤ (n + 2) ^ 11 :=
    (show 1329 ≤ (2 : ℕ) ^ 11 by decide).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 11)
  calc
    _ ≤ 1329 * (n + 2) := by unfold wordBudget; omega
    _ ≤ (n + 2) ^ 11 * (n + 2) := Nat.mul_le_mul_right _ hconst
    _ = _ := (pow_succ (n + 2) 11).symm

/-- A fixed multiple of the original input-size logarithm suffices at every dimension. -/
theorem admissionWidth_le_log (n : ℕ) : admissionWidth n ≤ 12 * Nat.clog 2 (n + 2) := by
  have hp := (budget_le_pow n).trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 2)) 12)
  rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (n + 2)) 12] at hp
  exact Nat.clog_le_of_le_pow hp

private theorem threshold_pow_le (n : ℕ) : 2 ^ admissionWidth n ≤ (n + 2) ^ 13 := by
  calc
    _ ≤ 2 * (wordBudget n + 1) := Nat.pow_clog_le_mul (by decide) (by omega)
    _ ≤ 2 * (n + 2) ^ 12 := Nat.mul_le_mul_left _ (budget_le_pow n)
    _ ≤ (n + 2) * (n + 2) ^ 12 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_succ' (n + 2) 12).symm

/-- All successful prefixes at every sufficiently wide physical width have polynomial words
and support independent of that width. The input is just the original raw dimension. -/
theorem bounded_reachable_polynomial {W n : ℕ}
    (hW : 12 * Nat.clog 2 (n + 2) ≤ W) (s : State 16) (t : ℕ)
    (hr : Runs W (entryProgram.program Reg.fast) (State.init [n]) s t) :
    (∀ i, s.data.regs i < (n + 2) ^ 13) ∧ (∀ a, s.data.mem a < (n + 2) ^ 13) ∧
      ∀ a, (n + 2) ^ 13 ≤ a → s.data.mem a = 0 := by
  obtain ⟨regs, mem, support⟩ := bounded_reachable ((admissionWidth_le_log n).trans hW) s t hr
  have hb := threshold_pow_le n
  exact ⟨fun i => (regs i).trans_le hb, fun a => (mem a).trans_le hb,
    fun a ha => support a (hb.trans ha)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
