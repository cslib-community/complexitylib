/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Width
public import Complexity.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Actual initialized halting modular counter and every-wide-width prefixes

The fixed standard-native program starts from the original header and signed matrix words.
Its prefix witness, raw count and charged halt refer to the same actual final memory. Every
wider admitted prefix agrees with a minimum-admission execution; the resulting word/support
bounds depend only on original inputs and not on the chosen physical width.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Complete initialized flat execution, exact raw count and all setup/recursion/halt charges. -/
theorem runs_input {W n p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n p A ≤ W) :
    InputFits W (inputWords n p values) ∧
    ∃ y t, t + 1 ≤ cost n p + 10 ∧
      Runs W (entryProgram.program Reg.result) (State.init (inputWords n p values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result) (State.init (inputWords n p values))
        (y.regs Reg.result) (t + 1) ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p ∧
      y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨ memoryEnd n p (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (inputWords n p values) : Data 128).mem d := by
  obtain ⟨hi, y, he, result, bounded, frame⟩ := exec_input values hlen hp hv hW
  obtain ⟨t, ht, run⟩ := he
  refine ⟨hi, y, t, by omega, ?_, ?_, result, bounded, frame⟩
  · simpa only [State.init, Nat.zero_add] using run.runs (pc := 0)
      (p := entryProgram.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [State.init] using run.executes Reg.result

private theorem pow_width_lt (n p A : ℕ) :
    2 ^ admissionWidth n p A < wordBound n p A := by
  let E := envelope n p A
  let k := Nat.clog 2 E
  have hB : 0 < addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n)) 3 (3 + n * n)
      (3 + 2 * (n * n)) := by unfold addressBudget; positivity
  have hE : 1 < E := by dsimp only [E, envelope]; omega
  have hkpos : 0 < k := Nat.clog_pos (by decide) hE
  have hk : k.pred + 1 = k := Nat.succ_pred_eq_of_pos hkpos
  have hpred : 2 ^ k.pred < E := Nat.pow_pred_clog_lt_self (by decide) hE
  change 2 ^ (k + 3) < 16 * E
  calc
    _ = 2 ^ k * 8 := by rw [Nat.pow_add]
    _ = 2 ^ (k.pred + 1) * 8 := congrArg (fun j => 2 ^ j * 8) hk.symm
    _ = (2 ^ k.pred * 2) * 8 := by rw [Nat.pow_succ]
    _ < 16 * E := by omega

/-- Every successful prefix has original-input bounded words and zero memory beyond the same
width-independent support envelope. The premise is an actual program prefix, not a supplied
execution/correctness certificate used by the algorithm. -/
theorem bounded_reachable {W n p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n p A ≤ W)
    (s : State 128) (steps : ℕ)
    (hr : Runs W (entryProgram.program Reg.result) (State.init (inputWords n p values)) s steps) :
    (∀ i, s.data.regs i < wordBound n p A) ∧
      (∀ a, s.data.mem a < wordBound n p A) ∧
      ∀ a, wordBound n p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_input values hlen hp hv le_rfl
  have low := Runs.prefix_at_smaller_width program_fixed.2 hW hr halt
  have bounded := low.bounded_init hi
  have hword := pow_width_lt n p A
  refine ⟨fun i => (bounded.1 i).trans hword, fun a => (bounded.2 a).trans hword, ?_⟩
  intro a ha
  have above : 2 ^ admissionWidth n p A ≤ a := hword.le.trans ha
  rw [low.mem_above (.init hi) above]
  cases a with
  | zero => have := Nat.two_pow_pos (admissionWidth n p A); omega
  | succ a =>
    change (inputWords n p values).getD a 0 = 0
    apply List.getD_eq_default
    have hl := hi.1
    dsimp only [Fits] at hl
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
