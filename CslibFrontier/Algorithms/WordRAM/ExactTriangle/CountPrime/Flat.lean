/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CountPrime.Width
public import CslibFrontier.Computability.WordRAM.Width
import Mathlib.Data.List.GetD
import CslibFrontier.Algorithms.WordRAM.NatClog

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
  have h : 2 ^ k < 2 * E := NatClog.two_pow_clog_lt_two_mul hE
  change 2 ^ (k + 3) < 16 * E
  rw [pow_add]
  omega

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
  exact hr.prefix_bounds_init program_fixed.2 hW hi halt (pow_width_lt n p A).le

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
