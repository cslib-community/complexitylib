/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Width
import Mathlib.Data.List.GetD

/-!
# Initialized halting minimum-count prime selection

The prefix, selected prime, raw modular count and charged halt all refer to the same actual
final machine state. Every successful prefix at a larger admitted physical width agrees with
the minimum-admission execution; prefix bounds therefore need not depend on physical width.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Actual original-input prefix and charged halt, with a selected minimum-count prime and
the exact associated modular count in the same final state. -/
theorem runs_input {W n D A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n D A ≤ W) :
    InputFits W (CountPrime.inputWords n D values) ∧
    ∃ y t, t + 1 ≤ timeBound n D + 16 ∧
      Runs W (entryProgram.program Reg.best) (State.init (CountPrime.inputWords n D values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.best) (State.init (CountPrime.inputWords n D values))
        (y.regs Reg.best) (t + 1) ∧
      y.regs Reg.found = 1 ∧
      Cslib.Algorithms.ExactTriangle.IsSelectedPrime
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        D (y.regs Reg.best) ∧
      y.regs Reg.bestCount = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0)
        (y.regs Reg.best) ∧ y.Bounded W ∧
      ∀ d, d < 3 + 3 * (n * n) ∨
          CountPrime.memoryEnd n (Nat.sqrt D) (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (CountPrime.inputWords n D values) : Data 160).mem d := by
  obtain ⟨hi, y, ⟨t, ht, he⟩, hf, hp, hc, hb, hm⟩ := exec_input values hlen hD hv hW
  refine ⟨hi, y, t, by omega, ?_, ?_, hf, hp, hc, hb, hm⟩
  · simpa only [State.init, Nat.zero_add] using he.runs (pc := 0)
      (p := entryProgram.program Reg.best) (Program.Contains.self _).append_left
  · simpa only [State.init] using he.executes Reg.best

/-- All words and support of any successful wider prefix are bounded by the original-input
minimum width, not by the chosen physical width. -/
theorem bounded_reachable {W n D A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n D A ≤ W)
    (s : State 160) (steps : ℕ)
    (hr : Runs W (entryProgram.program Reg.best)
      (State.init (CountPrime.inputWords n D values)) s steps) :
    (∀ i, s.data.regs i < 2 ^ admissionWidth n D A) ∧
      (∀ a, s.data.mem a < 2 ^ admissionWidth n D A) ∧
      ∀ a, 2 ^ admissionWidth n D A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_input values hlen hD hv le_rfl
  have low := Runs.prefix_at_smaller_width program_fixed.2 hW hr halt
  have bounded := low.bounded_init hi
  refine ⟨bounded.1, bounded.2, ?_⟩
  intro a ha
  rw [low.mem_above (.init hi) ha]
  cases a with
  | zero => have := Nat.two_pow_pos (admissionWidth n D A); omega
  | succ a =>
    change (CountPrime.inputWords n D values).getD a 0 = 0
    apply List.getD_eq_default
    have hl := hi.1
    dsimp only [Fits] at hl
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
