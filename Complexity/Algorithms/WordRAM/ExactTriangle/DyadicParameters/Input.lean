/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Exec
public import Complexity.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Initialized halting native parameter preparation

Input is the single raw original dimension n. The actual header, logarithm, two powers,
parameter readback and regime flag all refer to one final state. The same code works at every
larger admitted physical width. All original memory is preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Positive physical width admitting the original scalar and every computed parameter. -/
@[expose] def admissionWidth (n : ℕ) : ℕ := Nat.clog 2 (wordBudget n + 1)

/-- The original scalar is loaded by two actual native instructions before parameter setup. -/
@[expose] def entryProgram : Code .standard 16 :=
  .seq (ram[ Reg.divisor ← #1; Reg.side ← *Reg.divisor ]) program

/-- The initialized code remains fixed, including halt, and cannot read physical width. -/
theorem entryProgram_fixed : (entryProgram.program Reg.fast).length ≤ 128 ∧
    ¬(entryProgram.program Reg.fast).ReadsWidth := by decide +kernel

/-- The original-input width threshold is always positive. -/
theorem admissionWidth_pos (n : ℕ) : 0 < admissionWidth n := by
  apply Nat.clog_pos (by decide)
  unfold wordBudget
  omega

/-- Actual initialized execution at every admitted width. All original memory is preserved. -/
theorem exec_input {W n : ℕ} (hW : admissionWidth n ≤ W) :
    InputFits W [n] ∧
    ∃ y, ExecWithin W entryProgram (.init [n]) y (timeBound n + 2) ∧
      y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
      y.regs Reg.level = ParameterChoice.level n ∧ y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.groups = ParameterChoice.groups n ∧
      y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.Bounded W ∧ y.mem = (Data.init [n] : Data 16).mem := by
  have hfit : Fits W (wordBudget n) :=
    ((by omega : wordBudget n < wordBudget n + 1).trans_le
      (Nat.le_pow_clog (by decide) _)).trans_le
        (Nat.pow_le_pow_right (by decide) hW)
  have h1 : Fits W 1 := hfit.of_le (by unfold wordBudget; omega)
  have hn : Fits W n := hfit.of_le (by unfold wordBudget; omega)
  have hi : InputFits W [n] := ⟨by simpa using h1, by simpa using hn⟩
  let x := ((Data.init (r := 16) [n]).set Reg.divisor 1).set Reg.side n
  have header : ExecWithin (B := .standard) W
      (ram[ Reg.divisor ← #1; Reg.side ← *Reg.divisor ]) (.init [n]) x 2 := by
    ram_eval [x, h1, hn, Reg.divisor, Reg.side, Data.init, List.getD, Fin.mk.injEq]
  obtain ⟨y, he, hs, hb, hl, hd, hg, hL, hf, hm⟩ := exec x (by rfl) hfit
  have full : ExecWithin W entryProgram (.init [n]) y (timeBound n + 2) :=
    (header.seq he).mono (by omega)
  exact ⟨hi, y, full, hs, hb, hl, hd, hg, hL, hf, full.bounded (.init hi), hm⟩

/-- Same-state actual prefix and halt, with every output connected to the original dimension.
All instructions, including input loading and halt, have logarithmic total charge. -/
theorem runs_input {W n : ℕ} (hW : admissionWidth n ≤ W) :
    InputFits W [n] ∧
    ∃ y t, t + 1 ≤ 12 * Nat.log 2 n + 36 ∧
      Runs W (entryProgram.program Reg.fast) (State.init [n]) ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.fast) (State.init [n]) (y.regs Reg.fast) (t + 1) ∧
      y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
      y.regs Reg.level = ParameterChoice.level n ∧ y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.groups = ParameterChoice.groups n ∧
      y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.Bounded W ∧ y.mem = (Data.init [n] : Data 16).mem := by
  obtain ⟨hi, y, ⟨t, ht, he⟩, hs, hb, hl, hd, hg, hL, hf, hy, hm⟩ := exec_input hW
  have budget := timeBound_le n
  refine ⟨hi, y, t, by omega, ?_, ?_, hs, hb, hl, hd, hg, hL, hf, hy, hm⟩
  · simpa only [State.init, Nat.zero_add] using he.runs (pc := 0)
      (p := entryProgram.program Reg.fast) (Program.Contains.self _).append_left
  · simpa only [State.init] using he.executes Reg.fast

/-- Every successful wider prefix has words and support controlled by original n rather than
that chosen physical width. -/
theorem bounded_reachable {W n : ℕ} (hW : admissionWidth n ≤ W)
    (s : State 16) (t : ℕ)
    (hr : Runs W (entryProgram.program Reg.fast) (State.init [n]) s t) :
    (∀ i, s.data.regs i < 2 ^ admissionWidth n) ∧
      (∀ a, s.data.mem a < 2 ^ admissionWidth n) ∧
      ∀ a, 2 ^ admissionWidth n ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_input (n := n) le_rfl
  have low := Runs.prefix_at_smaller_width entryProgram_fixed.2 hW hr halt
  have bounded := low.bounded_init hi
  refine ⟨bounded.1, bounded.2, ?_⟩
  intro a ha
  rw [low.mem_above (.init hi) ha]
  cases a with
  | zero => have := Nat.two_pow_pos (admissionWidth n); omega
  | succ a =>
    change ([n] : List ℕ).getD a 0 = 0
    apply List.getD_eq_default
    have hl := hi.1
    dsimp only [Fits] at hl
    simp only [List.length_singleton] at hl ⊢
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
