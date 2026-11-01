/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Input

/-!
# Actual initialized halting parameter-selecting ExactTriangle execution

Original raw n,F and the three signed matrices are the complete input. The program computes
all parameters and its prime, executes the valid large or actual exhaustive small branch,
and returns the exact original ET verdict. Prefix, halt, restored arguments and frame all
refer to the same final state. No aggregate exponent or execution/selection oracle is assumed.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Numerical original-input threshold for the actual header and complete assembled program. -/
@[expose] def inputWidth (n F : ℕ) (values : List ℤ) : ℕ :=
  executionWidth n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values

/-- One fixed initialized standard-native program; header, complete body and halt are included. -/
theorem entryProgram_fixed : (entryProgram.program Reg.result).length ≤ 434015 ∧
    ¬(entryProgram.program Reg.result).ReadsWidth := by
  have size : entryProgram.size = entryHeader.size + program.size := by
    dsimp only [entryProgram, Code.size]
  refine ⟨?_, Code.not_readsWidth_program ?_ _⟩
  · have h := program_fixed.1
    simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton] at h ⊢
    rw [size, entryHeader_fixed.1]
    omega
  · simpa only [entryProgram, Code.ReadsWidth, not_or] using
      And.intro entryHeader_fixed.2 program_not_readsWidth

/-- Actual initialized execution at every admitted width, including zero vertices and the
entire small regime. The returned prime is real selection on the fast branch and zero otherwise. -/
theorem runs_input {W n F : ℕ} (values : List ℤ) (hlen : values.length = 3 * (n * n))
    (hv : ∀ z ∈ values, z.natAbs ≤ F) (hW : inputWidth n F values ≤ W) :
    let V := fun q => values.getD q 0
    let A := fun i j : Fin n => V (pairIndex (i, j))
    let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
    let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
    InputFits W (CountPrime.inputWords n F values) ∧
      ∃ (p : ℕ) (mem : ℕ → ℕ) (y : Data 640) (t : ℕ),
        t + 1 ≤ timeBound n p values mem + 16 ∧
        Runs W (entryProgram.program Reg.result) (State.init (CountPrime.inputWords n F values))
          ⟨entryProgram.size, y⟩ t ∧
        Executes W (entryProgram.program Reg.result)
          (State.init (CountPrime.inputWords n F values)) (y.regs Reg.result) (t + 1) ∧
        y.Bounded W ∧ (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
        (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
        (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
        (¬0 < ParameterChoice.blocks n → p = 0) ∧
        (∀ q, q < 3 + 3 * (n * n) ∨ workspaceEnd n (3 + 3 * (n * n)) values ≤ q →
          y.mem q = (Data.init (CountPrime.inputWords n F values) : Data 640).mem q) ∧
        y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = 3 ∧
        y.regs Reg.bc = 3 + n * n ∧ y.regs Reg.ac = 3 + 2 * (n * n) ∧
        y.regs Reg.free = 3 + 3 * (n * n) := by
  have hi := input_fits values hlen hv hW
  have hfit : Fits W (3 + 3 * (n * n) + 8) :=
    (envelope_fits values hW).of_le (by dsimp only [envelope]; omega)
  obtain ⟨a, ha, am, an, aF, ab, ac, ad, af⟩ := exec_entryHeader
    (n := n) (F := F) (.init (CountPrime.inputWords n F values)) rfl rfl hfit
  have word (q : ℕ) : a.mem (3 + q) = Signed.encode (values.getD q 0) := by
    rw [am]
    simpa only [Data.init] using CountPrime.input_word n F values q
  obtain ⟨p, mem, y, hy, yf, yiff, yp, yz, frame, yn, yF, ya, yb, yc, yfree⟩ :=
    exec_at values hlen hv a an aF ab ac ad af (by omega) (by omega) (by omega)
      (fun q _ => word q)
      (fun q _ => by simpa only [Nat.add_assoc] using word (n * n + q))
      (fun q _ => by simpa only [Nat.add_assoc] using word (2 * (n * n) + q)) hW
  have he : ExecWithin W entryProgram (.init (CountPrime.inputWords n F values)) y
      (15 + timeBound n p values mem) := ha.seq hy
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, p, mem, y, t, ?_, ?_, ?_, hex.bounded (.init hi), yf, yiff, yp, yz,
    ?_, yn, yF, ya, yb, yc, yfree⟩
  · exact (Nat.add_le_add_right ht 1).trans_eq (by omega)
  · simpa only [State.init, Nat.zero_add] using hex.runs (pc := 0)
      (p := entryProgram.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [State.init] using hex.executes Reg.result
  · intro q hq
    exact (frame q hq).trans (congrFun am q)

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
