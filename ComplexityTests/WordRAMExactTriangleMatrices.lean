/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.WriteMatrices
import Complexity.Computability.WordRAM.Compile

/-! # Native ET instance-matrix clients

The input to these local matrix-builder clients is an unsigned residue matrix. The complete ET
frontend must first produce those residues from signed weights and compute the instance catalogue.
-/

namespace ComplexityTests.WordRAMExactTriangleMatrices

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle.WriteMatrices

private def boot : Code .standard 17 := ram[
  one ← #1; idx ← #1; src ← *idx; idx ← idx + one; dst ← *idx; idx ← idx + one;
  size ← *idx; idx ← idx + one; dimension ← *idx; idx ← idx + one;
  modulus ← *idx; idx ← idx + one; first ← *idx; idx ← idx + one;
  length ← *idx; idx ← idx + one; rho ← *idx ]

private def input (n D p c len r : ℕ) (R : List ℕ) : List ℕ :=
  [9, 9 + R.length, n, D, p, c, len, r] ++ R ++ List.replicate (n * D) 77 ++ [99]

private def code (side : Bool) : Code .standard 17 := .seq boot (program side)

private def observe (side : Bool) (w n D p c len r : ℕ) (R : List ℕ) :
    Option (List ℕ × ℕ × ℕ) :=
  ((code side).eval w (n * D + 1) (.init (input n D p c len r R))).map fun yn =>
    ((List.range (n * D)).map fun i => yn.1.mem (9 + R.length + i),
      yn.1.mem (9 + R.length + n * D), yn.1.regs idx)

/-- Two source rows, all three labels, and an extra padded middle position. -/
example : observe false 8 2 7 3 0 2 1 [0, 1, 2, 0] =
    some ([0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0], 99, 14) := by decide

/-- The right matrix uses the negated residue and the transposed input indices. -/
example : observe true 8 2 7 3 0 2 1 [0, 1, 2, 0] =
    some ([1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], 99, 14) := by decide

/-- A shifted one-vertex piece reads the second column of the residue input. -/
example : observe false 8 2 4 3 1 1 2 [0, 1, 2, 0] =
    some ([1, 0, 0, 0, 0, 0, 1, 0], 99, 8) := by decide

example : observe true 8 2 4 3 1 1 2 [0, 1, 2, 0] =
    some ([0, 1, 0, 0, 1, 0, 0, 0], 99, 8) := by decide

/-- An empty outer part performs no stores and keeps the adjacent sentinel. -/
example : observe false 8 0 5 3 0 0 1 [] = some ([], 99, 0) := by decide

/-- A physical width too small for the matrix's addresses faults during actual execution. -/
example : observe true 4 2 7 3 0 2 1 [0, 1, 2, 0] = none := by decide

private def leftArgs : Args := ⟨9, 13, 2, 7, 3, 0, 2, 1⟩
private def residues (i : ℕ) : ℕ := [0, 1, 2, 0].getD i 0
private def leftInput : List ℕ := input 2 7 3 0 2 1 [0, 1, 2, 0]
private def leftOutput : List ℕ := [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]

/-- The quantitative theorem applies after a charged native header load. The witness is tied
to the actual initialized compiled run, all fourteen expected entries and the outside sentinel. -/
example : ∃ y t, t ≤ 304 ∧
    Runs 8 ((code false).program dst) (State.init leftInput) ⟨(code false).size, y⟩ (t - 1) ∧
    Executes 8 ((code false).program dst) (State.init leftInput) 13 t ∧
    (Block.mk 13 14).Realizes y.mem (fun i => leftOutput.getD i 0) ∧
    y.mem 27 = 99 ∧ y.Bounded 8 := by
  obtain ⟨b, hb, hba, hbm⟩ : ∃ b,
      ExecWithin 8 boot (.init leftInput) b 17 ∧ Entry leftArgs b ∧
        b.mem = (Data.init leftInput : Data 17).mem := by
    refine ⟨?b, ?run, ?args, ?memory⟩
    case run => ram_eval [boot, leftInput, input, Data.init, Fits]
    case args => constructor <;> decide
    case memory => rfl
  obtain ⟨y, hy, hya, -, hmatrix, hframe⟩ := exec (w := 8) false leftArgs residues b hba
    (by decide) (by decide)
    (by
      intro i hi
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
      rcases h with rfl | rfl | rfl | rfl <;> decide)
    (by
      intro i hi
      rw [hbm]
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
      rcases h with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t, ht, he⟩ := hb.seq hy
  have hr := he.runs (pc := 0) (p := (code false).program dst)
    (Program.Contains.self _).append_left
  refine ⟨y, t + 1, by exact Nat.add_le_add_right ht 1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel, Nat.zero_add, code, State.init] using hr
  · simpa only [code, State.init, hya.dst, leftArgs] using he.executes dst
  · have hv : ∀ i : Fin 14, entry false leftArgs residues i = leftOutput.getD i 0 := by decide
    intro i
    exact (hmatrix i).trans (hv i)
  · exact (hframe 27 (by change ¬(13 ≤ 27 ∧ 27 < 27); omega)).trans (congrFun hbm 27)
  · exact hr.bounded_init (by decide : InputFits 8 leftInput)

end ComplexityTests.WordRAMExactTriangleMatrices
