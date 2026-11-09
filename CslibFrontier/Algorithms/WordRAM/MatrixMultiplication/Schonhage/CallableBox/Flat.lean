/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Input

/-!
# Initialized flat callable products

The same final native data witnesses the charged prefix run, exact physical product words,
restored local original input, protected caller memory and the final halt. The program and its
163 registers are fixed independently of dimensions, runtime base and physical word width.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct

open Cslib.WordRAM
open CallableProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized execution with no computed-layout, bounded-scratch or execution premise.
Every original duplicate request has its own exact physical answer cell. The `n+1` charge
includes the halt reached by the same final data `y` in the prefix `Runs`. -/
theorem runs {W m N : ℕ} (t : ℕ) (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (ht : t ≤ m) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hcaller : ∀ v ∈ caller, Fits W v)
    (hfit : Fits W (inputBase caller + 4 * windowSize N qs.length + 1024)) :
    InputFits W (input t caller X Y qs) ∧
    ∃ y n, n ≤ timeBound m t qs + 2 ∧
      Runs W (entryProgram.program Reg.result) (State.init (input t caller X Y qs))
        ⟨entryProgram.size, y⟩ n ∧
      Executes W (entryProgram.program Reg.result) (State.init (input t caller X Y qs))
        (inputBase caller + QueriedProduct.outputBase (21 * m) m N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (inputBase caller + (QueriedProduct.outputBase (21 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length + 1 →
        y.mem (inputBase caller + a) =
          (State.init (input t caller X Y qs) : State 163).data.mem (inputBase caller + a)) ∧
      (∀ a, a < inputBase caller ∨ inputBase caller + windowSize N qs.length ≤ a →
        y.mem a = (State.init (input t caller X Y qs) : State 163).data.mem a) := by
  have hi := input_fits t caller X Y qs ht hN hX hY hcaller hfit
  let x := (State.init (input t caller X Y qs) : State 163).data
  let s := (x.set Reg.address 1).set Reg.base (inputBase caller)
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hread : x.mem 1 = inputBase caller := by simp [x, input, State.init, Data.init]
  have hs : ExecWithin (B := .standard) W
      (ram[ Reg.address ← #1; Reg.base ← *Reg.address ]) x s 2 := by
    ram_eval [s, h1, hread, Reg.address, Reg.base, Fin.mk.injEq]
  obtain ⟨y, hy, yr, yb, yM, yv, yi, yf⟩ := exec X Y qs s
    (by simp [s]) (fun a _ => input_word t caller X Y qs a) hX hY ht hN hfit
  have he : ExecWithin W entryProgram x y (2 + timeBound m t qs) := hs.seq hy
  have ybound : y.Bounded W := he.bounded (by simpa only [x, State.init] using Data.Bounded.init hi)
  obtain ⟨n, hn, he⟩ := he
  refine ⟨hi, y, n, by omega, ?_, ?_, ybound, yv, yi, yf⟩
  · simpa only [Nat.zero_add, x, State.init] using he.runs (pc := 0)
      (p := entryProgram.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [yr, x, State.init] using he.executes Reg.result

set_option maxRecDepth 4096 in
-- This finite syntactic check visits the fixed 160-register normalization sequence.
private theorem setup_size : setup.size ≤ 1024 := by decide +kernel

set_option maxRecDepth 4096 in
-- This finite syntactic check visits the fixed normalization and reused arithmetic routines.
private theorem setup_not_readsWidth : ¬setup.ReadsWidth := by decide +kernel

/-- The complete standalone caller has a fixed finite flat program, including halt. -/
theorem program_length_le : (entryProgram.program Reg.result).length ≤ 131072 := by
  have hp := BoxProduct.program_size_le true
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hp ⊢
  have hc := MemoryWindow.size_compile (BoxProduct.program true)
  have hs := setup_size
  have hi : restoreInput.size = 13 := by decide +kernel
  have ho : returnOutput.size = 13 := by decide +kernel
  have ht : includeThreshold.size = 2 := by decide +kernel
  simp only [entryProgram, program, core, Code.size] at *
  omega

/-- The width-independent code computes its own virtual modulus without reading physical width. -/
theorem not_readsWidth : ¬entryProgram.ReadsWidth := by
  have hr : ¬restoreInput.ReadsWidth := by decide +kernel
  have ho : ¬returnOutput.ReadsWidth := by decide +kernel
  have ht : ¬includeThreshold.ReadsWidth := by decide +kernel
  simp only [entryProgram, program, core, Code.ReadsWidth, Op.ReadsWidth,
    MemoryWindow.readsWidth_compile, BoxProduct.not_readsWidth, setup_not_readsWidth,
    hr, ho, ht, not_false_eq_true, or_self]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct
