/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue
import Complexity.Algorithms.WordRAM.ExactTriangle.Chunks
import Complexity.Algorithms.WordRAM.ExactTriangle.Parameters
import Complexity.Computability.WordRAM.Compile

/-! # Native ET chunk-boundary and parameter clients -/

namespace ComplexityTests.WordRAMExactTriangleChunks

open Cslib.WordRAM

namespace Chunk

open Cslib.Algorithms.WordRAM.ExactTriangle.Chunks

private def boot : Code .standard 14 := ram[
  one ← #1; addr ← #1; queries ← *addr; addr ← addr + one; dst ← *addr;
  addr ← addr + one; total ← *addr; addr ← addr + one; capacity ← *addr;
  addr ← addr + one; residue ← *addr ]

private def input (n cap rho : ℕ) : List ℕ :=
  [6, 6 + 2 * n, n, cap, rho] ++ List.range (2 * n) ++ List.replicate (3 * n + 3) 88 ++ [99]

private def code : Code .standard 14 := .seq boot program

private def observe (w n cap rho : ℕ) : Option (List (ℕ × ℕ × ℕ) × ℕ × ℕ) :=
  (code.eval w (n + 1) (.init (input n cap rho))).map fun yn =>
    ((List.range (yn.1.regs count)).map (fun k =>
      (yn.1.mem (6 + 2 * n + 3 * k), yn.1.mem (6 + 2 * n + 3 * k + 1),
        yn.1.mem (6 + 2 * n + 3 * k + 2))),
      yn.1.mem (6 + 5 * n + 3), yn.1.mem 6)

example : observe 8 5 2 7 = some ([(7, 6, 2), (7, 10, 2), (7, 14, 1)], 99, 0) := by decide

example : observe 8 4 2 7 = some ([(7, 6, 2), (7, 10, 2)], 99, 0) := by decide

example : observe 8 2 1 3 = some ([(3, 6, 1), (3, 8, 1)], 99, 0) := by decide

example : observe 8 0 3 7 = some ([], 99, 88) := by decide

/-- Insufficient address width faults in the real descriptor writer. -/
example : observe 4 5 2 7 = none := by decide

private def raw : List ℕ := input 5 2 7

/-- The complete descriptor theorem is instantiated at a shortened last chunk and connected
to the initialized compiled execution. The source pair words and outside sentinel are retained. -/
example : ∃ y t, t ≤ 104 ∧
    Runs 8 (code.program count) (State.init raw) ⟨code.size, y⟩ (t - 1) ∧
    Executes 8 (code.program count) (State.init raw) 3 t ∧
    y.mem 22 = 7 ∧ y.mem 23 = 14 ∧ y.mem 24 = 1 ∧ y.mem 6 = 0 ∧ y.mem 34 = 99 := by
  obtain ⟨b, hb, hregs, hmem⟩ : ∃ b,
      ExecWithin 8 boot (.init raw) b 11 ∧
        (b.regs queries = 6 ∧ b.regs dst = 16 ∧ b.regs total = 5 ∧
          b.regs capacity = 2 ∧ b.regs residue = 7) ∧
        b.mem = (Data.init raw : Data 14).mem := by
    refine ⟨?b, ?run, ?args, ?memory⟩
    case run => ram_eval [boot, raw, input, Data.init, Fits]
    case args => decide
    case memory => rfl
  obtain ⟨hq, hd, hn, hc, hrho⟩ := hregs
  obtain ⟨y, hy, hycount, -, hcells, hframe⟩ := exec (w := 8) b
    (by rw [hc]; decide) (by rw [hd, hn]; decide) (by rw [hq, hn]; decide)
  have hcount : y.regs count = 3 := by simpa [hn, hc, Nat.ceilDiv_eq_add_pred_div] using hycount
  have hlast := hcells 2 (by rw [hcount]; decide)
  obtain ⟨t, ht, he⟩ := hb.seq hy
  have hr := he.runs (pc := 0) (p := code.program count)
    (Program.Contains.self _).append_left
  have ht' : t ≤ 103 := by simpa only [hn] using ht
  refine ⟨y, t + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [code, State.init, Nat.zero_add, Nat.add_sub_cancel] using hr
  · simpa only [code, State.init, hcount] using he.executes count
  · simpa [hd, hrho] using hlast.1
  · simpa [hd, hq, hc] using hlast.2.1
  · simpa [hd, hn, hc] using hlast.2.2
  · exact (hframe 6 (by rw [hd, hcount]; decide)).trans (congrFun hmem 6)
  · exact (hframe 34 (by rw [hd, hcount]; decide)).trans (congrFun hmem 34)

end Chunk

namespace Catalogue

open Cslib.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue

private def boot : Code .standard 32 := ram[
  one ← #1; addr ← #1; counts ← *addr; addr ← addr + one; queries ← *addr;
  addr ← addr + one; size ← *addr; addr ← addr + one; modulus ← *addr;
  addr ← addr + one; dst ← *addr; addr ← addr + one; capacity ← *addr ]

private def input : List ℕ :=
  [7, 10, 2, 3, 35, 2] ++ [0, 3, 4] ++ List.range 24 ++ [99] ++
    List.replicate 12 88 ++ [77]

private def code : Code .standard 32 := .seq boot program

private def observe : Option (List (ℕ × ℕ × ℕ) × List ℕ) :=
  (code.eval 8 8 (.init input)).map fun yn =>
    ((List.range (yn.1.regs written)).map (fun k =>
      (yn.1.mem (35 + 3 * k), yn.1.mem (35 + 3 * k + 1), yn.1.mem (35 + 3 * k + 2))),
      [yn.1.regs heap, yn.1.mem 7, yn.1.mem 8, yn.1.mem 9, yn.1.mem 10,
        yn.1.mem 34, yn.1.mem 47])

/-- Empty classes consume no descriptor slots; the odd class has a shortened last chunk.
The count table, query words and both outside sentinels survive. -/
example : observe = some
    ([(1, 18, 2), (1, 22, 1), (2, 26, 2), (2, 30, 2)], [47, 0, 3, 4, 0, 99, 77]) := by
  decide

private def classSize (r : ℕ) : ℕ := if r = 1 then 3 else if r = 2 then 4 else 0

/-- The same four actual descriptors follow from the general theorem and an initialized
compiled run, with all count, separation and width premises discharged. -/
example : ∃ y t, t ≤ 287 ∧
    Runs 8 (code.program written) (State.init input) ⟨code.size, y⟩ (t - 1) ∧
    Executes 8 (code.program written) (State.init input) 4 t ∧
    y.mem 35 = 1 ∧ y.mem 39 = 22 ∧ y.mem 40 = 1 ∧ y.mem 45 = 30 ∧
    y.mem 47 = 77 ∧ y.mem 10 = 0 := by
  obtain ⟨b, hb, hregs, hmem⟩ : ∃ b,
      ExecWithin 8 boot (.init input) b 13 ∧
        (b.regs counts = 7 ∧ b.regs queries = 10 ∧ b.regs size = 2 ∧
          b.regs modulus = 3 ∧ b.regs dst = 35 ∧ b.regs capacity = 2) ∧
        b.mem = (Data.init input : Data 32).mem := by
    refine ⟨?b, ?run, ?args, ?memory⟩
    case run => ram_eval [boot, input, Data.init, Fits]
    case args => decide
    case memory => rfl
  obtain ⟨hcount, hq, hn, hp, hd, hcap⟩ := hregs
  obtain ⟨y, hy, hycount, hyheap, -, hcells, hframe⟩ := exec (w := 8) b classSize
    (by
      intro r hr
      rw [hp] at hr
      rw [hcount, hmem]
      interval_cases r <;> decide)
    (by
      intro r hr
      rw [hp] at hr
      rw [hn]
      interval_cases r <;> decide)
    (by rw [hcap]; decide) (by rw [hcount, hp, hd]; decide)
    (by rw [hq, hp, hn, hd]; decide)
    (by rw [hd, hp, hn, hcount, hq]; decide)
  have hwritten : y.regs written = 4 := by
    simpa [hcap, hp, before, classSize, Finset.sum_range_succ,
      Nat.ceilDiv_eq_add_pred_div] using hycount
  have first := hcells 1 (by rw [hp]; decide) 0 (by rw [hcap]; decide)
  have second := hcells 1 (by rw [hp]; decide) 1 (by rw [hcap]; decide)
  have last := hcells 2 (by rw [hp]; decide) 1 (by rw [hcap]; decide)
  obtain ⟨t, ht, he⟩ := hb.seq hy
  have hr := he.runs (pc := 0) (p := code.program written)
    (Program.Contains.self _).append_left
  have ht' : t ≤ 286 := by simpa only [hp, hn] using ht
  refine ⟨y, t + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [code, State.init, Nat.zero_add, Nat.add_sub_cancel] using hr
  · simpa only [code, State.init, hwritten] using he.executes written
  · simpa [hd, hcap, before, classSize, Finset.sum_range_succ,
      Nat.ceilDiv_eq_add_pred_div] using first.1
  · simpa [hd, hq, hn, hcap, before, classSize, Finset.sum_range_succ,
      Nat.ceilDiv_eq_add_pred_div] using second.2.1
  · simpa [hd, hcap, before, classSize, Finset.sum_range_succ,
      Nat.ceilDiv_eq_add_pred_div] using second.2.2
  · simpa [hd, hq, hn, hcap, before, classSize, Finset.sum_range_succ,
      Nat.ceilDiv_eq_add_pred_div] using last.2.1
  · exact (hframe 47 (by rw [hd, hwritten]; decide)).trans (congrFun hmem 47)
  · exact (hframe 10 (by rw [hd, hwritten]; decide)).trans (congrFun hmem 10)

end Catalogue

namespace Params

open Cslib.Algorithms.WordRAM.ExactTriangle.Parameters
open Cslib.Algorithms.ExactTriangle

private def boot : Code .standard 15 := ram[
  one ← #1; arg ← #1; size ← *arg; arg ← arg + one; dimension ← *arg;
  arg ← arg + one; divisor ← *arg ]

private def code : Code .standard 15 := .seq boot program

private def observe (w n D g : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  (code.eval w (n * n + D + 2) (.init [n, D, g])).map fun yn =>
    (yn.1.regs middleRoot, yn.1.regs capacity, yn.1.regs pieceLength, yn.1.regs pieces)

example : observe 10 3 4 1 = some (2, 4, 2, 2) := by decide

example : observe 10 3 4 3 = some (2, 4, 1, 3) := by decide

example : observe 10 0 0 0 = some (0, 0, 0, 0) := by decide

example : observe 2 3 4 1 = none := by decide

private theorem parameters_values :
    sOf 4 = 2 ∧ queryCap 3 4 = 4 ∧ pieceSize 4 1 = 2 ∧ numPieces 3 4 1 = 2 := by
  have h4 : Nat.sqrt 4 = 2 := by
    have hlow : 2 ≤ Nat.sqrt 4 := Nat.le_sqrt.mpr (by decide)
    have hhigh : Nat.sqrt 4 < 3 := Nat.sqrt_lt.mpr (by decide)
    omega
  have h20 : Nat.sqrt 20 = 4 := by
    have hlow : 4 ≤ Nat.sqrt 20 := Nat.le_sqrt.mpr (by decide)
    have hhigh : Nat.sqrt 20 < 5 := Nat.sqrt_lt.mpr (by decide)
    omega
  simp only [sOf, queryCap, pieceSize, numPieces, Nat.ceilDiv_eq_add_pred_div]
  norm_num [h4, h20]

/-- The exported sufficient fits are satisfied, and all four computed parameters come from the
same initialized compiled run; parameter computation preserves every input cell. -/
example : ∃ y t, t ≤ 65 ∧
    Runs 10 (code.program pieces) (State.init [3, 4, 1]) ⟨code.size, y⟩ (t - 1) ∧
    Executes 10 (code.program pieces) (State.init [3, 4, 1]) 2 t ∧
    y.regs middleRoot = 2 ∧ y.regs capacity = 4 ∧ y.regs pieceLength = 2 ∧
    y.regs pieces = 2 ∧ y.mem = (Data.init [3, 4, 1] : Data 15).mem := by
  obtain ⟨b, hb, hregs, hmem⟩ : ∃ b,
      ExecWithin 10 boot (.init [3, 4, 1]) b 7 ∧
        (b.regs size = 3 ∧ b.regs dimension = 4 ∧ b.regs divisor = 1) ∧
        b.mem = (Data.init [3, 4, 1] : Data 15).mem := by
    refine ⟨?b, ?run, ?args, ?memory⟩
    case run => ram_eval [boot, Data.init, Fits]
    case args => decide
    case memory => rfl
  obtain ⟨hn, hD, hg⟩ := hregs
  obtain ⟨hS, hQ, hPiece, hPieces⟩ := parameters_values
  obtain ⟨y, hy, hs, hq, hB, hH, -, -, -, hym⟩ := exec (w := 10) b
    (by rw [hD]; decide) (by rw [hn]; decide)
    (by rw [hD, hg, hS]; decide) (by rw [hn, hD, hg, hPiece]; decide)
  have hyH : y.regs pieces = 2 := by
    simpa only [hn, hD, hg, hPieces] using hH
  obtain ⟨t, ht, he⟩ := hb.seq hy
  have hr := he.runs (pc := 0) (p := code.program pieces)
    (Program.Contains.self _).append_left
  have ht' : t ≤ 64 := by simpa only [hn, hD, hS, hQ] using ht
  refine ⟨y, t + 1, by omega, ?_, ?_, ?_, ?_, ?_, hyH, hym.trans hmem⟩
  · simpa only [code, State.init, Nat.zero_add, Nat.add_sub_cancel] using hr
  · simpa only [code, State.init, hyH] using he.executes pieces
  · simpa only [hD, hS] using hs
  · simpa only [hn, hD, hQ] using hq
  · simpa only [hD, hg, hPiece] using hB

end Params

end ComplexityTests.WordRAMExactTriangleChunks
