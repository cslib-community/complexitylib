/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.Classes
import Complexity.Computability.WordRAM.Compile

/-! # Initialized native residue-class clients

These clients execute the actual header loader and class scanner. Empty classes, duplicate
residues, row-major ordering, unused output capacity and an outside sentinel are observable.
-/

namespace ComplexityTests.WordRAMExactTriangleQueries

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle.Classes

private def boot : Code .standard 20 := ram[
  one ← #1; addr ← #1; src ← *addr; addr ← addr + one; size ← *addr;
  addr ← addr + one; counts ← *addr; addr ← addr + one; queries ← *addr;
  addr ← addr + one; modulus ← *addr ]

private def input (n p : ℕ) (R : List ℕ) : List ℕ :=
  [6, n, 6 + R.length, 6 + R.length + p, p] ++ R ++ List.replicate p 77 ++
    List.replicate (2 * (n * n) * p) 88 ++ [99]

private def code : Code .standard 20 := .seq boot program

private def observe (w n p : ℕ) (R : List ℕ) :
    Option (List (ℕ × List (ℕ × ℕ)) × ℕ × ℕ) :=
  (code.eval w (p + 1) (.init (input n p R))).map fun yn =>
    ((List.range p).map (fun j =>
      (yn.1.mem (6 + R.length + j),
        (List.range (yn.1.mem (6 + R.length + j))).map fun k =>
          (yn.1.mem (6 + R.length + p + 2 * (n * n) * j + 2 * k),
            yn.1.mem (6 + R.length + p + 2 * (n * n) * j + 2 * k + 1)))),
      yn.1.mem (6 + R.length + p + 2 * (n * n) * p), yn.1.mem 6)

example : observe 8 2 4 [0, 1, 2, 0] =
    some ([(2, [(0, 0), (1, 1)]), (1, [(0, 1)]), (1, [(1, 0)]), (0, [])], 99, 0) := by
  decide

example : observe 8 0 3 [] = some ([(0, []), (0, []), (0, [])], 99, 0) := by decide

example : observe 8 2 0 [0, 1, 2, 0] = some ([], 99, 0) := by decide

example : observe 4 2 4 [0, 1, 2, 0] = none := by decide

private def raw : List ℕ := input 2 4 [0, 1, 2, 0]
private def residues (q : ℕ) : ℕ := [0, 1, 2, 0].getD q 0

/-- Every theorem premise is discharged for the same initialized native run. Both matching
positions in class zero are connected to its computed count, and adjacent capacity stays intact. -/
example : ∃ y t, t ≤ 298 ∧
    Runs 8 (code.program counts) (State.init raw) ⟨code.size, y⟩ (t - 1) ∧
    Executes 8 (code.program counts) (State.init raw) 10 t ∧
    y.mem 10 = 2 ∧ y.mem 13 = 0 ∧
    y.mem 14 = 0 ∧ y.mem 15 = 0 ∧ y.mem 16 = 1 ∧ y.mem 17 = 1 ∧
    y.mem 46 = 99 ∧ y.mem 6 = 0 ∧ y.Bounded 8 := by
  obtain ⟨b, hb, hregs, hmem⟩ : ∃ b,
      ExecWithin 8 boot (.init raw) b 11 ∧
        (b.regs src = 6 ∧ b.regs size = 2 ∧ b.regs counts = 10 ∧
          b.regs queries = 14 ∧ b.regs modulus = 4) ∧
        b.mem = (Data.init raw : Data 20).mem := by
    refine ⟨?b, ?run, ?args, ?memory⟩
    case run => ram_eval [boot, raw, input, Data.init, Fits]
    case args => decide
    case memory => rfl
  obtain ⟨hs, hn, hc, hq, hp⟩ := hregs
  obtain ⟨y, hy, -, hcounts, hpairs, hframe⟩ := exec (w := 8) b residues (by decide)
    (by
      intro q hq'
      rw [hs, hmem]
      rw [hn] at hq'
      have heq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
      rcases heq with rfl | rfl | rfl | rfl <;> decide)
    (by rw [hs, hn, hc]) (by rw [hc, hp, hq])
    (by rw [hc, hp]; decide) (by rw [hq, hn, hp]; decide) (by rw [hn]; decide)
  have hcregs : y.regs counts = 10 := by
    have hpres : program.Preserves counts := by decide
    exact (hy.regs_eq hpres).trans hc
  obtain ⟨t, ht, he⟩ := hb.seq hy
  have hr := he.runs (pc := 0) (p := code.program counts)
    (Program.Contains.self _).append_left
  have ht' : t ≤ 297 := by simpa only [hn, hp] using ht
  have hz := hpairs 0 (by rw [hp]; decide)
  have hz0 := hz 0 (by rw [hn]; decide) (by decide)
  have hz3 := hz 3 (by rw [hn]; decide) (by decide)
  have hcount0 : Nat.count (fun q => residues q = 0) 4 = 2 := by decide
  have hcount3 : Nat.count (fun q => residues q = 3) 4 = 0 := by decide
  have hrank3 : Nat.count (fun q => residues q = 0) 3 = 1 := by decide
  refine ⟨y, t + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [code, State.init, Nat.zero_add, Nat.add_sub_cancel] using hr
  · simpa only [code, State.init, hcregs] using he.executes counts
  · simpa [hc, hn, hcount0] using hcounts 0 (by rw [hp]; decide)
  · simpa [hc, hn, hcount3] using hcounts 3 (by rw [hp]; decide)
  · simpa [hq, hn] using hz0.1
  · simpa [hq, hn] using hz0.2
  · simpa [hq, hn, hrank3] using hz3.1
  · simpa [hq, hn, hrank3] using hz3.2
  · exact (hframe 46 (by rw [hc, hp]; decide) (by rw [hq, hp, hn]; decide)).trans
      (congrFun hmem 46)
  · exact (hframe 6 (by rw [hc, hp]; decide) (by rw [hq, hp, hn]; decide)).trans
      (congrFun hmem 6)
  · exact hr.bounded_init (by decide : InputFits 8 raw)

end ComplexityTests.WordRAMExactTriangleQueries
