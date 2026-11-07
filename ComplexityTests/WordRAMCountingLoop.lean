/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Computability.WordRAM.CountingLoop
import Complexity.Computability.WordRAM.Notation
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Padding

/-!
# Counting loops from dirty states and nonzero indices

The generic rule is applied to a real one-instruction body, with exact interpreter clocks.
Padding checks empty/nonempty output, overwritten dirty cells and both adjacent sentinels.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMCountingLoop

open Cslib.WordRAM

private abbrev index : Fin 4 := 0
private abbrev limit : Fin 4 := 1
private abbrev one : Fin 4 := 2
private abbrev sentinel : Fin 4 := 3

private def body : Code .standard 4 := ram[ index ← index + one ]
private def loop : Code .standard 4 := .loop (.lt index limit) body

-- A proof client starting at any bounded index: memory and an unrelated dirty register survive.
example {w N : ℕ} (x : Data 4) (hN : x.regs limit = N) (h1 : x.regs one = 1)
    (hle : x.regs index ≤ N) (hfit : Fits w N) :
    ∃ y, ExecWithin w loop x y ((N - x.regs index) * 3 + 2) ∧
      y.regs index = N ∧ y.mem = x.mem ∧ y.regs sentinel = x.regs sentinel := by
  let P (_ : ℕ) (y : Data 4) := y.regs limit = N ∧ y.regs one = 1 ∧
    y.mem = x.mem ∧ y.regs sentinel = x.regs sentinel
  have step (y : Data 4) (hy : P (y.regs index) y) (hi : y.regs index < N) :
      ∃ z, ExecWithin w body y z 1 ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1 := by
    have he : ExecWithin w body y (y.set index (y.regs index + 1)) 1 := by
      ram_eval [body, hy.2.1, hfit.of_le (by omega : y.regs index + 1 ≤ N)]
    refine ⟨_, he, ⟨?_, ?_, hy.2.2.1, ?_⟩, by simp⟩
    · exact (he.regs_eq (by decide : body.Preserves limit)).trans hy.1
    · exact (he.regs_eq (by decide : body.Preserves one)).trans hy.2.1
    · exact (he.regs_eq (by decide : body.Preserves sentinel)).trans hy.2.2.2
  obtain ⟨y, he, ⟨_, _, hm, hs⟩, hi⟩ := ExecWithin.loop_count P
    (fun _ hy => hy.1) step hle ⟨hN, h1, rfl, rfl⟩
  exact ⟨y, he, hi, hm, hs⟩

private def start (j N : ℕ) : Data 4 :=
  ⟨![j, N, 1, 6], fun a => a + 20⟩

-- The endpoint is the largest three-bit word: N fits, but N+1 does not.
#guard match loop.eval 3 3 (start 5 7) with
  | some (y, t) => y.regs index == 7 && y.regs limit == 7 && y.regs sentinel == 6 &&
      y.mem 12 == 32 && t == 8
  | none => false

#guard match loop.eval 3 0 (start 7 7) with
  | some (y, t) => y.regs index == 7 && y.mem 12 == 32 && t == 2
  | none => false

example : Fits 3 7 ∧ ¬Fits 3 8 := by decide

private def paddingStart (n : ℕ) : Data 10 :=
  ⟨![2, n, 3, 4, 5, 6, 99, 98, 97, 96], fun a => a + 100⟩

open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

-- No stores in the empty case; setup three plus final exit two, from dirty registers/memory.
#guard match Padding.program.eval 5 0 (paddingStart 0) with
  | some (y, t) => y.mem 2 == 102 && y.mem 1 == 101 &&
      y.regs Padding.dst == 2 && y.regs Padding.len == 0 && t == 5
  | none => false

-- Two complete groups overwrite all old cells; input arguments and adjacent cells survive.
#guard match Padding.program.eval 5 2 (paddingStart 2) with
  | some (y, t) => y.mem 1 == 101 && y.mem 2 == 3 && y.mem 3 == 4 && y.mem 4 == 5 &&
      y.mem 5 == 6 && y.mem 6 == 3 && y.mem 7 == 4 && y.mem 8 == 5 && y.mem 9 == 6 &&
      y.mem 10 == 110 && y.regs Padding.dst == 2 && y.regs Padding.len == 2 &&
      y.regs Padding.pad0 == 3 && y.regs Padding.pad3 == 6 && t == 29
  | none => false

-- The empty proof client needs only the existing fits, with no one-past-the-counter premise.
example : ∃ y, ExecWithin 3 Padding.program (paddingStart 0) y 5 ∧
    y.mem 2 = 102 ∧ y.mem 10 = 110 := by
  obtain ⟨y, hy, hm, _⟩ := Padding.exec (w := 3) (paddingStart 0) (by decide) (by decide)
  refine ⟨y, hy, ?_, ?_⟩
  all_goals rw [hm]; decide

-- The migrated public proof retains the exact 12*N+5 allowance and dirty-memory contract.
example : ∃ y, ExecWithin 5 Padding.program (paddingStart 2) y 29 ∧
    y.mem 2 = 3 ∧ y.mem 9 = 6 ∧ y.mem 10 = 110 ∧ y.regs Padding.pad3 = 6 := by
  obtain ⟨y, hy, hm, hr⟩ := Padding.exec (w := 5) (paddingStart 2) (by decide) (by decide)
  refine ⟨y, hy, ?_, ?_, ?_, hr Padding.pad3 (by decide)⟩
  all_goals rw [hm]; decide

end ComplexityTests.WordRAMCountingLoop
