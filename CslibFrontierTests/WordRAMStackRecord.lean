/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStack
import CslibFrontier.Computability.WordRAM.Compile
import Mathlib.Tactic.FinCases

/-!
# Native fixed-record stack regressions

A two-word record is pushed above an existing stack tail into dirty reserved memory, then popped
into different registers. The tests exercise the traversal word stack's generic record
certificates, actual instruction counts, order and frame guarantees, the empty-record case, and
the Chan–He controller's unchanged graph.
-/

namespace CslibFrontierTests.WordRAMStackRecord

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal (WordStack.Rep WordStack.pushRecord
  WordStack.popRecord WordStack.pushRecord_exec WordStack.popRecord_exec)

private def registers (i : Fin 9) : Fin 14 := ⟨2 + i.val, by omega⟩
private def source : Fin 2 → Fin 14 := ![0, 1]
private def target : Fin 2 → Fin 14 := ![11, 12]

private def dirty : Data 14 where
  regs := ![4, 7, 0, 0, 1, 8, 0, 0, 0, 0, 0, 99, 98, 13]
  mem a := if a = 8 then 3 else if a = 9 then 99 else if a = 10 then 98
    else if a = 12 then 77 else 0

private theorem dirty_rep : WordStack.Rep 7 8 3 [3] (dirty.comap registers) := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl, by decide, ?_⟩
  · intro i
    fin_cases i <;> decide
  · intro a
    dsimp [dirty, Data.comap]
    split_ifs <;> decide
  · intro i
    fin_cases i
    rfl

/-- Both generic certificates apply to concrete dirty memory and preserve the old stack tail.
The destination bank initially contains different words, and the external memory/register
sentinels are preserved by the certified frames. -/
example : ∃ y z, Exec 7 (WordStack.pushRecord registers source 0) dirty y 19 ∧
    Exec 7 (WordStack.popRecord registers target 0) y z 29 ∧
    WordStack.Rep 7 8 3 [3] (z.comap registers) ∧ z.regs 11 = 4 ∧ z.regs 12 = 7 ∧
    z.regs 13 = 13 ∧ z.mem 12 = 77 := by
  obtain ⟨y, hy, hry, hfy, hpy⟩ := WordStack.pushRecord_exec registers (by decide) source 0
    (by decide) dirty [3] (by decide) (by decide) dirty_rep (by decide) (by decide)
  have hr : WordStack.Rep 7 8 3 (List.ofFn ![4, 7] ++ [3]) (y.comap registers) := hry
  obtain ⟨z, hz, hrz, hout, hfz, hpz⟩ := WordStack.popRecord_exec registers (by decide) target 0
    (by decide) (by decide) y [3] ![4, 7] (by decide) (by decide) hr
  refine ⟨y, z, hy, hz, hrz, hout 0, hout 1, ?_, ?_⟩
  · exact (hpz 13 (by decide) (by decide)).trans (hpy 13 (by decide))
  · exact (hfz 12 (by decide)).trans (hfy 12 (by decide))

private def roundTrip : Code .standard 14 :=
  .seq (WordStack.pushRecord registers source 0) (WordStack.popRecord registers target 0)

-- Native interpretation confirms order, total body cost 48, the charged halt, and live tail size.
example : run 7 (roundTrip.program 11) 49 ⟨0, dirty⟩ = some (4, 49) ∧
    run 7 (roundTrip.program 12) 49 ⟨0, dirty⟩ = some (7, 49) ∧
    run 7 (roundTrip.program 4) 49 ⟨0, dirty⟩ = some (1, 49) ∧
    run 7 (roundTrip.program 11) 48 ⟨0, dirty⟩ = none := by
  decide

-- Popping leaves the written cells dirty, in reverse physical order above the preserved tail.
private def inspectPopped (address : ℕ) : Code .standard 14 :=
  .seq roundTrip (.seq (.op (.const 0 address)) (.op (.load 0 0)))

example : run 7 ((inspectPopped 9).program 0) 51 ⟨0, dirty⟩ = some (7, 51) ∧
    run 7 ((inspectPopped 10).program 0) 51 ⟨0, dirty⟩ = some (4, 51) := by
  decide

-- Empty records execute just their real self-copy; no minimum word width is hidden in it.
example (x : Data 14) :
    Exec 0 (WordStack.pushRecord registers (Fin.elim0 : Fin 0 → Fin 14) 0) x x 1 ∧
    Exec 0 (WordStack.popRecord registers (Fin.elim0 : Fin 0 → Fin 14) 0) x x 1 := by
  have h : Exec (B := .standard) 0 (.op (.copy (0 : Fin 14) 0)) x x 1 := by
    convert (Exec.copy (B := Basis.standard) (w := 0) (x := x) (d := 0) (s := 0)) using 1
    ext i <;> simp [Data.set]
  exact ⟨h, h⟩

namespace TraversalGraph

open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

-- These are the original one-word native blocks, kept here only to pin the instruction graph.
private def push (i : Fin 7) : Code .standard 128 :=
  let tag := Traversal.registers WordStack.tag
  let arg := Traversal.registers WordStack.arg
  let src := slot i
  .seq (ram[ tag ← #0; arg ← src ]) (WordStack.program.rename Traversal.registers)

private def pop (i : Fin 7) : Code .standard 128 :=
  let tag := Traversal.registers WordStack.tag
  let arg := Traversal.registers WordStack.arg
  .seq (ram[ tag ← #1; arg ← #0 ])
    (.seq (WordStack.program.rename Traversal.registers)
      (.op (.copy (slot i) (Traversal.registers WordStack.out))))

example : pushFrame =
    .seq (push 6) (.seq (push 5) (.seq (push 4) (.seq (push 3)
      (.seq (push 2) (.seq (push 1) (.seq (push 0) (.op (.copy (slot 0) (slot 0))))))))) := rfl

example : popFrame =
    .seq (pop 0) (.seq (pop 1) (.seq (pop 2) (.seq (pop 3)
      (.seq (pop 4) (.seq (pop 5) (.seq (pop 6) (.op (.copy (slot 0) (slot 0))))))))) := rfl

end TraversalGraph

end CslibFrontierTests.WordRAMStackRecord
