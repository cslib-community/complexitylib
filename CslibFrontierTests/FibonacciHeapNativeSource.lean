/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Source

/-!
# Concrete memory behavior of the Fibonacci heap's iteration sources

These are oracle-program tests, not native execution certificates. Empty and occupied table
slots, both preparation branches, zero iteration and a maximum fitting key retain their actual
queries and writes. A dirty cell outside the layout stays untouched.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeSource

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open FibonacciHeap FibonacciHeap.Native

private def lower {α : Type} (p : FibonacciHeap.Prog α) : Memory.Prog α :=
  Cslib.DataStructure.link ((layout 2 0).methods 5) p

private def empty : Memory.State :=
  ⟨fun a => if a = 31 then 17 else 0, 23⟩

/-- An occupied consolidation slot with a maximum five-bit key and a dirty outside cell. -/
def occupied : Memory.State :=
  ⟨fun a => if a = 0 then 31 else if a = 16 then 1 else if a = 31 then 17 else 0, 23⟩

private def marked : Memory.State :=
  ⟨fun a => if a = 12 ∨ a = 21 then 1 else if a = 31 then 17 else 0, 23⟩

private def unmarkedChild : Memory.State :=
  ⟨fun a => if a = 2 then 2 else if a = 31 then 17 else 0, 23⟩

/-- Zero slots do not read even the first degree, including an out-of-layout starting degree. -/
example : (Memory.spec 5).clientHistory occupied (lower (gather 0 31)) = [] := by decide

/-- An empty slot costs its one read and advances the degree without touching dirty memory. -/
example :
    (Memory.spec 5).clientResult empty (lower (gatherStep 0)) = 1 ∧
    ((Memory.spec 5).clientHistory empty (lower (gatherStep 0))).length = 1 ∧
    ((Memory.spec 5).clientState empty (lower (gatherStep 0))).mem 31 = 17 := by decide

/-- An occupied slot is cleared and becomes the first root. The maximum key is unshifted. -/
example :
    let s := (Memory.spec 5).clientState occupied (lower (gather 1 0))
    s.mem 16 = 0 ∧ s.mem 19 = 1 ∧ s.mem 20 = 1 ∧ s.mem 0 = 31 ∧ s.mem 31 = 17 ∧
      s.frontier = 23 ∧
      ((Memory.spec 5).clientHistory occupied (lower (gather 1 0))).length = 8 := by decide

/-- With zero inner scatter fuel, an unprepared root-list step only reads its next pointer. -/
example :
    (Memory.spec 5).clientResult occupied (lower (scatterList 0 false 1 0 31)) = 31 ∧
    ((Memory.spec 5).clientHistory occupied (lower (scatterList 0 false 1 0 31))).length = 1 := by
  decide

/-- A zero parent ends the source cascade after one read, without changing a mark. -/
example :
    (Memory.spec 5).clientResult empty (lower (cascadeStep 0)) = none ∧
    ((Memory.spec 5).clientHistory empty (lower (cascadeStep 0))).length = 1 := by decide

/-- Marking an unmarked child stops the original cascade instead of reading its parent again. -/
example :
    let s := (Memory.spec 5).clientState unmarkedChild (lower (cascade 2 0))
    s.mem 2 = 2 ∧ s.mem 12 = 1 ∧ s.mem 21 = 1 ∧ s.mem 31 = 17 ∧
      ((Memory.spec 5).clientHistory unmarkedChild (lower (cascade 2 0))).length = 5 := by decide

/-- An empty consolidation slot stops with the original maximum, without shifting that word. -/
example :
    (Memory.spec 5).clientResult empty (lower (scatterStep (0, 31))) = (none, 31) ∧
    ((Memory.spec 5).clientState empty (lower (scatterStep (0, 31)))).mem 16 = 1 ∧
    ((Memory.spec 5).clientHistory empty (lower (scatterStep (0, 31)))).length = 3 := by decide

/-- Source cutoff truncation is preserved even with an occupied slot; no nontruncation premise
is smuggled into the source equations. Native while realization must prove that premise later. -/
example :
    (Memory.spec 5).clientResult occupied (lower (scatter 0 0 31)) = 31 ∧
    (Memory.spec 5).clientHistory occupied (lower (scatter 0 0 31)) = [] := by decide

/-- Preparation clears the mark and decreases its counter before the unchanged inner scatter. -/
example :
    let s := (Memory.spec 5).clientState marked (lower (scatterList 0 true 1 0 31))
    s.mem 12 = 0 ∧ s.mem 21 = 0 ∧ s.mem 31 = 17 ∧ s.frontier = 23 ∧
      (Memory.spec 5).clientResult marked (lower (scatterList 0 true 1 0 31)) = 31 ∧
      ((Memory.spec 5).clientHistory marked (lower (scatterList 0 true 1 0 31))).length = 6 := by
  decide

/-- A live presence tag at zero cutoff is genuinely truncated. The source while equation does
not discharge the native nontruncation condition. -/
example : ¬Cslib.WordRAM.Realization.whileSafe
    (fun (_ : Unit) (a : Option ℕ) => Cslib.WordRAM.Realization.optionWords a 0 ≠ 0)
    (fun a : Unit × Option ℕ =>
      lower (cascadeStep (Cslib.WordRAM.Realization.optionWords a.2 1)))
    (fun _ _ _ => True) 5 () 0 (some 0) empty := by
  simp only [Cslib.WordRAM.Realization.whileSafe]
  decide

/-- One parent query is enough for this zero-parent case: the tag becomes false before the
cutoff and the actual source memory history is admissible. -/
example : Cslib.WordRAM.Realization.whileSafe
    (fun (_ : Unit) (a : Option ℕ) => Cslib.WordRAM.Realization.optionWords a 0 ≠ 0)
    (fun a : Unit × Option ℕ =>
      lower (cascadeStep (Cslib.WordRAM.Realization.optionWords a.2 1)))
    (fun _ _ _ => True) 5 () 1 (some 0) empty ∧
    (Memory.spec 5).ValidHistory empty
      ((Memory.spec 5).clientHistory empty (lower (cascade 1 0))) := by
  simp only [Cslib.WordRAM.Realization.whileSafe]
  decide

/-- Handle zero is still a live optional root. No finite cutoff of zero certifies its exit. -/
example : ¬Cslib.WordRAM.Realization.whileSafe
    (fun (_ : Unit) (a : Option ℕ × ℕ) => Cslib.WordRAM.Realization.optionWords a.1 0 ≠ 0)
    (fun a : Unit × (Option ℕ × ℕ) =>
      lower (scatterStep (Cslib.WordRAM.Realization.optionWords a.2.1 1, a.2.2)))
    (fun _ _ _ => True) 5 () 0 (some 0, 31) occupied := by
  simp only [Cslib.WordRAM.Realization.whileSafe]
  decide

/-- One empty-slot body clears the pending tag and preserves the maximum-word accumulator.
The original three-query history is admissible and does not touch the dirty outside cell. -/
example : Cslib.WordRAM.Realization.whileSafe
    (fun (_ : Unit) (a : Option ℕ × ℕ) => Cslib.WordRAM.Realization.optionWords a.1 0 ≠ 0)
    (fun a : Unit × (Option ℕ × ℕ) =>
      lower (scatterStep (Cslib.WordRAM.Realization.optionWords a.2.1 1, a.2.2)))
    (fun _ _ _ => True) 5 () 1 (some 0, 31) empty ∧
    (Memory.spec 5).ValidHistory empty
      ((Memory.spec 5).clientHistory empty (lower (scatter 1 0 31))) ∧
    ((Memory.spec 5).clientState empty (lower (scatter 1 0 31))).mem 31 = 17 := by
  simp only [Cslib.WordRAM.Realization.whileSafe]
  decide

end ComplexityTests.FibonacciHeapNativeSource
