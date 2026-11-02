/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Bind
import Complexity.Computability.WordRAM.Realization.Primitive

/-! A uniform continuation reads the address returned by allocation, not a statically fixed cell. -/

namespace ComplexityTests.WordRAMRealizationBind

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private def word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private def environment : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  (word.prodMap word).trans (Fin.appendEquiv 1 1).toEmbedding

private def allocatedRead (count : ℕ) : Memory.Prog ℕ :=
  (Memory.alloc count).bind Memory.read

-- The two source emitters are uniform over all initial counts and all returned addresses.
-- Only their existing primitive certificates are supplied: no intermediate assertion or
-- manually chosen register layout is needed by the bind client.
example : Realizes .exact allocatedRead word word
    (fun _ _ _ => True) (fun _ _ => 1) := by
  have hp : Realizes .exact (fun count => Memory.alloc count) word word
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.alloc word 0
  have hq : Realizes .exact (fun da : ℕ × ℕ => Memory.read da.2) environment word
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read environment 1
  have h := Realizes.bind hp hq
  exact h.consequence (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ => le_rfl)

private def initial : Memory.State := ⟨fun _ => 7, 3⟩

-- This is a nonempty admissible instance; the allocated base is 3 while the input count is 2.
example : Memory.WellFormed 4 initial := by
  constructor
  · decide
  · intro address
    change Fits 4 7
    decide

example : (Memory.spec 4).ValidHistory initial
    ((Memory.spec 4).clientHistory initial (allocatedRead 2)) := by decide

example : (Memory.spec 4).clientResult initial (allocatedRead 2) = 0 := by decide

example : ((Memory.spec 4).clientState initial (allocatedRead 2)).frontier = 5 := by decide

-- The abstraction retains cells outside the allocated block, including inaccessible cells.
example : ((Memory.spec 4).clientState initial (allocatedRead 2)).mem 10 = 7 := by decide

-- Empty allocation cannot justify reading its returned frontier: the existing memory domain
-- remains a genuine obligation of the composed realization.
example : ¬(Memory.spec 4).ValidHistory initial
    ((Memory.spec 4).clientHistory initial (allocatedRead 0)) := by decide

end ComplexityTests.WordRAMRealizationBind
