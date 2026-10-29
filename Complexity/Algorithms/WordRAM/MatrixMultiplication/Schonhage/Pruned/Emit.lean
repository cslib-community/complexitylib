/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Charged timestamp insertion for native child queries

## Main results

* `PrunedQuery.exec_emit`: one native membership test and optional unique suffix insertion,
  within nine instructions, with the complete memory update and register frame.

This kernel does not assume that a child request set was computed elsewhere. The surrounding
native scan supplies each tested suffix and uses the returned timestamp/list updates.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Exactly the registers a timestamp insertion can modify. -/
def EmitLocal (i : Fin registers) : Prop :=
  i = address ∨ i = marker ∨ i = temporary ∨ i = childCount

instance (i : Fin registers) : Decidable (EmitLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = marker ∨ i = temporary ∨ i = childCount))

private theorem emit_preserves (i : Fin registers) : ¬EmitLocal i → emit.Preserves i := by
  decide +kernel +revert

/-- Timestamp insertion performs its real load, comparison, optional stores and increment.
The result states the exact memory update even before a caller supplies array separation. -/
theorem exec_emit {w : ℕ} (x : Data registers) (h1 : x.regs one = 1)
    (hs : Fits w (x.regs stamps + x.regs suffix))
    (hl : Fits w (x.regs childList + x.regs childCount))
    (hn : Fits w (x.regs childCount + 1)) :
    ∃ y, ExecWithin w emit x y 9 ∧
      y.regs childCount =
        (if x.mem (x.regs stamps + x.regs suffix) = x.regs epoch then
          x.regs childCount else x.regs childCount + 1) ∧
      y.mem =
        (if x.mem (x.regs stamps + x.regs suffix) = x.regs epoch then x.mem else
          Function.update
            (Function.update x.mem (x.regs childList + x.regs childCount) (x.regs suffix))
            (x.regs stamps + x.regs suffix) (x.regs epoch)) ∧
      (∀ i, ¬EmitLocal i → y.regs i = x.regs i) := by
  let s := x.regs stamps + x.regs suffix
  let z := (x.set address s).set marker (x.mem s)
  by_cases h : x.mem s = x.regs epoch
  · let y := z.set temporary (z.regs temporary)
    have he : ExecWithin w emit x y 4 := by
      ram_eval [emit, z, y, s, h, hs, address, stamps, suffix, marker, epoch, temporary,
        childCount, childList, one, Fin.mk.injEq]
    refine ⟨y, he.mono (by decide), ?_, ?_, fun i hi => he.regs_eq (emit_preserves i hi)⟩
    · simp only [s] at h
      simp [y, z, h, childCount, address, marker, temporary]
    · simp only [s] at h
      simp [y, z, h]
  · let y :=
      (((((z.set address (x.regs childList + x.regs childCount)).write
        (x.regs childList + x.regs childCount) (x.regs suffix)).set address s).write
        s (x.regs epoch)).set childCount (x.regs childCount + 1))
    have he : ExecWithin w emit x y 9 := by
      ram_eval [emit, z, y, s, h, hs, hl, hn, h1, address, stamps, suffix, marker, epoch,
        temporary, childCount, childList, one, Fin.mk.injEq]
    refine ⟨y, he, ?_, ?_, fun i hi => he.regs_eq (emit_preserves i hi)⟩
    · simp only [s] at h
      simp [y, h]
    · simp only [s] at h
      simp [y, z, h, s, Data.write_mem]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
