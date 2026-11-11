/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.EXP.Separation
import Complexity.Computability.Complexity.Classes.Immune.Complete

/-! Bounded halting with a binary time bound: a concrete accepted instance, the rejection of every
instance with step bound zero, the problem and its complement being nonempty, a reduction of the
diagonal problem, an infinite `P` problem strictly inside bounded halting, and Book's separations
of `E`. -/

namespace ComplexityTests.BoundedHalting

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.BitString

/-- Halt at once, emitting the symbol `1` (`eBit true`), whatever the input head reads. -/
def acceptAct : Act := ⟨0, [], some 1, none⟩

/-- A machine with no work tapes that accepts every input in one step. -/
def acceptDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, acceptAct), (⟨0, some 0, []⟩, acceptAct), (⟨0, some 1, []⟩, acceptAct)]⟩

/-- With one step, the accepting machine accepts the input `[true]`. -/
example : BoundedHalting.mk acceptDesc [true] [true] ∈ BoundedHalting := by
  rw [BoundedHalting.mk_mem_iff]
  decide

/-- The accepting machine also accepts the empty input with the step bound `2`, written `10`. -/
example : BoundedHalting.mk acceptDesc [] [true, false] ∈ BoundedHalting := by
  rw [BoundedHalting.mk_mem_iff]
  decide

/-- With the step bound zero, no machine accepts: it has not halted. -/
example (d : Desc) (x : List Bool) : BoundedHalting.mk d x [] ∉ BoundedHalting := by
  rw [BoundedHalting.mk_mem_iff]
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd h)

/-- Bounded halting and its complement are nonempty, since `∅` and the universe are in `P`. -/
example : BoundedHalting.Nonempty ∧ BoundedHaltingᶜ.Nonempty := by
  constructor
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact BoundedHalting.notMem_P (h ▸ ⟨fun _ => false, by fun_prop, fun _ => by simp⟩)
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact BoundedHalting.notMem_P (h ▸ ⟨fun _ => true, by fun_prop, fun _ => by simp⟩)

/-- The diagonal problem of the time hierarchy, which is not in `P`, reduces to bounded halting. -/
example : PolyTimeReducible encBits encBits {x | diagonal x = true} BoundedHalting :=
  BoundedHalting.polyTimeHard_EXP encBits _ setOf_diagonal_mem_EXP

/-- Bounded halting strictly contains an infinite problem in `P`. -/
example : ∃ B ∈ P encBits, B.Infinite ∧ B ⊂ BoundedHalting :=
  let ⟨⟨B, hB, hinf, hsub⟩, _⟩ := BoundedHalting.exists_infinite_subset_mem_P
  ⟨B, hB, hinf, hsub.ssubset_of_ne fun h => BoundedHalting.notMem_P (h ▸ hB)⟩

/-- `E` is strictly between `P` and `EXP`, and is neither `NP` nor `PSPACE`. -/
example : P encBits ⊂ E encBits ∧ E encBits ⊂ EXP encBits ∧ E encBits ≠ NP encBits ∧
    E encBits ≠ PSPACE encBits :=
  ⟨P_ssubset_E, E_ssubset_EXP, E_ne_NP, E_ne_PSPACE⟩

end ComplexityTests.BoundedHalting
