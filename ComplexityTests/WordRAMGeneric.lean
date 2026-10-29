/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Generic

/-!
# Exact word-RAM specialization

The adapter retains overflow faults and the original policy on arbitrary states: moves, halts
and control labels are not checked against the word width. These tests exercise those choices,
in addition to a nonempty-input computation and the general exact-count equivalence.
-/

namespace ComplexityTests.WordRAMGeneric

open Cslib WordRAM

private def double : Program .standard 2 :=
  [.op (.const 1 1), .op (.load 0 1), .op (.bin .add 0 0 0), .halt 0]

private def oversized : State 2 := ⟨0, ⟨fun _ => 9, fun _ => 0⟩⟩

/-- The generic adapter preserves nonempty-input execution, overflow faults, unchecked moves/halts
on arbitrary initial data, and unbounded natural control labels. -/
example :
    GenericRAM.run (M := Basis.standard.genericModel) 4 double.toGeneric 4
      ((State.init [3]).toGeneric .standard) = some (6, 4) ∧
    GenericRAM.step (M := Basis.standard.genericModel) 3
      (Program.toGeneric (B := .standard) [.op (.const (0 : Fin 1) 8), .halt 0])
      ((State.init []).toGeneric .standard) = .fault ∧
    GenericRAM.run (M := Basis.standard.genericModel) 0
      (Program.toGeneric (B := .standard) [.op (.copy 0 1), .halt 0]) 2
      (oversized.toGeneric .standard) = some (9, 2) ∧
    GenericRAM.step (M := Basis.standard.genericModel) 0
      (Program.toGeneric (B := .standard) [.jump 100]) (oversized.toGeneric .standard) =
      .next ((⟨100, oversized.data⟩ : State 2).toGeneric .standard) :=
  ⟨by rw [run_toGeneric]; decide,
   by rw [step_toGeneric]; rfl,
   by rw [run_toGeneric]; rfl,
   by rw [step_toGeneric]; rfl⟩

/-- info: 'Cslib.WordRAM.step_toGeneric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.step_toGeneric

/-- info: 'Cslib.WordRAM.executes_toGeneric_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.executes_toGeneric_iff

/-- info: 'Cslib.GenericRAM.Executes.unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.GenericRAM.Executes.unique

end ComplexityTests.WordRAMGeneric
