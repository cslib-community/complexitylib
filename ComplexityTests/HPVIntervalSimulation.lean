/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalSimulation

/-! Interval steps of a concrete fair-coin machine, decided by finite simulation: the finite
storage of an embedded window is evaluated, and the semantic interval step follows. -/

namespace ComplexityTests.HPVIntervalSimulation

open Turing MultiTapeMachine MultiTapePTM MultiTapeNTM.ChoiceTable Cslib.Turing

/-- On one work tape, write every coin and move right; the input head moves right too. The first
step emits its coin; then the machine keeps walking without output. -/
private def walk : MultiTapePTM 1 Bool Bool where
  initial := false
  tr state _ _ _ bit := .step
    { inputTape := 1,
      workTapes := fun _ => (some (some bit), 1),
      output := if state then none else some bit, state := some true }
    Empty.elim Empty.elim

/-- The blocks of the start: every head in block `0` at offset `0`. -/
private def J₀ : Option (Fin 1) → ℤ := fun _ => 0

/-- The start record: state `false`, offsets `0`, nothing emitted. -/
private def c₀ : BlockControl 1 Bool 2 := (some false, fun _ => 0, .empty)

/-- After the coins `true, false`: state `true`; the input head at coordinate `1` (clamped at the
right end cell of the one-symbol input), offset `1`; the work head at `2`, offset `0` in block
`1`; and the emitted word `[true]`. -/
private def c₁ : BlockControl 1 Bool 2 :=
  (some true, fun head => match head with | none => 1 | some _ => 0, .accept)

/-- The work tape after the coins `true, false`: the middle block holds them. -/
private def w₁ : Fin 1 → Fin 3 → ZMod 2 → Option Bool := fun _ d r =>
  if d = 1 then some (r = 0) else none

/-- The blocks move: the input head stays in block `0`, the work head moves to block `1`. -/
private def δ₁ : Option (Fin 1) → SignType := fun head => match head with | none => 0 | some _ => 1

-- The finite simulation decides the interval condition by evaluation.
example : walk.LocalIntervalStep 2 [true] J₀ δ₁ c₀ (fun _ _ _ => none) [true, false] c₁ w₁ := by
  decide

-- A different leaving record (output track `other`) fails.
example : ¬ walk.LocalIntervalStep 2 [true] J₀ δ₁ c₀ (fun _ _ _ => none) [true, false]
    (some true, fun head => match head with | none => 1 | some _ => 0, .other) w₁ := by
  decide

-- So the semantic interval step on the integer-indexed tapes holds.
example : walk.IntervalStep 2 [true] J₀ δ₁ c₀ (fun _ _ _ => none) [true, false] c₁ w₁ :=
  (walk.intervalStep_iff_localIntervalStep 2 _ _ _ _ _ _ _ _).mpr (by decide)

end ComplexityTests.HPVIntervalSimulation
