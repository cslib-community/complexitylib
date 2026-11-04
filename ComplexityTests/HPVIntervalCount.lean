/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.PolyTime

/-! Interval counts of a concrete fair-coin machine on plain data: the count is evaluated, the
interval tensor follows, and the polynomial-time certificate applies with a satisfiable budget. -/

namespace ComplexityTests.HPVIntervalCount

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

/-- The blocks of the start: every head in block `0`. -/
private def J₀ : Option (Fin 1) → ℤ := fun _ => 0

/-- The input head stays in block `0`, the work head moves to block `1`. -/
private def δ₁ : Option (Fin 1) → SignType := fun head => match head with | none => 0 | some _ => 1

/-- The start record: state `false`, offsets `0`, nothing emitted. -/
private def c₀ : BlockControl 1 Bool 2 := (some false, fun _ => 0, .empty)

/-- After the coins `true, false`: state `true`, the input head at offset `1`, the work head at
offset `0` of block `1`, and output track `accept`. -/
private def c₁ : BlockControl 1 Bool 2 :=
  (some true, fun head => match head with | none => 1 | some _ => 0, .accept)

/-- The work tape after the coins `true, false`: the middle block holds them. -/
private def w₁ : Fin 1 → Fin 3 → ZMod 2 → Option Bool := fun _ d r =>
  if d = 1 then some (r = 0) else none

-- The plain data of the records and windows.
example : controlData c₁ = (some true, fun head => match head with | none => 1 | some _ => 0,
    .accept) := by
  refine Prod.ext rfl (Prod.ext (funext fun head => ?_) rfl)
  cases head <;> rfl

example : windowCells 2 (w₁ 0) = [none, none, some true, some false, none, none] := by decide

-- Of the four coin strings of two bits, only `true, false` leaves the record `c₁` and the window
-- `w₁`, evaluated on plain data.
example : walk.localIntervalCount 2 [true] J₀ δ₁ (controlData c₀)
    (fun _ => windowCells 2 fun _ _ => none) (controlData c₁) (fun h => windowCells 2 (w₁ h)) =
      1 := by
  decide

-- With output track `other` instead, no coin string qualifies.
example : walk.localIntervalCount 2 [true] J₀ δ₁ (controlData c₀)
    (fun _ => windowCells 2 fun _ _ => none)
    (some true, fun head => match head with | none => 1 | some _ => 0, .other)
    (fun h => windowCells 2 (w₁ h)) = 0 := by
  decide

-- So the interval tensor is `1`.
example : walk.intervalCount 2 [true] J₀ δ₁ c₀ (fun _ _ _ => none) c₁ w₁ = 1 := by
  rw [← localIntervalCount_eq_intervalCount]
  decide

-- The certificate applies: with a fixed block length the budget `2 ^ b (2 b + 1) ≤ 20` holds, so
-- the count of the arguments with a computed input is polynomial-time.
example : MultiTapeTM.ComputableInPolyTime (fun x : List Bool =>
    (⟨x, 2, J₀, δ₁, controlData c₀, fun _ => windowCells 2 fun _ _ => none, controlData c₁,
      fun h => windowCells 2 (w₁ h)⟩ : IntervalData 1 Bool).count walk)
    MultiTapeTM.encBits MultiTapeTM.encUnary :=
  computableInPolyTime_localIntervalCount walk
    (IntervalData.computableInPolyTime_mk MultiTapeTM.ComputableInPolyTime.id'
      (.const _) (.const _) (.const _) (.const _) (.const _) (.const _) (.const _))
    (size := fun _ => 20) (Cslib.PolynomiallyBounded.const 20) fun _ => by norm_num

end ComplexityTests.HPVIntervalCount
