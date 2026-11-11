/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.TFNP.Subclasses.Sperner
import Mathlib.Tactic.IntervalCases

/-! Sperner's lemma on concrete colourings, a colouring violating the boundary condition, and
concrete instances of circuit `2D-SPERNER`. -/

namespace ComplexityTests.Sperner

open Cslib Cslib.Sperner Cslib.Sperner.GridTriangle Cslib.Complexity Turing.MultiTapeTM

/-! ### Sperner's lemma on a `3 × 3` grid -/

/-- A Sperner colouring of the `3 × 3` grid with seven trichromatic triangles. -/
private def c3 (p : ℕ × ℕ) : Fin 3 :=
  if p = (1, 1) then 0 else if p = (1, 2) ∨ p = (2, 1) then 1 else if p = (2, 2) then 2
  else boundaryColor p

private theorem c3_isSpernerColoring : IsSpernerColoring 3 c3 := by
  intro x y hx hy
  interval_cases x <;> interval_cases y <;> decide

example : 0 < ((triangles 3 3).filter (Trichromatic c3)).card :=
  (c3_isSpernerColoring.odd_card_trichromatic (by decide)).pos

-- The parity count is exact: more than one trichromatic triangle can occur.
example : ((triangles 3 3).filter (Trichromatic c3)).card = 7 := by decide

example : ∃ t, InGrid 3 3 t ∧ Trichromatic c3 t :=
  c3_isSpernerColoring.exists_trichromatic (by decide)

-- Here `start` is itself trichromatic: it is a sink, and the door path from it is trivial.
example : Trichromatic c3 start ∧ next c3 3 3 start = start := by decide

/-- A Sperner colouring of the `2 × 2` grid whose door path from `start` has length two. -/
private def c2 (p : ℕ × ℕ) : Fin 3 := if p = (1, 1) then 1 else boundaryColor p

example : next c2 2 2 start = ⟨true, 0, 0⟩ ∧ next c2 2 2 ⟨true, 0, 0⟩ = ⟨false, 1, 0⟩ ∧
    prev c2 2 2 ⟨false, 1, 0⟩ = ⟨true, 0, 0⟩ ∧ next c2 2 2 ⟨false, 1, 0⟩ = ⟨false, 1, 0⟩ := by
  decide

example : ¬Trichromatic c2 start ∧ Trichromatic c2 ⟨false, 1, 0⟩ := by decide

/-! ### The boundary condition is needed -/

/-- A colouring of the `2 × 2` grid using all three colours, without a trichromatic triangle. -/
private def stripes (p : ℕ × ℕ) : Fin 3 := if p.2 = 0 then 2 else if p.2 = 1 then 1 else 0

example : ¬IsSpernerColoring 2 stripes := fun h => absurd (h 2 1 le_rfl (by decide) (.inr
  (.inr (.inl rfl)))) (by decide)

example : ((triangles 2 2).filter (Trichromatic stripes)).card = 0 := by decide

/-! ### Circuit `2D-SPERNER` -/

/-- The circuit code copying its first input bit, the low bit of `x`. -/
private def firstBit : CircuitCode := ([], [0])

/-- On the `1 × 1` grid every point is a boundary point, and `start` is trichromatic. -/
example : Sperner2D (0, firstBit) [false] := by decide

/-- On the `2 × 2` grid the circuit colours the centre `(1, 1)` with colour `1`, giving the
colouring `c2`: the code `[false, true, false]` of `⟨false, 1, 0⟩` is a solution and `start` is
not. -/
example : Sperner2D (1, firstBit) [false, true, false] := by decide

example : ¬Sperner2D (1, firstBit) [false, false, false] := by decide

-- The successor circuit follows the door path of `c2` on codes.
example : Sperner2D.succ ((1, firstBit), [false, false, false]) = [true, false, false] ∧
    Sperner2D.succ ((1, firstBit), [true, false, false]) = [false, true, false] := by decide

/-- The circuit code with outputs `¬x₀, ¬x₀, x₀` (gate `2` negates input wire `0`). At the centre
`(1, 1)` of the `2 × 2` grid its outputs are `false, false, true`, which is Case `2` of the case
encoding `Δ₁⁺, Δ₁⁻, Δ₂⁺, Δ₂⁻` and decodes to colour `2`. -/
private def caseTwo : CircuitCode := ([(.not, [0])], [2, 2, 0])

example : Sperner2D.color (1, caseTwo) (1, 1) = 2 := by decide

-- The unique trichromatic triangle is then `⟨true, 0, 1⟩`, with code `[true, false, true]`.
example : Sperner2D (1, caseTwo) [true, false, true] := by decide

example : ¬Sperner2D (1, caseTwo) [false, true, false] := by decide

-- Words of the wrong length are not solutions.
example : ¬Sperner2D (1, firstBit) [true, true] := by decide

example : Sperner2D ∈ PPAD encSperner2D := Sperner2D_mem_PPAD

example : searchDomain Sperner2D = Set.univ :=
  isTotalSearch_iff_searchDomain_eq_univ.1 Sperner2D_mem_TFNP.2

example : Sperner2D ∈ PPA encSperner2D :=
  Sperner2D_searchReducible_EndOfLine.mem_PPA Sperner2D_mem_TFNP.1 EndOfLine_mem_PPA

end ComplexityTests.Sperner
