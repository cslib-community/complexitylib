/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.PPSZ.Implied

/-! PPSZ's oracle on the word RAM: on a formula where `x₁ = true` is implied by two clauses but not
by one, the finite search `Cslib.Complexity.PPSZ.impliedTest` and the implied value
`Cslib.Complexity.PPSZ.implied`, concrete runs of `Cslib.Algorithms.WordRAM.PPSZ.impliedCode`
checked against them, the odometer on a small list of lists, and the specification of
`impliedCode` at word size `8`. -/

namespace ComplexityTests.WordRAMPPSZ

open Cslib.WordRAM Cslib.Logic.PL Cslib.Complexity.PPSZ Cslib.Algorithms.WordRAM.PPSZ
open Cslib.Algorithms.WordRAM.PPZ (optCode)

/-- `x₀ ∧ (¬x₀ ∨ x₁)`. -/
def φ : CNF (Fin 2) := [[(0, true)], [(0, false), (1, true)]]

/-- The empty partial assignment. -/
def τ : Fin 2 → Option Bool := fun _ => none

-- Two clauses imply `x₁ = true`; no single clause does, and nothing implies `x₁ = false`.
example : impliedTest φ 2 τ 1 true = true := by decide
example : impliedTest φ 1 τ 1 true = false := by decide
example : impliedTest φ 2 τ 1 false = false := by decide
example : WImplied φ 2 τ 1 true := (wImplied_iff_test _ _ _ _ _).mpr (by decide)
example : ¬WImplied φ 1 τ 1 true := fun h => absurd ((wImplied_iff_test _ _ _ _ _).mp h)
  (by decide)
example : implied φ 2 τ 1 = some true := by rw [implied_eq_test]; decide +kernel
example : implied φ 1 τ 1 = none := by rw [implied_eq_test]; decide +kernel
example : implied φ 1 τ 0 = some true := by rw [implied_eq_test]; decide +kernel

-- The odometer steps through the sections of `[[0, 1], [5, 6]]` in order, first entry fastest.
example : [[0, 1], [5, 6]].sections = [[0, 5], [1, 5], [0, 6], [1, 6]] := by decide
example : nextSection [[0, 1], [5, 6]] [1, 5] = some [0, 6] := by decide
example : nextSection [[0, 1], [5, 6]] [1, 6] = none := by decide

open Cslib.Algorithms.WordRAM.PPZ.Reg in
/-- The clauses of `φ` at addresses `2, …, 6`, the empty partial assignment at `7, 8`, the bound
`s` at `7 + 2 · 2 = 11` with zero scratch memory after it, and the variable `x` in `xReg`. -/
def input (s x : ℕ) : Data 32 where
  regs i := if i = one then 1 else if i = two then 2 else if i = cBeg then 2
    else if i = cEnd then 7 else if i = tBase then 7 else if i = nReg then 2
    else if i = xReg then x else 0
  mem a := if a = 7 ∨ a = 8 then 2 else if a = 11 then s
    else (Cslib.Algorithms.WordRAM.Schoening.encodeClauses φ).getD (a - 2) 0

/-- The register of the result. -/
abbrev resReg : Fin 32 := Cslib.Algorithms.WordRAM.PPZ.Reg.res

-- The program stores `optCode (implied φ s τ x)`: `1` for `x₁` with `s = 2`, `2` (none) with
-- `s = 1`, and `1` for `x₀` with `s = 1`; it leaves the scratch memory zero.
example : ((impliedCode.eval 16 20 (input 2 1)).map fun z => z.1.regs resReg) =
    some (optCode (implied φ 2 τ 1)) := by
  rw [implied_eq_test]; decide +kernel

example : ((impliedCode.eval 16 20 (input 1 1)).map fun z => z.1.regs resReg) =
    some (optCode (implied φ 1 τ 1)) := by
  rw [implied_eq_test]; decide +kernel

example : ((impliedCode.eval 16 20 (input 1 0)).map fun z => z.1.regs resReg) =
    some (optCode (implied φ 1 τ 0)) := by
  rw [implied_eq_test]; decide +kernel

example : ((impliedCode.eval 16 20 (input 2 1)).map fun z =>
    (List.range 4).map fun i => z.1.mem (12 + i)) = some [0, 0, 0, 0] := by
  decide +kernel

-- The specification applies at word size `8`.
example := impliedCode_spec (w := 8) φ τ 1 2 (C := 2) (Tb := 7) (input 2 1) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> rfl) (by decide) (by decide)
  (by decide) (by decide)

end ComplexityTests.WordRAMPPSZ
