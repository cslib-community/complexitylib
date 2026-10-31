/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.PPZ.Forced
import Complexity.Algorithms.WordRAM.PPZ.Round
import Complexity.Computability.Complexity.FineGrained.PPZ.LazyOrder

/-! PPZ on the word RAM: concrete runs of the forced-value scan and of the satisfaction check on a
small 3-CNF, checked against `Cslib.Complexity.PPZ.forced` and `CNF.eval`, the lazy form of a round
on no variables, and the round program's specification at word size `8`. -/

namespace ComplexityTests.WordRAMPPZ

open Cslib.WordRAM Cslib.Logic.PL Cslib.Complexity.PPZ Cslib.Algorithms.WordRAM.PPZ

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁ ∨ x₂)`. -/
def φ : CNF (Fin 3) := [[(0, true), (1, true)], [(0, false), (1, true), (2, true)]]

/-- The partial assignment `x₀ = false`, with `x₁` and `x₂` unset. -/
def τ : Fin 3 → Option Bool := ![some false, none, none]

-- Under `τ`, the first clause is a unit clause on `x₁`; the second is satisfied by `¬x₀`.
example : forced φ τ 1 = some true := by decide
example : forced φ τ 2 = none := by decide

/-- The clauses of `φ` at addresses `2, …, 8`, the partial assignment `τ` at `9, 10, 11`, and the
variable `x` in `xReg`. -/
def forcedInput (x : ℕ) : Data 32 where
  regs i := if i = Reg.one then 1 else if i = Reg.two then 2 else if i = Reg.cBeg then 2
    else if i = Reg.cEnd then 9 else if i = Reg.tBase then 9 else if i = Reg.xReg then x else 0
  mem a := if a = 9 then 0 else if a = 10 ∨ a = 11 then 2
    else (Cslib.Algorithms.WordRAM.Schoening.encode φ).getD (a - 1) 0

-- The scan stores `optCode (forced φ τ x)`: `1` (forced true) for `x₁`, `2` (unforced) for `x₂`.
example : ((forcedCode.eval 16 8 (forcedInput 1)).map fun z => z.1.regs Reg.res) =
    some (optCode (forced φ τ 1)) := by
  decide

example : ((forcedCode.eval 16 8 (forcedInput 2)).map fun z => z.1.regs Reg.res) =
    some (optCode (forced φ τ 2)) := by
  decide

-- A round on no variables changes nothing.
example (O : (Fin 3 → Option Bool) → Fin 3 → Option Bool) (g : Fin 0 → Fin 3) :
    roundOn O g τ = PMF.pure τ :=
  roundOn_zero O g τ

/-- The clauses of `φ` at addresses `2, …, 8`, the frame of a round with `τ` at `9, 10, 11`, and
the total assignment `σ` stored there. -/
def checkInput (σ : Fin 3 → Bool) : Data 32 where
  regs i := if i = Reg.one then 1 else if i = Reg.two then 2 else if i = Reg.cBeg then 2
    else if i = Reg.cEnd then 9 else if i = Reg.tBase then 9 else if i = Reg.nReg then 3
    else if i = Reg.pBase then 12 else 0
  mem a := if 9 ≤ a ∧ a < 12 then (σ ⟨(a - 9) % 3, Nat.mod_lt _ (by omega)⟩).toNat
    else (Cslib.Algorithms.WordRAM.Schoening.encode φ).getD (a - 1) 0

-- `x₀ = false, x₁ = true, x₂ = false` satisfies `φ`; `x₀ = true, x₁ = x₂ = false` falsifies its
-- second clause. The check outputs whether the stored assignment satisfies `φ`.
example : φ.eval ![false, true, false] = true := by decide
example : φ.eval ![true, false, false] = false := by decide

example : ((roundCheck.eval 16 8 (checkInput ![false, true, false])).map
    fun z => z.1.regs Reg.out) = some 1 := by
  decide

example : ((roundCheck.eval 16 8 (checkInput ![true, false, false])).map
    fun z => z.1.regs Reg.out) = some 0 := by
  decide

-- A stored partial assignment reads back.
example : partialAssignmentAt (fun a => if a = 9 then 0 else if a = 10 then 2 else 1) 9 3 =
    ![some false, none, some true] := by
  decide

-- The round program's specification applies at word size `8` to `φ`, whose input has length `8`.
example := roundProgram_spec φ (w := 8) (by decide)

end ComplexityTests.WordRAMPPZ
