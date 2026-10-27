/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Defs
public import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# Bounded signed integer RAM

`Signed.model` instantiates the generic RAM with the operational choices of
`LeanTrominoes.ComplexityAbstract.RAM` at revision `6d5b36c1`
([MIT–ULB CompGeom Group][Tromino2025]). Values are integers, addresses are naturals, and
the configuration is a word width. Every produced, moved, stored, or returned value must fit
the signed word range. Address registers must be nonnegative and below `2^w`; the current
program counter and every continuation label must also be below `2^w`.

Arithmetic uses Lean's integer division and remainder, including their total zero-divisor
conventions. Each instruction, including halt, costs one. This is the source's signed model,
not the unsigned `Cslib.WordRAM` instance; in particular subtraction is not truncated.

## Main definitions

* `Arithmetic`, `Test`: the original arithmetic and comparison symbols.
* `Fits`, `model`: signed word bounds and the generic RAM instance.
* `initial`, `InputFits`: the original input layout and admissibility predicate.

## Main results

* `fits_zero`, `fits_one`: basic representable values.
* `Fits.natAbs_le`: magnitude bounded by the negative endpoint.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed

/-- The five arithmetic operations of the original signed RAM. -/
inductive Arithmetic
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- Integer arithmetic, with Lean's total division and remainder conventions. -/
def Arithmetic.eval : Arithmetic → ℤ → ℤ → ℤ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y

/-- Equality and signed strict comparison. -/
inductive Test
  | eq | lt
  deriving DecidableEq, Repr

/-- Interpret a comparison on signed integers. -/
def Test.eval : Test → ℤ → ℤ → Bool
  | .eq, x, y => decide (x = y)
  | .lt, x, y => decide (x < y)

/-- Signed two's-complement range, requiring a positive word width. -/
def Fits (w : ℕ) (value : ℤ) : Prop :=
  0 < w ∧ -(2 ^ (w - 1) : ℤ) ≤ value ∧ value < (2 ^ (w - 1) : ℤ)

instance (w : ℕ) (value : ℤ) : Decidable (Fits w value) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A signed word's magnitude is at most the magnitude of its negative endpoint. -/
theorem Fits.natAbs_le {w : ℕ} {z : ℤ} (h : Fits w z) :
    z.natAbs ≤ 2 ^ (w - 1) := by
  rcases h with ⟨_, hlo, hhi⟩
  have hp : ((2 ^ (w - 1) : ℕ) : ℤ) = 2 ^ (w - 1) := by norm_cast
  by_cases hz : 0 ≤ z
  · have := Int.eq_natAbs_of_nonneg hz
    omega
  · have := Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)
    omega

/-- Zero fits at every positive width. -/
theorem fits_zero {w : ℕ} (positive : 0 < w) : Fits w 0 := by
  have power : (0 : ℤ) < 2 ^ (w - 1) := pow_pos (by decide) _
  exact ⟨positive, by omega, power⟩

/-- One fits at every width of at least two bits. -/
theorem fits_one {w : ℕ} (wide : 2 ≤ w) : Fits w 1 := by
  have power : (2 : ℤ) ≤ 2 ^ (w - 1) := by
    simpa using
      (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ w - 1 by omega))
  exact ⟨by omega, by omega, by omega⟩

/-- The original bounded signed integer RAM, as a generic machine model.
All writes and halts check `Fits`; addresses and control labels use the unsigned range. -/
abbrev model : Model where
  Value := ℤ
  Address := ℕ
  Config := ℕ
  Const := ℤ
  operations := ⟨Arithmetic, fun _ => 2⟩
  tests := ⟨Test, fun _ => 2⟩
  constant := fun _ c => some c
  evalOp := fun _ f args => some (f.eval (args 0) (args 1))
  evalTest := fun _ f args => some (f.eval (args 0) (args 1))
  admissible := fun w v => decide (Fits w v)
  address := fun w a => if a < 0 ∨ a ≥ (2 ^ w : ℕ) then none else some a.toNat
  validMove := fun w v => decide (Fits w v)
  validPC := fun w pc => decide (pc < 2 ^ w)

/-- Zero registers and an input length header at address zero, followed by input words.
Input placement is a calling convention, not part of the instruction cost. -/
def initial {r : ℕ} (input : List ℤ) : State model r :=
  ⟨0, .init 0 (fun address =>
    if address = 0 then (input.length : ℤ) else input[address - 1]?.getD 0)⟩

/-- Input words and their length header fit the signed range. -/
def InputFits (w : ℕ) (input : List ℤ) : Prop :=
  Fits w input.length ∧ ∀ value ∈ input, Fits w value

end Cslib.GenericRAM.Signed
