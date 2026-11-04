/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Catalytic.Comparison
import Complexity.Computability.TreeEval.CookMertz

/-!
# Catalytic equality tests

Concrete runs of the sum-of-squares test and the key test on registers with arbitrary contents,
including a register borrowed from the Cook–Mertz state, and a wraparound counterexample showing
that the modulus bound of `natCast_sqDist_eq_zero_iff` cannot be dropped.
-/

namespace ComplexityTests.CatalyticComparison

open Cslib.Catalytic

/-- Registers with arbitrary contents over `ZMod 8`: three registers of two elements. -/
def regs8 : Fin 3 → Fin 2 → ZMod 8 := ![![3, 7], ![5, 1], ![6, 2]]

/-- Equal vectors: the flag is set, and the registers and the accumulator `4` are restored. -/
example : eqTest (1 : Fin 3) ![1, 0] ![1, 0] (regs8, 4) = (true, (regs8, 4)) := by decide

/-- Different vectors: the flag is clear, and everything is restored. -/
example : eqTest (1 : Fin 3) ![1, 0] ![0, 1] (regs8, 4) = (false, (regs8, 4)) := by decide

/-- The first half of the test adds the squared distance `1² + 1² = 2` to the accumulator and
leaves the borrowed register as it was. -/
example : addSqDist 1 (1 : Fin 3) ![1, 0] ![0, 1] (regs8, 4) = (regs8, 6) := by decide

/-- **Wraparound.** In `ZMod 5`, `(1 - 0)² + (2 - 0)² = 0`, so the test reports the different
vectors `(1, 2)` and `(0, 0)` as equal. Here `ℓ · (b - 1)² = 2 · 2² = 8 ≥ 5`. -/
example : (eqTest (0 : Fin 1) ![(1 : ZMod 5), 2] ![0, 0] (![![4, 3]], 2)).1 = true := by decide

/-- The same vectors are told apart in `ZMod 9`, where `8 < 9`. -/
example : (eqTest (0 : Fin 1) ![(1 : ZMod 9), 2] ![0, 0] (![![4, 3]], 2)).1 = false := by decide

/-- The bound of `natCast_sqDist_eq_zero_iff` holds for these digits below `3` in `ZMod 9`, so the
flag is equality for every content of the registers and the accumulator. -/
example (T : (Fin 1 → Fin 2 → ZMod 9) × ZMod 9) :
    eqTest 0 ((↑) ∘ ![1, 2]) ((↑) ∘ ![0, 0]) T = (false, T) := by
  rw [eqTest_eq_natCast (b := 3) (by decide) (by decide) (by decide)]
  congr 1

/-- Over `ℤ` there is no wraparound. -/
example (T : (Fin 2 → Fin 2 → ℤ) × ℤ) :
    eqTest 0 ![(1 : ℤ), 2] ![0, 0] T = (false, T) := by
  rw [eqTest_eq_int]
  congr 1

/-- Concrete runs over `ℤ`. -/
example : (eqTest (0 : Fin 2) ![(3 : ℤ), -4] ![3, -4] (![![10, -7], ![0, 2]], -5)).1 = true ∧
    (eqTest (0 : Fin 2) ![(3 : ℤ), -4] ![-3, 4] (![![10, -7], ![0, 2]], -5)).1 = false := by
  decide

/-- The accumulator size for `ℓ = 3` digits below `b = 4`: `size 3 + 2 · size 4 = 2 + 2 · 3 = 8`
bits, and indeed `3 · 3² = 27 < 2⁸`. -/
example : Nat.size 3 + 2 * Nat.size 4 = 8 := by decide

/-- With that accumulator, the test of three digits below `4` is exact for any register contents. -/
example (T : (Fin 2 → Fin 3 → ZMod (2 ^ (Nat.size 3 + 2 * Nat.size 4))) ×
    ZMod (2 ^ (Nat.size 3 + 2 * Nat.size 4))) :
    eqTest 0 ((↑) ∘ ![3, 0, 2]) ((↑) ∘ ![3, 0, 2]) T = (true, T) := by
  rw [eqTest_eq_two_pow (b := 4) (by decide) (by decide)]
  congr 1

section CookMertz

open Cslib.TreeEval

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A Cook–Mertz state over `ZMod 7` with arbitrary register contents. -/
def cmState : State (ZMod 7) 2 := ![![1, 6], ![2, 5], ![3, 4]]

/-- The test borrows register `2` of the Cook–Mertz state to compare two embedded two-bit values,
and restores the state. -/
example : eqTest (2 : Fin 3) (embed ![true, false]) (embed ![true, false]) (cmState, 3) =
      (true, (cmState, 3)) ∧
    eqTest (2 : Fin 3) (embed ![true, false]) (embed ![true, true]) (cmState, 3) =
      (false, (cmState, 3)) := by
  decide

end CookMertz

/-- **The key test over `ZMod 2`** on a table with arbitrary bits: equal keys flip the result bit,
different keys leave it, and the table is restored. -/
example : keyTest (1 : ZMod 2) (2 : Fin 4) 2 ![1, 0, 1, 1] 0 = (![1, 0, 1, 1], 1) ∧
    keyTest (1 : ZMod 2) (2 : Fin 4) 3 ![1, 0, 1, 1] 0 = (![1, 0, 1, 1], 0) := by
  decide

/-- The key test over `ℤ` adds the coefficient for equal keys, for any table. -/
example (V : Fin 4 → ℤ) : keyTest 5 (1 : Fin 4) 1 V 2 = (V, 7) := by
  rw [keyTest_eq]
  norm_num

end ComplexityTests.CatalyticComparison
