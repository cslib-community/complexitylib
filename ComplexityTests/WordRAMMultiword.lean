/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.WordRAM.Multiword.Mul

/-! Maximal digits, odd widths, zero-length operands, and actual instruction counts. -/

namespace WordRAMMultiwordTests

open Cslib.WordRAM Cslib.WordRAM.Multiword Cslib.WordRAM.Multiword.Schoolbook

/-- Observe the output digits and charged instruction count of the actual interpreter. -/
def observed (w m n : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) :
    Option (List ℕ × ℕ) :=
  ((fixedProgram m n).eval w 0 (input m n a b)).map fun (y, t) =>
    ((outputRegs m n).map y.regs, t)

/-- Maximal digits, odd widths, unequal lengths, internal zero digits, zero-length operands,
width exclusions below `2`, and code size of `fixedProgram 18 18`. -/
example :
    observed 2 2 2 ![1, 1] ![1, 1] = some ([1, 0, 0, 1], 41) ∧
    observed 3 3 3 ![1, 1, 1] ![1, 1, 1] = some ([1, 0, 0, 0, 1, 1], 80) ∧
    observed 4 3 2 ![3, 3, 3] ![3, 3] = some ([1, 0, 3, 2, 3], 64) ∧
    observed 2 3 2 ![1, 0, 1] ![1, 1] = some ([1, 1, 1, 1, 0], 64) ∧
    (observed 2 0 3 ![] ![1, 1, 1] = some ([0, 0, 0], 11) ∧
      observed 2 3 0 ![1, 1, 1] ![] = some ([0, 0, 0], 32) ∧
      observed 2 0 0 ![] ![] = some ([], 8)) ∧
    (observed 1 2 2 ![0, 0] ![0, 0] = none ∧
      observed 0 2 2 ![0, 0] ![0, 0] = none) ∧
    (fixedProgram 18 18).size = 2465 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, size_fixedProgram 18 18⟩

/-- The full six-word product contract has a bounded concrete instance at width two. -/
example : ∃ x y : Data 76, x.Bounded 2 ∧ y.Bounded 2 ∧
    Exec 2 (fixedProgram 18 18) x y 2465 ∧
    Multiword.value (radix 2) x (leftRegs 18 18) = 4095 ∧
    Multiword.value (radix 2) x (rightRegs 18 18) = 4095 ∧
    Multiword.Bounded (radix 2) y (outputRegs 18 18) ∧
    Multiword.value (radix 2) y (outputRegs 18 18) = 4095 * 4095 :=
  six_word_product (by decide) (by decide) (by decide)

end WordRAMMultiwordTests
