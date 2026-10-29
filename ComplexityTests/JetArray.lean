/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.JetArray

/-!
# Regression tests for rectangular integer tables and truncated bivariate jet arrays

Concrete kernel-checked evaluations and theorem instantiations for
`Complexity.Computability.PolyTime.Int.Table` and `Complexity.Computability.PolyTime.JetArray`:
- rectangular `rowEntry` lookup, `tabulateTable`, `IsTableShape`, and extensionality;
- 2D truncation at both `z^J` and `V^ℓ` on rectangular (`J ≠ ℓ`) signed arrays;
- boundary dimensions `J = 0`, `ℓ = 0`, and ragged-input normalization;
- commutativity, associativity, distributivity, and shift nilpotency;
- nonvacuous instantiations of `jetL1Norm` and binary bit-length bounds;
- plain `ComputableInPolyTime` composition via `fun_prop`.
-/

namespace ComplexityTests.JetArray

open Cslib
open Turing MultiTapeTM

/-! ### Shared rectangular table lookup and tabulation (`PolyTime.Int.Table`) -/

example :
    (let T := tabulateTable 2 3 fun i j => (10 * i + j : ℤ) - 5
    T = [[-5, -4, -3], [5, 6, 7]] ∧
      rowEntry T 1 2 = 7 ∧
      rowEntry T 2 0 = 0 ∧
      rowEntry T 0 3 = 0) ∧
    tabulateTable 2 3 (rowEntry [[1, 2, -1], [3, 0, 4]]) = [[1, 2, -1], [3, 0, 4]] :=
  ⟨by decide +kernel, tabulateTable_rowEntry ⟨rfl, by decide +kernel⟩⟩

/-! ### Concrete 2D truncation, rectangular arithmetic, boundary dimensions, and algebraic laws -/

-- (1 + 2V - V^2 + (3 + 4V^2)z) * (2 - 3V + V^2 + (-1 + 5V + 2V^2)z) mod (z^2, V^3)
-- drops z^2 and V^3, V^4 terms, leaving (2 + V - 7V^2) + (5 - 6V + 24V^2)z.
example :
    convJet 2 3 [[1, 2, -1], [3, 0, 4]] [[2, -3, 1], [-1, 5, 2]] =
      [[2, 1, -7], [5, -6, 24]] ∧
    addJet 3 2 [[1, -2], [3, 4], [-5, 6]] [[2, 2], [-1, 0], [5, -3]] =
      [[3, 0], [2, 4], [0, 3]] ∧
    subJet 3 2 [[1, -2], [3, 4], [-5, 6]] [[2, 2], [-1, 0], [5, -3]] =
      [[-1, -4], [4, 4], [-10, 9]] ∧
    smulJet 3 2 (-3) [[1, -2], [0, 4], [-5, 6]] =
      [[-3, 6], [0, -12], [15, -18]] ∧
    shiftZJet 3 2 [[1, 2], [3, 4], [5, 6]] = [[0, 0], [1, 2], [3, 4]] ∧
    shiftZJet 3 2 (shiftZJet 3 2 (shiftZJet 3 2 [[1, 2], [3, 4], [5, 6]])) =
      zeroJet 3 2 ∧
    shiftVJet 2 3 [[1, 2, 3], [4, 5, 6]] = [[0, 1, 2], [0, 4, 5]] ∧
    shiftVJet 2 3 (shiftVJet 2 3 (shiftVJet 2 3 [[1, 2, 3], [4, 5, 6]])) =
      zeroJet 2 3 ∧
    zeroJet 0 3 = [] ∧
    convJet 0 3 [[1, 2, 3]] [[4, 5, 6]] = [] ∧
    zeroJet 3 0 = [[], [], []] ∧
    convJet 3 0 [[1], [2], [3]] [[4], [5], [6]] = [[], [], []] ∧
    constJet 0 0 42 = [] ∧
    constJet 2 0 42 = [[], []] ∧
    addJet 2 2 [[1, 99, 100], [], [7, 8]] [[10], [20, 30, 40]] =
      [[11, 99], [20, 30]] := by
  decide +kernel

example :
    (let A := [[1, -2], [3, 4], [-5, 1]]
    let B := [[2, 1], [-1, 3], [0, -2]]
    let C := [[-3, 2], [1, 0], [4, -1]]
    convJet 3 2 (convJet 3 2 A B) C = convJet 3 2 A (convJet 3 2 B C) ∧
      convJet 3 2 A (addJet 3 2 B C) = addJet 3 2 (convJet 3 2 A B) (convJet 3 2 A C) ∧
      convJet 3 2 (constJet 3 2 1) A = A) ∧
    convJet 2 3 (constJet 2 3 1) [[1, 2, -1], [3, 0, 4]] = [[1, 2, -1], [3, 0, 4]] :=
  ⟨by decide +kernel, constJet_one_convJet ⟨rfl, by decide +kernel⟩⟩

/-! ### Coefficient-norm and bit-length bounds -/

-- Strict norm decrease under cancellation/truncation, tightness when no terms truncate,
-- and nonvacuous instantiation of `size_natAbs_rowEntry_convJet_le` and
-- `length_encIntBin_mem_convJet_le` on 2 × 3 inputs with magnitudes ≤ 5 (`size ≤ 3`).
example :
    (jetL1Norm [[1, 2, -1], [3, 0, 4]] = 11 ∧
      jetL1Norm [[2, -3, 1], [-1, 5, 2]] = 14 ∧
      jetL1Norm (convJet 2 3 [[1, 2, -1], [3, 0, 4]] [[2, -3, 1], [-1, 5, 2]]) = 45 ∧
      jetL1Norm (convJet 2 3 [[1, 2, 0], [3, 0, 0]] [[0, 1, 0], [0, 0, 0]]) =
        jetL1Norm [[1, 2, 0], [3, 0, 0]] * jetL1Norm [[0, 1, 0], [0, 0, 0]]) ∧
    (∀ j u : ℕ,
      (rowEntry (convJet 2 3 [[1, 2, -1], [3, 0, 4]] [[2, -3, 1], [-1, 5, 2]]) j u).natAbs.size ≤
        3 + 3 + (2 * 3).size) ∧
    ∀ {row : List ℤ},
      row ∈ convJet 2 3 [[1, 2, -1], [3, 0, 4]] [[2, -3, 1], [-1, 5, 2]] →
      ∀ {z : ℤ}, z ∈ row → (encIntBin z).length ≤ 3 + 3 + (2 * 3).size + 1 :=
  ⟨by decide +kernel,
    fun j u => size_natAbs_rowEntry_convJet_le (bA := 3) (bB := 3)
      (by decide +kernel) (by decide +kernel) j u,
    fun hrow _ hz => length_encIntBin_mem_convJet_le (bA := 3) (bB := 3)
      (by decide +kernel) (by decide +kernel) hrow hz⟩

/-- info: ([[2, 1, -7], [5, -6, 24]], 45, [[3, 2, 4], [4, 4, 6]]) -/
#guard_msgs in
#eval
  let P := convJet 2 3 [[1, 2, -1], [3, 0, 4]] [[2, -3, 1], [-1, 5, 2]]
  (P, jetL1Norm P, P.map fun row => row.map fun z => (encIntBin z).length)

/-! ### Plain `ComputableInPolyTime` composition -/

-- Composite expression over unary `(J, ℓ)` and two jet arrays certified directly by `fun_prop`
-- with plain `ComputableInPolyTime` (no `Tidy` types).
example :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × JetRows =>
        tabulateTable p.1.1 p.1.2 fun i j => rowEntry p.2 j i)
      (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
      (encList (encList encIntBin)) ∧
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × JetRows) × JetRows =>
        let J := p.1.1.1
        let ℓ := p.1.1.2
        let A := p.1.2
        let B := p.2
        convJet J ℓ (addJet J ℓ A (shiftZJet J ℓ B))
          (subJet J ℓ (shiftVJet J ℓ A) (constJet J ℓ 3)))
      (encPair (encPair (encPair encUnary encUnary) (encList (encList encIntBin)))
        (encList (encList encIntBin)))
      (encList (encList encIntBin)) :=
  ⟨by fun_prop, by fun_prop⟩

end ComplexityTests.JetArray
