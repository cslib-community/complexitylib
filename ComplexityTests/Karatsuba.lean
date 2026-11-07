/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Query.Arith.Karatsuba.Correctness
import Complexity.Algorithms.Lean.Query.Arith.Karatsuba.Cost
import Mathlib.Tactic.ComputeDegree

/-!
# Karatsuba multiplication

`karatsuba` multiplies concrete integer coefficient lists, including operands of different
lengths (padded with zeros, so the result can end in zeros), an odd length with an uneven split,
and empty operands. Over an arbitrary commutative ring, one level of the recursion is the
three-multiplication formula. The exact counts are checked at small lengths, against the closed
forms at powers of two and against the schoolbook count `n ^ 2`, which they meet only at `n = 1`.
The query count is the same under a dishonest oracle, and the packaged query bound is applied at
a concrete length.
-/

namespace ComplexityTests.Karatsuba

open Cslib Cslib.Query Cslib.Query.Karatsuba ArithQuery Polynomial

/-! ### Concrete products -/

/-- `(1 + 2X)(3 + 4X) = 3 + 10X + 8X²`. -/
example : (karatsuba [1, 2] [3, 4] : FreeM (ArithQuery ℤ) _).eval honest = [3, 10, 8] := by
  decide +kernel

/-- Unequal lengths: the shorter operand is padded to length `3`, so the result has `5`
coefficients, the last one zero. -/
example : (karatsuba [1, 2, 3] [4, 5] : FreeM (ArithQuery ℤ) _).eval honest =
    [4, 13, 22, 15, 0] := by
  decide +kernel

/-- Length `5` splits as `2 + 3`; negative coefficients exercise the subtractions. -/
example : (karatsuba [1, -1, 2, 0, 3] [2, 1, 0, -1, 1] : FreeM (ArithQuery ℤ) _).eval honest =
    [2, -1, 3, 1, 8, 0, 2, -3, 3] := by
  decide +kernel

/-- Empty operands. -/
example : (karatsuba [] [] : FreeM (ArithQuery ℤ) _).eval honest = [] := by decide +kernel

example : (karatsuba [] [5, 7] : FreeM (ArithQuery ℤ) _).eval honest = [0, 0, 0] := by
  decide +kernel

/-- One level of the recursion is Karatsuba's formula, over any commutative ring. -/
example {α : Type} [CommRing α] (a b c d : α) :
    ofCoeffList ((karatsuba [a, b] [c, d]).eval honest) =
      ofCoeffList [a * c, (a + b) * (c + d) - a * c - b * d, b * d] := by
  rw [ofCoeffList_eval_karatsuba]
  simp only [ofCoeffList_cons, ofCoeffList_nil, C_mul, C_sub, C_add]
  ring

/-- Correctness as a polynomial identity: the first two coefficients of `X + 1` and `X - 1`. -/
example : ofCoeffList ((karatsuba ((X + 1 : ℤ[X]).coeffsBelow 2)
    ((X - 1 : ℤ[X]).coeffsBelow 2)).eval honest) = X ^ 2 - 1 := by
  rw [ofCoeffList_eval_karatsuba_coeffsBelow (by compute_degree!) (by compute_degree!)]
  ring

/-! ### Exact counts -/

example : (List.range 9).map mulCount = [0, 1, 3, 7, 9, 17, 21, 25, 27] := by decide +kernel

example : (List.range 9).map addCount = [0, 0, 5, 19, 28, 60, 78, 100, 113] := by decide +kernel

/-- At `n = 8 = 2 ^ 3` the closed forms give `27` multiplications and `113` additions. -/
example : mulCount 8 = 27 ∧ 2 * addCount 8 + 16 * 8 = 13 * 27 + 3 :=
  ⟨mulCount_two_pow 3, addCount_two_pow 3⟩

/-- Fewer multiplications than the schoolbook method from `n = 2` on, but not at `n = 1`. -/
example : mulCount 5 < 5 ^ 2 := mulCount_lt_sq (by norm_num)

example : ¬ mulCount 1 < 1 ^ 2 := by simp

/-- At length `5` the multiplication count lies between `3 ^ ⌊log₂ 5⌋ = 9` and
`3 ^ ⌈log₂ 5⌉ = 27`. -/
example : 9 ≤ mulCount 5 ∧ mulCount 5 ≤ 27 := by decide +kernel

/-! ### Cost under every oracle -/

/-- An oracle answering every query with `0`. -/
private def zeroOracle : {ι : Type} → ArithQuery ℤ ι → ι
  | _, .add _ _ => 0
  | _, .sub _ _ => 0
  | _, .mul _ _ => 0

/-- The dishonest oracle sees the same `7 + 19` queries as the honest one. -/
example : (karatsuba [1, 2, 3] [4, 5] : FreeM (ArithQuery ℤ) _).countQueries zeroOracle = 26 := by
  decide +kernel

example : (karatsuba [1, 2, 3] [4, 5] : FreeM (ArithQuery ℤ) _).countQueries honest = 26 := by
  rw [countQueries_karatsuba]
  decide +kernel

/-- With multiplications ten times as expensive as additions, length `4` costs `10 · 9 + 28`. -/
example (o : {ι : Type} → ArithQuery ℤ ι → ι) (p q : List ℤ) (hp : p.length = 4)
    (hq : q.length = 4) : (karatsuba p q).cost o (weight 1 10) = 118 := by
  rw [cost_karatsuba, hp, hq]
  decide +kernel

/-- Operands of length at most `4` make at most `9 · 3 ^ 2 = 81` queries under every oracle. -/
example (o : {ι : Type} → ArithQuery ℤ ι → ι) (p q : List ℤ) (hp : p.length ≤ 4)
    (hq : q.length ≤ 4) : (karatsuba p q).countQueries o ≤ 81 := by
  have h := karatsuba_upperBound o 4 (p, q) (max_le hp hq)
  have h4 : Nat.clog 2 4 = 2 := Nat.clog_pow 2 2 one_lt_two
  simp only [h4] at h
  exact h

end ComplexityTests.Karatsuba
