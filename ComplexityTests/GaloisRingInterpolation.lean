/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PolyTime.GaloisRingInterpolation

/-! # Polynomials over `(ℤ / 2 ^ p)[U] / (f)` and Lagrange interpolation

Concrete evaluation and interpolation in the Galois ring `(ℤ / 8)[U] / (U ^ 2 + U + 1)`, at the
nodes `0, 1, U`, whose differences `1, U, U - 1` are units; the correctness statements; and the
polynomial-time certificate of interpolation in closed form. -/

namespace ComplexityTests.GaloisRingInterpolation

open Cslib.GaloisRingArith Turing.MultiTapeTM

/-- The nodes `0, 1, U`. -/
def nodes : List (List ℕ) := [[0, 0], [1, 0], [0, 1]]

/-- The values `1, 2, 3 + U`. -/
def values : List (List ℕ) := [[1, 0], [2, 0], [3, 1]]

-- Horner evaluation of `1 + U z + z ^ 2` at `z = U`: `1 + U ^ 2 + U ^ 2 = 1 + 2 U ^ 2 = 7 + 6 U`.
example : peval 3 [1, 1] [[1, 0], [0, 1], [1, 0]] [0, 1] = [7, 6] := by decide

-- `(z - U) (z - 1) = U - (1 + U) z + z ^ 2`, that is `[U, -1 - U, 1]`.
example : pmulLinear 3 [1, 1] [0, 1] [[7, 0], [1, 0]] = [[0, 1], [7, 7], [1, 0]] := by decide

-- The interpolating polynomial takes the values `1, 2, 3 + U` at `0, 1, U`.
example : (nodes.map fun z => peval 3 [1, 1] (interp 3 [1, 1] nodes values) z) = values := by
  decide

-- It has three coefficients.
example : (interp 3 [1, 1] nodes values).length = 3 := by decide

/-- Interpolation takes the given values, given correct inverses of the denominators. -/
example (v y : List (List ℕ))
    (hinv : ∀ i < v.length, val 3 [1, 1] (basisDen 3 [1, 1] v i) *
      val 3 [1, 1] (inv 3 [1, 1] (basisDen 3 [1, 1] v i)) = 1) {k : ℕ} (hk : k < v.length) :
    (pval 3 [1, 1] (interp 3 [1, 1] v y)).eval (val 3 [1, 1] (v.getD k [])) =
      val 3 [1, 1] (y.getD k []) :=
  eval_pval_interp v y hinv hk

/-- **Interpolation in polynomial time**, on the ring description `(p, fl)` with `p` in unary,
the nodes and the values. -/
example : ComputableInPolyTime
    (fun q : (ℕ × List ℕ) × (List (List ℕ) × List (List ℕ)) => interp q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encUnary (encList encNat))
      (encPair (encList (encList encNat)) (encList (encList encNat))))
    (encList (encList encNat)) := by
  fun_prop

end ComplexityTests.GaloisRingInterpolation
