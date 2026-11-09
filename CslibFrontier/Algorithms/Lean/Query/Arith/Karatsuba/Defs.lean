/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import CslibFrontier.Init

/-!
# Karatsuba multiplication as an arithmetic query program

Karatsuba multiplication of coefficient lists in the arithmetic query model
`FreeM (ArithQuery α)`. Every ring operation on coefficients is a query: the program is generic
in `α` with only `[Zero α]` (for zero padding), so it cannot compute on coefficients except by
asking the oracle. Its control flow depends only on the lengths of the inputs, so its query
counts are the same for every oracle.

`Cslib.Query.Karatsuba.mulFit n p q` multiplies the first `n` coefficients of `p` and `q`, padded
with zeros, and returns the `2 n - 1` coefficients of the product. For `n ≥ 2` it splits each
operand at `m = ⌊n / 2⌋` into a low half of length `m` and a high half of length `k = n - m`,
makes the three recursive products `p₀ q₀`, `(p₀ + p₁) (q₀ + q₁)` and `p₁ q₁`, and recombines
them as `p₀ q₀ + X ^ m ((p₀ + p₁) (q₀ + q₁) - p₀ q₀ - p₁ q₁) + X ^ (2 m) p₁ q₁` using only
additions and subtractions. `Cslib.Query.karatsuba p q` runs it at the longer length.

The exact query counts are `mulCount n` multiplications and `addCount n` additions and
subtractions, with `M(n) = M(⌊n/2⌋) + 2 M(⌈n/2⌉)` and `A(n) = A(⌊n/2⌋) + 2 A(⌈n/2⌉) + 4 n - 3`.
Correctness is in `CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Correctness`, and the cost
theorems and the `O(n ^ log₂ 3)` bounds are in
`CslibFrontier.Algorithms.Lean.Query.Arith.Karatsuba.Cost`.

## Main definitions

* `Cslib.Query.karatsuba`: Karatsuba multiplication of two coefficient lists.
* `Cslib.Query.Karatsuba.mulFit`: Karatsuba multiplication of the zero-padded first `n`
  coefficients.
* `Cslib.Query.Karatsuba.addList`, `Cslib.Query.Karatsuba.subList`, `Cslib.Query.Karatsuba.addAt`:
  coefficientwise addition and subtraction, and addition at an offset.
* `Cslib.Query.Karatsuba.mulCount`, `Cslib.Query.Karatsuba.addCount`: the multiplication and
  addition counts of `mulFit`.

## Main results

* `Cslib.Query.Karatsuba.length_eval_mulFit`: `mulFit n` returns `2 n - 1` coefficients under
  every oracle.
* `Cslib.Query.length_eval_karatsuba`: `karatsuba p q` returns `2 max(|p|, |q|) - 1` coefficients.

## References

* [Karatsuba and Ofman, *Multiplication of Many-Digital Numbers by Automatic
  Computers*][KaratsubaOfman1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Problem 30-1.
-/

public section

namespace Cslib.Query

variable {α : Type}

open ArithQuery

namespace Karatsuba

/-- Coefficientwise sum of two coefficient lists: one addition query for each position where
both lists have a coefficient; the overhang of the longer list is copied without a query. -/
@[expose] def addList : List α → List α → FreeM (ArithQuery α) (List α)
  | [], q => pure q
  | a :: p, [] => pure (a :: p)
  | a :: p, b :: q => do
    let c ← doAdd a b
    let r ← addList p q
    return c :: r

/-- Coefficientwise difference `p - q`: one subtraction query for each coefficient of `q`, with
`p` padded by zeros if it is shorter. -/
@[expose] def subList [Zero α] : List α → List α → FreeM (ArithQuery α) (List α)
  | p, [] => pure p
  | p, b :: q => do
    let c ← doSub (p.headD 0) b
    let r ← subList p.tail q
    return c :: r

/-- Add `w` into `base` starting at position `m`, that is, `base + X ^ m * w` on coefficient lists
when `m ≤ base.length`. -/
@[expose] def addAt (m : ℕ) (base w : List α) : FreeM (ArithQuery α) (List α) := do
  let r ← addList (base.drop m) w
  return base.take m ++ r

/-- Karatsuba multiplication of the first `n` coefficients of `p` and `q`, padded with zeros.
The result has `2 n - 1` coefficients. -/
@[expose] def mulFit [Zero α] : ℕ → List α → List α → FreeM (ArithQuery α) (List α)
  | 0, _, _ => pure []
  | 1, p, q => do
    let c ← doMul (p.headD 0) (q.headD 0)
    return [c]
  | n + 2, p, q => do
    let m := (n + 2) / 2
    let k := n + 2 - m
    let p₀ := p.takeD m 0
    let p₁ := (p.drop m).takeD k 0
    let q₀ := q.takeD m 0
    let q₁ := (q.drop m).takeD k 0
    let s ← addList p₀ p₁
    let t ← addList q₀ q₁
    let z₀ ← mulFit m p₀ q₀
    let z₁ ← mulFit k s t
    let z₂ ← mulFit k p₁ q₁
    let w₁ ← subList z₁ z₀
    let w ← subList w₁ z₂
    addAt m (z₀ ++ 0 :: z₂) w
termination_by n _ _ => n
decreasing_by all_goals omega

/-- The number of multiplication queries of `mulFit n`:
`M(0) = 0`, `M(1) = 1` and `M(n) = M(⌊n/2⌋) + 2 M(⌈n/2⌉)`. -/
@[expose] def mulCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => mulCount ((n + 2) / 2) + 2 * mulCount (n + 2 - (n + 2) / 2)
termination_by n => n
decreasing_by all_goals omega

/-- The number of addition and subtraction queries of `mulFit n`:
`A(0) = A(1) = 0` and `A(n) = A(⌊n/2⌋) + 2 A(⌈n/2⌉) + 4 n - 3`. -/
@[expose] def addCount : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => addCount ((n + 2) / 2) + 2 * addCount (n + 2 - (n + 2) / 2) + (4 * n + 5)
termination_by n => n
decreasing_by all_goals omega

end Karatsuba

/-- **Karatsuba multiplication** of two coefficient lists, constant coefficient first, at the
length of the longer one. -/
@[expose] def karatsuba [Zero α] (p q : List α) : FreeM (ArithQuery α) (List α) :=
  Karatsuba.mulFit (max p.length q.length) p q

namespace Karatsuba

variable (o : {ι : Type} → ArithQuery α ι → ι)

/-- `addList p q` has the length of the longer list. -/
theorem length_eval_addList (p q : List α) :
    ((addList p q).eval o).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [addList]
  | cons a p ih =>
    cases q with
    | nil => simp [addList]
    | cons b q => simp [addList, ih]

/-- `subList p q` has the length of the longer list. -/
theorem length_eval_subList [Zero α] (p q : List α) :
    ((subList p q).eval o).length = max p.length q.length := by
  induction q generalizing p with
  | nil => simp [subList]
  | cons b q ih =>
    simp only [subList, doSub, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure,
      List.length_cons, ih, List.length_tail]
    omega

/-- `mulFit n` returns `2 n - 1` coefficients under every oracle. -/
theorem length_eval_mulFit [Zero α] (n : ℕ) (p q : List α) :
    ((mulFit n p q).eval o).length = 2 * n - 1 := by
  induction n using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
    match n with
    | 0 => simp [mulFit]
    | 1 => simp [mulFit]
    | n + 2 =>
      rw [mulFit]
      simp only [addAt, FreeM.eval_bind, FreeM.eval_pure, List.length_append, List.length_take,
        List.length_drop, length_eval_addList, length_eval_subList, List.length_cons]
      rw [ih _ (by omega), ih _ (by omega), ih _ (by omega)]
      omega

end Karatsuba

/-- `karatsuba p q` returns `2 max(|p|, |q|) - 1` coefficients under every oracle. -/
theorem length_eval_karatsuba [Zero α] (o : {ι : Type} → ArithQuery α ι → ι) (p q : List α) :
    ((karatsuba p q).eval o).length = 2 * max p.length q.length - 1 :=
  Karatsuba.length_eval_mulFit o _ p q

end Cslib.Query
