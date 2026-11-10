/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate
public import Cslib.Algorithms.Lean.Query.Arith.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Schoolbook matrix multiplication as an arithmetic query program

`Cslib.Query.schoolbookMatMul n A B` multiplies two `n × n` matrices in the arithmetic query model
`FreeM (ArithQuery S)`: each entry is the dot product `∑ k, A i k * B k j`, computed by
`Cslib.Query.schoolbookDot` with `n` multiplication queries and `n - 1` addition queries. The
program is generic in `S` with only `[Zero S]` (for the empty dot product), so it can combine
entries only by asking the oracle, and its control flow does not depend on the answers: it makes
`n ^ 2 * n` multiplications and `n ^ 2 * (n - 1)` additions under every oracle.

Over `MinTropical R` an addition query is a comparison (a minimum) and a multiplication query is
an addition of weights, so this is the cubic (min,+) product.

## Main definitions

* `Cslib.Query.schoolbookDot`: the dot product as a query program.
* `Cslib.Query.schoolbookMatMul`: the schoolbook matrix product as a query program.

## Main results

* `Cslib.Query.eval_schoolbookDot`, `Cslib.Query.eval_schoolbookMatMul`: under an oracle that
  answers additions and multiplications honestly, the programs compute `∑ k, a k * b k` and
  `A * B`, over any non-unital non-associative semiring.
* `Cslib.Query.cost_schoolbookDot`, `Cslib.Query.cost_schoolbookMatMul`: the exact weighted costs
  `n * cMul + (n - 1) * cAdd` and `n ^ 2 * (n * cMul + (n - 1) * cAdd)` under every oracle.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Sections 4.2
  and 25.1.
-/

public section

namespace Cslib.Query

variable {S : Type}

/-- The dot product `∑ k, a k * b k`, computed left to right with `n` multiplication queries and
`n - 1` addition queries. -/
@[expose] def schoolbookDot [Zero S] : (n : ℕ) → (Fin n → S) → (Fin n → S) → FreeM (ArithQuery S) S
  | 0, _, _ => pure 0
  | 1, a, b => ArithQuery.doMul (a 0) (b 0)
  | n + 2, a, b => do
    let p ← ArithQuery.doMul (a 0) (b 0)
    let r ← schoolbookDot (n + 1) (fun i => a i.succ) (fun i => b i.succ)
    ArithQuery.doAdd p r

theorem eval_schoolbookDot [AddCommMonoid S] [Mul S] (oracle : {ι : Type} → ArithQuery S ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) :
    ∀ (n : ℕ) (a b : Fin n → S), (schoolbookDot n a b).eval oracle = ∑ k, a k * b k
  | 0, a, b => by simp [schoolbookDot]
  | 1, a, b => by simp [schoolbookDot, hmul]
  | n + 2, a, b => by
    rw [Fin.sum_univ_succ]
    simp only [schoolbookDot, FreeM.eval_bind, FreeM.eval_lift, hmul, hadd,
      eval_schoolbookDot oracle hadd hmul (n + 1)]

theorem cost_schoolbookDot [Zero S] (oracle : {ι : Type} → ArithQuery S ι → ι) (cAdd cMul : ℕ) :
    ∀ (n : ℕ) (a b : Fin n → S),
      (schoolbookDot n a b).cost oracle (ArithQuery.weight cAdd cMul) = n * cMul + (n - 1) * cAdd
  | 0, a, b => by simp [schoolbookDot]
  | 1, a, b => by simp [schoolbookDot, ArithQuery.weight]
  | n + 2, a, b => by
    simp only [schoolbookDot, FreeM.cost_bind, FreeM.cost_lift, ArithQuery.weight,
      cost_schoolbookDot oracle cAdd cMul (n + 1)]
    rw [show n + 2 - 1 = n + 1 from rfl, Nat.add_sub_cancel]
    ring

/-- The schoolbook matrix product: every entry is a `schoolbookDot`. Over `MinTropical R` this is
the (min,+) product with `n ^ 3` additions of weights and `n ^ 2 * (n - 1)` comparisons. -/
@[expose] def schoolbookMatMul [Zero S] (n : ℕ) (A B : Matrix (Fin n) (Fin n) S) :
    FreeM (ArithQuery S) (Matrix (Fin n) (Fin n) S) :=
  FreeM.tabulateMatrix n fun i j => schoolbookDot n (A i) (fun k => B k j)

theorem eval_schoolbookMatMul [NonUnitalNonAssocSemiring S]
    (oracle : {ι : Type} → ArithQuery S ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b)
    (n : ℕ) (A B : Matrix (Fin n) (Fin n) S) : (schoolbookMatMul n A B).eval oracle = A * B := by
  rw [schoolbookMatMul, FreeM.eval_tabulateMatrix]
  ext i j
  rw [Matrix.of_apply, eval_schoolbookDot oracle hadd hmul, Matrix.mul_apply]

theorem cost_schoolbookMatMul [Zero S] (oracle : {ι : Type} → ArithQuery S ι → ι)
    (cAdd cMul n : ℕ) (A B : Matrix (Fin n) (Fin n) S) :
    (schoolbookMatMul n A B).cost oracle (ArithQuery.weight cAdd cMul) =
      n ^ 2 * (n * cMul + (n - 1) * cAdd) := by
  simp only [schoolbookMatMul, FreeM.cost_tabulateMatrix, cost_schoolbookDot, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Cslib.Query
