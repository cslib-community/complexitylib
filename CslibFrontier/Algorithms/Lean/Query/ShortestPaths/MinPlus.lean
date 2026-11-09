/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Arith.FloydWarshall
public import CslibFrontier.Algorithms.Lean.Query.Arith.MatMul
public import CslibFrontier.Algorithms.ShortestPaths.Tripartite
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# All-pairs shortest paths and the (min,+) product: cost-preserving reductions

All-pairs shortest paths (APSP) and the (min,+) matrix product reduce to each other in the query
model `FreeM Q`, for any query type `Q`.

* **APSP to (min,+) products.** `Cslib.Query.apspBySquaring mp W` squares `withOneDiag W` exactly
  `⌈log₂ (n - 1)⌉` times with a product subroutine `mp`. If `mp` computes (min,+) products, the
  result is the shortest-distance matrix of every `W` without negative cycles, and the cost is
  `⌈log₂ (n - 1)⌉` times a bound on the cost of `mp`.
* **(min,+) products to APSP.** `Cslib.Query.minPlusViaAPSP apsp A B` calls an APSP subroutine
  once, on the tripartite graph of `A` and `B` with `3 n` vertices, and reads off a block. If
  `apsp` computes shortest distances for graphs without negative cycles, the result is `A * B`,
  and the cost is exactly the cost of that one call.

So an algorithm for either problem with cost `T(n)` yields one for the other with cost
`⌈log₂ (n - 1)⌉ T(n)` or `T(3 n)`. Both reductions are generic in the entry type: they issue no
queries of their own and cannot inspect weights. Indexing and the construction of the tripartite
matrix are pure code, which `FreeM` does not charge.

Instantiated with `Cslib.Query.schoolbookMatMul` and `Cslib.Query.floydWarshall` in the arithmetic
query model, they give APSP with `⌈log₂ (n - 1)⌉ n ^ 2 (n cMul + (n - 1) cAdd)` cost (CLRS
Section 25.1) and the (min,+) product with `27 n ^ 3 (cAdd + cMul)` cost.

## Main definitions

* `Cslib.Query.squareIter`: square a matrix `k` times with a product subroutine.
* `Cslib.Query.apspBySquaring`: APSP by repeated squaring.
* `Cslib.Query.minPlusViaAPSP`: the (min,+) product by one call of an APSP subroutine.

## Main results

* `Cslib.Query.isShortestDistances_apspBySquaring`, `Cslib.Query.cost_apspBySquaring_le`,
  `Cslib.Query.cost_apspBySquaring`: APSP reduces to `⌈log₂ (n - 1)⌉` (min,+) products.
* `Cslib.Query.eval_minPlusViaAPSP`, `Cslib.Query.cost_minPlusViaAPSP`: the (min,+) product
  reduces to one APSP instance on `3 n` vertices.
* `Cslib.Query.isShortestDistances_apspBySquaring_schoolbook`,
  `Cslib.Query.cost_apspBySquaring_schoolbook`, `Cslib.Query.eval_minPlusViaAPSP_floydWarshall`,
  `Cslib.Query.cost_minPlusViaAPSP_floydWarshall`: the instantiations.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 25.1.
* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018].
-/

public section

open Cslib.Algorithms.ShortestPaths

namespace Cslib.Query

/-! ### APSP from (min,+) products by repeated squaring -/

section Squaring

variable {Q : Type → Type} {S : Type}

/-- Square the matrix `k` times with the product subroutine `mp`. -/
@[expose] def squareIter {n : ℕ}
    (mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S →
      FreeM Q (Matrix (Fin n) (Fin n) S)) :
    ℕ → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)
  | 0, D => pure D
  | k + 1, D => do
    let D' ← mp D D
    squareIter mp k D'

/-- **APSP by repeated squaring**, as a reduction to a matrix-product subroutine `mp`: square
`withOneDiag W` exactly `⌈log₂ (n - 1)⌉` times. The program issues no queries of its own. -/
@[expose] def apspBySquaring [One S] {n : ℕ}
    (mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S))
    (W : Matrix (Fin n) (Fin n) S) : FreeM Q (Matrix (Fin n) (Fin n) S) :=
  squareIter mp (Nat.clog 2 (n - 1)) (withOneDiag W)

theorem eval_squareIter [Semiring S] {n : ℕ} (oracle : {ι : Type} → Q ι → ι)
    {mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)}
    (hmp : ∀ A B, (mp A B).eval oracle = A * B) :
    ∀ (k : ℕ) (D : Matrix (Fin n) (Fin n) S), (squareIter mp k D).eval oracle = D ^ 2 ^ k
  | 0, D => by simp [squareIter]
  | k + 1, D => by
    rw [squareIter, FreeM.eval_bind, hmp, eval_squareIter oracle hmp k, ← sq, ← pow_mul,
      ← pow_succ']

theorem cost_squareIter_le {T : Type} [AddCommMonoid T] [PartialOrder T] [IsOrderedAddMonoid T]
    {n : ℕ} (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)}
    {t : T} (hmp : ∀ A B, (mp A B).cost oracle weight ≤ t) :
    ∀ (k : ℕ) (D : Matrix (Fin n) (Fin n) S), (squareIter mp k D).cost oracle weight ≤ k • t
  | 0, D => by simp [squareIter]
  | k + 1, D => by
    rw [squareIter, FreeM.cost_bind, succ_nsmul']
    exact add_le_add (hmp D D) (cost_squareIter_le oracle weight hmp k _)

theorem cost_squareIter {T : Type} [AddMonoid T] {n : ℕ} (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    {mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)}
    {t : T} (hmp : ∀ A B, (mp A B).cost oracle weight = t) :
    ∀ (k : ℕ) (D : Matrix (Fin n) (Fin n) S), (squareIter mp k D).cost oracle weight = k • t
  | 0, D => by simp [squareIter]
  | k + 1, D => by
    rw [squareIter, FreeM.cost_bind, succ_nsmul', hmp, cost_squareIter oracle weight hmp k]

/-- The cost of `apspBySquaring`: at most `⌈log₂ (n - 1)⌉` times a bound on the cost of a call
of the product subroutine. -/
theorem cost_apspBySquaring_le [One S] {T : Type} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] {n : ℕ} (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)}
    {t : T} (hmp : ∀ A B, (mp A B).cost oracle weight ≤ t) (W : Matrix (Fin n) (Fin n) S) :
    (apspBySquaring mp W).cost oracle weight ≤ Nat.clog 2 (n - 1) • t :=
  cost_squareIter_le oracle weight hmp _ _

/-- The cost of `apspBySquaring`: exactly `⌈log₂ (n - 1)⌉` times the cost of a call of the
product subroutine, when that cost does not depend on the operands. -/
theorem cost_apspBySquaring [One S] {T : Type} [AddMonoid T] {n : ℕ}
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {mp : Matrix (Fin n) (Fin n) S → Matrix (Fin n) (Fin n) S → FreeM Q (Matrix (Fin n) (Fin n) S)}
    {t : T} (hmp : ∀ A B, (mp A B).cost oracle weight = t) (W : Matrix (Fin n) (Fin n) S) :
    (apspBySquaring mp W).cost oracle weight = Nat.clog 2 (n - 1) • t :=
  cost_squareIter oracle weight hmp _ _

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

/-- **APSP reduces to (min,+) products.** If `mp` computes (min,+) products under `oracle`, then
`apspBySquaring mp` computes shortest distances for every weight matrix without negative
cycles. -/
theorem isShortestDistances_apspBySquaring {n : ℕ} (oracle : {ι : Type} → Q ι → ι)
    {mp : Matrix (Fin n) (Fin n) (MinTropical R) → Matrix (Fin n) (Fin n) (MinTropical R) →
      FreeM Q (Matrix (Fin n) (Fin n) (MinTropical R))}
    (hmp : ∀ A B, (mp A B).eval oracle = A * B)
    {W : Matrix (Fin n) (Fin n) (MinTropical R)} (hW : NoNegCycle W) :
    IsShortestDistances W ((apspBySquaring mp W).eval oracle) := by
  rw [apspBySquaring, eval_squareIter oracle hmp]
  apply isShortestDistances_withOneDiag_pow hW
  rw [Fintype.card_fin]
  exact Nat.le_pow_clog one_lt_two _

end Squaring

/-! ### (min,+) products from APSP on the tripartite graph -/

section ViaAPSP

variable {Q : Type → Type} {S : Type} [Zero S]

/-- **The (min,+) product reduces to APSP**: run the APSP subroutine on the tripartite graph of
`A` and `B` with `3 n` vertices and read off the block from layer `0` to layer `2`. The program
issues no queries of its own. -/
@[expose] def minPlusViaAPSP {n : ℕ}
    (apsp : Matrix (Fin (3 * n)) (Fin (3 * n)) S → FreeM Q (Matrix (Fin (3 * n)) (Fin (3 * n)) S))
    (A B : Matrix (Fin n) (Fin n) S) : FreeM Q (Matrix (Fin n) (Fin n) S) := do
  let D ← apsp ((tripartite A B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
  return Matrix.of fun i k => D (finProdFinEquiv (0, i)) (finProdFinEquiv (2, k))

/-- The cost of `minPlusViaAPSP` is the cost of its one call of the APSP subroutine. -/
theorem cost_minPlusViaAPSP {T : Type} [AddMonoid T] {n : ℕ} (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    (apsp : Matrix (Fin (3 * n)) (Fin (3 * n)) S → FreeM Q (Matrix (Fin (3 * n)) (Fin (3 * n)) S))
    (A B : Matrix (Fin n) (Fin n) S) :
    (minPlusViaAPSP apsp A B).cost oracle weight =
      (apsp ((tripartite A B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)).cost
        oracle weight := by
  rw [minPlusViaAPSP, FreeM.cost_bind, FreeM.cost_pure, add_zero]

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

/-- **The (min,+) product reduces to APSP.** If `apsp` computes shortest distances under
`oracle` for every graph on `3 n` vertices without negative cycles, then `minPlusViaAPSP apsp`
computes (min,+) products. -/
theorem eval_minPlusViaAPSP {n : ℕ} (oracle : {ι : Type} → Q ι → ι)
    {apsp : Matrix (Fin (3 * n)) (Fin (3 * n)) (MinTropical R) →
      FreeM Q (Matrix (Fin (3 * n)) (Fin (3 * n)) (MinTropical R))}
    (happsp : ∀ W, NoNegCycle W → IsShortestDistances W ((apsp W).eval oracle))
    (A B : Matrix (Fin n) (Fin n) (MinTropical R)) :
    (minPlusViaAPSP apsp A B).eval oracle = A * B := by
  have hD := happsp _ ((noNegCycle_tripartite A B).submatrix finProdFinEquiv.symm)
  rw [minPlusViaAPSP, FreeM.eval_bind, FreeM.eval_pure]
  ext i k
  exact hD.tripartite_block finProdFinEquiv i k

end ViaAPSP

/-! ### Instantiations in the arithmetic query model -/

section Instances

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

/-- Repeated squaring with schoolbook (min,+) products computes shortest distances. -/
theorem isShortestDistances_apspBySquaring_schoolbook
    (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) {n : ℕ}
    {W : Matrix (Fin n) (Fin n) (MinTropical R)} (hW : NoNegCycle W) :
    IsShortestDistances W ((apspBySquaring (schoolbookMatMul n) W).eval oracle) :=
  isShortestDistances_apspBySquaring oracle (eval_schoolbookMatMul oracle hadd hmul n) hW

/-- Repeated squaring with schoolbook products costs `⌈log₂ (n - 1)⌉ n ^ 2 (n cMul + (n - 1) cAdd)`
under every oracle: the `Θ(n ^ 3 log n)` algorithm of CLRS Section 25.1. -/
theorem cost_apspBySquaring_schoolbook {S : Type} [Zero S] [One S]
    (oracle : {ι : Type} → ArithQuery S ι → ι) (cAdd cMul n : ℕ) (W : Matrix (Fin n) (Fin n) S) :
    (apspBySquaring (schoolbookMatMul n) W).cost oracle (ArithQuery.weight cAdd cMul) =
      Nat.clog 2 (n - 1) * (n ^ 2 * (n * cMul + (n - 1) * cAdd)) := by
  rw [cost_apspBySquaring oracle _ (cost_schoolbookMatMul oracle cAdd cMul n), smul_eq_mul]

/-- Floyd–Warshall on the tripartite graph computes (min,+) products. -/
theorem eval_minPlusViaAPSP_floydWarshall
    (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (MinTropical R)) :
    (minPlusViaAPSP (floydWarshall (3 * n)) A B).eval oracle = A * B :=
  eval_minPlusViaAPSP oracle (fun _ hW => isShortestDistances_floydWarshall oracle hadd hmul hW)
    A B

/-- Floyd–Warshall on the tripartite graph costs `(3 n) ^ 3 (cAdd + cMul)` under every
oracle. -/
theorem cost_minPlusViaAPSP_floydWarshall {S : Type} [Zero S] [One S]
    (oracle : {ι : Type} → ArithQuery S ι → ι) (cAdd cMul n : ℕ) (A B : Matrix (Fin n) (Fin n) S) :
    (minPlusViaAPSP (floydWarshall (3 * n)) A B).cost oracle (ArithQuery.weight cAdd cMul) =
      (3 * n) ^ 3 * (cAdd + cMul) := by
  rw [cost_minPlusViaAPSP, cost_floydWarshall]

end Instances

end Cslib.Query
