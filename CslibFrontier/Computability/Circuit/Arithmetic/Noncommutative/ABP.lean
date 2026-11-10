/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.FreeAlgebra
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Non-commutative algebraic branching programs and Nisan's lower bound

A *homogeneous layered non-commutative ABP* of degree `d` over the variables `X`
(`Cslib.Circuits.Arithmetic.NoncommABP`) has layers `0, …, d` of `width k` vertices, a single
source (`width 0 = 1`) and a single sink (`width d = 1`). The edge from vertex `i` of layer `k` to
vertex `j` of layer `k + 1` is labelled by the homogeneous linear form
`∑ x, weight k x i j • x` (`NoncommABP.edge`). A path computes the product of its labels in order
from source to sink, and the ABP computes the sum over all paths (`NoncommABP.polynomial`), an
element of the free algebra `FreeAlgebra K X`. The *size* is the number of vertices,
`∑_{k ≤ d} width k` (`NoncommABP.size`). Only layers `0, …, d` matter; widths and weights beyond
layer `d` are ignored.

*Nisan's partial derivative matrix* `M_k(f)` (`Cslib.Circuits.Arithmetic.nisanMatrix k m f`) has
rows indexed by the words of length `k`, columns by the words of length `m`, and entry `(u, v)` the
coefficient of the word `u v` in `f`. Words are tuples `Fin k → X`, read by `FreeMonoid.ofFn`.

* **Factorization** (Nisan, proof of Theorem 1; Saptharishi, Subclaim 11.3). If `k + m = d`,
  then `M_k` of the computed polynomial is the product of the `n^k × width k` matrix of
  coefficients of the polynomials `pre k l` computed from the source to the vertices of layer `k`,
  and the `width k × n^m` matrix of coefficients of the polynomials `suf k m l` computed from those
  vertices to the sink (`NoncommABP.nisanMatrix_eq_mul`).
* **Nisan's lower bound** (Nisan, Theorem 1; Saptharishi, proof of Theorem 11.2). Hence layer `k`
  has at least `rank M_k(f)` vertices (`NoncommABP.rank_nisanMatrix_le_width`), and the size is at
  least `∑_{k ≤ d} rank M_k(f)` (`NoncommABP.sum_rank_nisanMatrix_le_size`).

The matching construction is in
`CslibFrontier.Computability.Circuit.Arithmetic.Noncommutative.Nisan`.

**Size convention.** The size counts every vertex, the source and the sink included, as in
Nisan's Definition 1, and the bound sums `rank M_k(f)` over `0 ≤ k ≤ d`, as in Nisan's Theorem 1.
The displayed statement of Theorem 11.2 in Saptharishi's survey leaves out the final term
`rank M_d(f)`, which is `1` for nonzero `f`.

## Main definitions

* `Cslib.Circuits.Arithmetic.NoncommABP`: homogeneous layered non-commutative ABPs.
* `Cslib.Circuits.Arithmetic.NoncommABP.polynomial`, `NoncommABP.size`.
* `Cslib.Circuits.Arithmetic.nisanMatrix`: Nisan's partial derivative matrix.

## Main results

* `Cslib.Circuits.Arithmetic.NoncommABP.nisanMatrix_eq_mul`: the factorization through a layer.
* `Cslib.Circuits.Arithmetic.NoncommABP.rank_nisanMatrix_le_width`: the width lower bound.
* `Cslib.Circuits.Arithmetic.NoncommABP.sum_rank_nisanMatrix_le_size`: the size lower bound.
* `Cslib.Circuits.Arithmetic.NoncommABP.width_le_size`: every layer is at most the size.

## References

* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991NonCommutative],
  extended abstract, §2 (Definition 1) and §3 (Theorem 1 and its proof sketch).
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], Chapter 11 (Definition 11.1, Theorem 11.2,
  Subclaim 11.3); the chapter is unchanged from release v9.0.3.
-/

public section

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra

/-- A homogeneous layered non-commutative ABP of degree `d` over the variables `X`: layers
`0, …, d`, one source, one sink, and homogeneous linear forms on the edges. -/
structure NoncommABP (K : Type*) [CommSemiring K] (X : Type*) (d : ℕ) where
  /-- The number of vertices in layer `k`. -/
  width : ℕ → ℕ
  /-- There is a single source. -/
  width_zero : width 0 = 1
  /-- There is a single sink. -/
  width_deg : width d = 1
  /-- `weight k x i j` is the coefficient of `x` on the edge from vertex `i` of layer `k` to
  vertex `j` of layer `k + 1`. -/
  weight : (k : ℕ) → X → Matrix (Fin (width k)) (Fin (width (k + 1))) K

/-- Nisan's partial derivative matrix `M_k(f)`: rows are the words of length `k`, columns the
words of length `m`, and the entry at `(u, v)` is the coefficient of the word `u v` in `f`
([Saptharishi2026Survey], Definition 11.1, with `m = d - k`). -/
noncomputable def nisanMatrix {K : Type*} [CommSemiring K] {X : Type*} (k m : ℕ)
    (f : FreeAlgebra K X) : Matrix (Fin k → X) (Fin m → X) K :=
  Matrix.of fun u v => coeff (FreeMonoid.ofFn u * FreeMonoid.ofFn v) f

/-- The entries of Nisan's partial derivative matrix. -/
@[simp] theorem nisanMatrix_apply {K : Type*} [CommSemiring K] {X : Type*} (k m : ℕ)
    (f : FreeAlgebra K X) (u : Fin k → X) (v : Fin m → X) :
    nisanMatrix k m f u v = coeff (FreeMonoid.ofFn u * FreeMonoid.ofFn v) f := by
  simp [nisanMatrix]

namespace NoncommABP

variable {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {d : ℕ}
  (A : NoncommABP K X d)

/-- The linear form `∑ x, weight k x i j • x` on the edge from vertex `i` of layer `k` to vertex
`j` of layer `k + 1`. -/
@[expose] noncomputable def edge (k : ℕ) (i : Fin (A.width k)) (j : Fin (A.width (k + 1))) :
    FreeAlgebra K X :=
  ∑ x, A.weight k x i j • ι K x

/-- The polynomial computed from the source to vertex `j` of layer `k`. -/
noncomputable def pre : (k : ℕ) → Fin (A.width k) → FreeAlgebra K X
  | 0, _ => 1
  | k + 1, j => ∑ i, pre k i * A.edge k i j

/-- The polynomial computed from vertex `i` of layer `k` through the next `m` layers. -/
noncomputable def suf : (k m : ℕ) → Fin (A.width k) → FreeAlgebra K X
  | _, 0, _ => 1
  | k, m + 1, i => ∑ j, A.edge k i j * suf (k + 1) m j

/-- The polynomial computed by the ABP: the sum over the vertices of layer `d`, that is, the
sink. -/
@[expose] noncomputable def polynomial : FreeAlgebra K X :=
  ∑ j, A.pre d j

omit [Fintype X] in
/-- The size: the number of vertices in layers `0, …, d`, the sink included. -/
@[expose] def size : ℕ :=
  ∑ k ∈ Finset.range (d + 1), A.width k

omit [Fintype X] in
/-- Every layer has at most `size` vertices. -/
theorem width_le_size {k : ℕ} (hk : k ≤ d) : A.width k ≤ A.size :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The source computes `1`. -/
theorem pre_zero (j : Fin (A.width 0)) : A.pre 0 j = 1 := by
  simp [pre]

/-- The polynomials of layer `k + 1` from those of layer `k`. -/
theorem pre_succ (k : ℕ) (j : Fin (A.width (k + 1))) :
    A.pre (k + 1) j = ∑ i, A.pre k i * A.edge k i j := by
  simp [pre]

/-- The empty path computes `1`. -/
theorem suf_zero (k : ℕ) (i : Fin (A.width k)) : A.suf k 0 i = 1 := by
  simp [suf]

/-- The polynomials through `m + 1` layers from those through `m` layers. -/
theorem suf_succ (k m : ℕ) (i : Fin (A.width k)) :
    A.suf k (m + 1) i = ∑ j, A.edge k i j * A.suf (k + 1) m j := by
  simp [suf]

/-- Cutting the ABP at layer `k`: every source–sink path passes through exactly one vertex of
layer `k`. -/
theorem polynomial_eq_sum_pre_mul_suf (k m : ℕ) (h : k + m = d) :
    A.polynomial = ∑ l, A.pre k l * A.suf k m l := by
  induction m generalizing k with
  | zero =>
    subst h
    simp [polynomial, suf_zero]
  | succ m ih =>
    rw [ih (k + 1) (by omega)]
    simp only [pre_succ, suf_succ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

/-- Edge labels are homogeneous of degree `1`. -/
theorem isHomogeneous_edge (k : ℕ) (i : Fin (A.width k)) (j : Fin (A.width (k + 1))) :
    (A.edge k i j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ fun x _ => (isHomogeneous_ι x).smul _

/-- The polynomials computed at layer `k` are homogeneous of degree `k`. -/
theorem isHomogeneous_pre (k : ℕ) (j : Fin (A.width k)) : (A.pre k j).IsHomogeneous k := by
  induction k with
  | zero => simpa [pre_zero] using isHomogeneous_one
  | succ k ih =>
    rw [pre_succ]
    exact IsHomogeneous.sum _ _ fun i _ => (ih i).mul (A.isHomogeneous_edge k i j)

/-- The polynomials computed through `m` layers are homogeneous of degree `m`. -/
theorem isHomogeneous_suf (k m : ℕ) (i : Fin (A.width k)) :
    (A.suf k m i).IsHomogeneous m := by
  induction m generalizing k with
  | zero => simpa [suf_zero] using isHomogeneous_one
  | succ m ih =>
    rw [suf_succ, Nat.add_comm m 1]
    exact IsHomogeneous.sum _ _ fun j _ => (A.isHomogeneous_edge k i j).mul (ih (k + 1) j)

/-- The computed polynomial is homogeneous of degree `d`. -/
theorem isHomogeneous_polynomial : A.polynomial.IsHomogeneous d :=
  IsHomogeneous.sum _ _ fun j _ => A.isHomogeneous_pre d j

/-- The coefficient of the variable `x` in an edge label. -/
theorem coeff_of_edge (k : ℕ) (i : Fin (A.width k)) (j : Fin (A.width (k + 1))) (x : X) :
    coeff (FreeMonoid.of x) (A.edge k i j) = A.weight k x i j := by
  classical
  simp [edge, coeff_ι, Finsupp.single_apply, FreeMonoid.of_injective.eq_iff]

/-- The coefficients of the polynomials of layer `k + 1` from those of layer `k`. -/
theorem coeff_pre_succ (k : ℕ) (j : Fin (A.width (k + 1))) (u : Fin k → X) (x : X) :
    coeff (FreeMonoid.ofFn u * FreeMonoid.of x) (A.pre (k + 1) j) =
      ∑ i, coeff (FreeMonoid.ofFn u) (A.pre k i) * A.weight k x i j := by
  simp only [pre_succ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_mul_mul_of_isHomogeneous, coeff_of_edge]
  rw [FreeMonoid.length_ofFn]
  exact A.isHomogeneous_pre k i

/-- **Factorization through a layer** ([Saptharishi2026Survey], Subclaim 11.3). If
`k + m = d`, then `M_k` of the computed polynomial is `G * H`, where `G` holds the coefficients of
the polynomials computed at layer `k` and `H` the coefficients of the polynomials computed from
layer `k` to the sink. -/
theorem nisanMatrix_eq_mul (k m : ℕ) (h : k + m = d) :
    nisanMatrix k m A.polynomial =
      Matrix.of (fun (u : Fin k → X) (l : Fin (A.width k)) =>
          coeff (FreeMonoid.ofFn u) (A.pre k l)) *
        Matrix.of fun (l : Fin (A.width k)) (v : Fin m → X) =>
          coeff (FreeMonoid.ofFn v) (A.suf k m l) := by
  ext u v
  rw [nisanMatrix_apply, A.polynomial_eq_sum_pre_mul_suf k m h, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_mul_mul_of_isHomogeneous, Matrix.of_apply, Matrix.of_apply]
  rw [FreeMonoid.length_ofFn]
  exact A.isHomogeneous_pre k l

end NoncommABP

section Rank

variable {K : Type*} [Field K] {X : Type*} [Fintype X] {d : ℕ} (A : NoncommABP K X d)

/-- **Nisan's width bound** ([Nisan1991NonCommutative], proof of Theorem 1;
[Saptharishi2026Survey], proof of Theorem 11.2). Layer `k` of an ABP computing `f` has at least
`rank M_k(f)` vertices. -/
theorem NoncommABP.rank_nisanMatrix_le_width (k m : ℕ) (h : k + m = d) :
    (nisanMatrix k m A.polynomial).rank ≤ A.width k := by
  rw [A.nisanMatrix_eq_mul k m h]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (Fintype.card_fin _).le)

/-- **Nisan's size bound** ([Nisan1991NonCommutative], Theorem 1, lower bound;
[Saptharishi2026Survey], Theorem 11.2). An ABP computing `f` has size at least
`∑_{k ≤ d} rank M_k(f)`. The sum includes the sink layer `k = d`, as in Nisan's Theorem 1; the
survey's displayed statement leaves out this term. -/
theorem NoncommABP.sum_rank_nisanMatrix_le_size :
    ∑ k ∈ Finset.range (d + 1), (nisanMatrix k (d - k) A.polynomial).rank ≤ A.size :=
  Finset.sum_le_sum fun k hk =>
    A.rank_nisanMatrix_le_width k (d - k) (by have := Finset.mem_range.mp hk; omega)

end Rank

end Cslib.Circuits.Arithmetic
