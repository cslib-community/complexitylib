/-
Copyright (c) 2026 Paul Cadman, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.VP
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Complexity.Computability.Circuit.Bird
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# The determinant is in VP

The *generic matrix* `genericMatrix K n` is the `n × n` matrix whose entries are the `n * n`
variables, in row-major order, and the determinant family `detFamily K` consists of its
determinants. Over every commutative ring `K` the determinant family is in `VP K`
[Valiant1979Algebra]: `exists_circuit_det` gives, for every `n`, an arithmetic circuit with at most
`3 * n ^ 4 + 4` gates computing the generic determinant as a formal polynomial.

The circuit runs Bird's division-free algorithm [Bird2011], whose correctness is Mathlib's
`BirdDet` development; `Cslib.Circuits.Rational.DeterminantAlgorithm` executes the same
algorithm on integer matrices. Bird's algorithm, like Berkowitz's [Berkowitz1984], uses only
additions, multiplications and integer constants, so no field or characteristic hypothesis is
needed. It runs `n - 1` stages. Each stage multiplies the previous matrix, with its diagonal
replaced by negated suffix sums and its lower triangle cleared, by the input matrix; each of its
`n ^ 2` entries costs at most `3 * n + 3` gates. Common subexpressions are not shared across
entries, which a sharper count would exploit. Only the gate count is certified; the circuits are
obtained from a synthesis bound, not constructed by a certified uniform procedure.

The permanent family `permFamily K` of generic permanents is also a p-family
(`isPFamily_permFamily`). Nothing here places it in `VP` or proves Valiant's `VNP`-completeness of
the permanent.

## Main definitions

* `Cslib.Circuits.Arithmetic.genericMatrix`: the matrix of variables.
* `Cslib.Circuits.Arithmetic.detFamily`: the family of generic determinants.
* `Cslib.Circuits.Arithmetic.permFamily`: the family of generic permanents.

## Main results

* `Cslib.Circuits.Arithmetic.det_eq_birdDetSpec`: Bird's algorithm computes the determinant over
  every commutative ring.
* `Cslib.Circuits.Arithmetic.totalDegree_det_genericMatrix_le`: the generic determinant has degree
  at most `n`.
* `Cslib.Circuits.Arithmetic.exists_circuit_det`: a circuit with at most `3 * n ^ 4 + 4` gates;
  `exists_circuit_det_eval`: the same circuit evaluates the determinant over every commutative
  `K`-algebra.
* `Cslib.Circuits.Arithmetic.detFamily_mem_VP`: the determinant family is in `VP`.
* `Cslib.Circuits.Arithmetic.isPFamily_permFamily`: the permanent family is a p-family.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [R. S. Bird, *A simple division-free algorithm for computing determinants*][Bird2011]
* [S. J. Berkowitz, *On computing the determinant in small parallel time using a small number of
  processors*][Berkowitz1984]
* The shared bridges in `Complexity/Computability/Circuit/Bird.lean` restate Paul Cadman's
  private Mathlib correctness proofs, preserving the earlier integer and generic-ring source
  credit there.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

/-! ### Bird's algorithm over a commutative ring -/

section Bird

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Bird's algorithm in matrix form computes the determinant over every commutative ring
[Bird2011]. The shared bridge restates Mathlib's private matrix-specification theorem. -/
theorem det_eq_birdDetSpec (A : Matrix (Fin n) (Fin n) R) : A.det = BirdDet.Spec.birdDet A :=
  (Bird.spec_eq_det A).symm

end Bird

/-! ### The generic matrix and the determinant family -/

/-- The generic `n × n` matrix over `K`: entry `(i, j)` is the variable `n * i + j` of
`MvPolynomial (Fin (n * n)) K`. -/
noncomputable def genericMatrix (K : Type u) [CommSemiring K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n * n)) K) :=
  Matrix.of fun i j => X (finProdFinEquiv (i, j))

/-- The determinant family over `K`: its `n`-th member is the determinant of the generic
`n × n` matrix, a polynomial in `n * n` variables. -/
noncomputable def detFamily (K : Type u) [CommRing K] : PolynomialFamily K where
  vars n := n * n
  poly n := (genericMatrix K n).det

variable {K : Type u} [CommRing K]

/-- The generic determinant has total degree at most `n`. -/
theorem totalDegree_det_genericMatrix_le (n : ℕ) : (genericMatrix K n).det.totalDegree ≤ n := by
  rw [Matrix.det_apply']
  refine totalDegree_finsetSum_le fun σ _ => (totalDegree_mul _ _).trans ?_
  rw [← map_intCast (C : K →+* MvPolynomial (Fin (n * n)) K), totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-! ### The permanent family -/

/-- The permanent family over `K`: its `n`-th member is the permanent of the generic `n × n`
matrix, a polynomial in `n * n` variables. -/
noncomputable def permFamily (K : Type u) [CommSemiring K] : PolynomialFamily K where
  vars n := n * n
  poly n := (genericMatrix K n).permanent

/-- The generic permanent has total degree at most `n`. -/
theorem totalDegree_permanent_genericMatrix_le (n : ℕ) :
    (genericMatrix K n).permanent.totalDegree ≤ n := by
  rw [Matrix.permanent]
  refine totalDegree_finsetSum_le fun σ _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-- The permanent family over `K` is a p-family (`vars n = n ^ 2` and `totalDegree ≤ n`). -/
theorem isPFamily_permFamily : (permFamily K).IsPFamily :=
  ⟨PolynomiallyBounded.id.mul PolynomiallyBounded.id,
    PolynomiallyBounded.id.mono_of_le (totalDegree_permanent_genericMatrix_le (K := K))⟩

/-! ### Bird's algorithm as an arithmetic circuit -/

section Synthesis

variable {n : ℕ}

/-- The matrix whose entries are the coordinates of a point, in row-major order. -/
private abbrev entries (x : Fin (n * n) → MvPolynomial (Fin (n * n)) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n * n)) K) :=
  Matrix.of fun i j => x (finProdFinEquiv (i, j))

/-- Stage `t` of Bird's algorithm on the matrix of a point. -/
private noncomputable abbrev stage (t : ℕ) (x : Fin (n * n) → MvPolynomial (Fin (n * n)) K) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n * n)) K) :=
  (BirdDet.Spec.stepEntry (entries x))^[t] (entries x)

/-- The entries of stage `t`, as functions of the point. -/
private noncomputable abbrev stageSet (K : Type u) [CommRing K] (n t : ℕ) :
    Set ((Fin (n * n) → MvPolynomial (Fin (n * n)) K) → MvPolynomial (Fin (n * n)) K) :=
  Set.range fun p : Fin n × Fin n => fun x => stage t x p.1 p.2

/-- The constants zero and minus one. -/
private noncomputable abbrev constants (K : Type u) [CommRing K] (n : ℕ) :
    Set ((Fin (n * n) → MvPolynomial (Fin (n * n)) K) → MvPolynomial (Fin (n * n)) K) :=
  {fun _ => 0, fun _ => -1}

/-- The interpretation of arithmetic circuits in polynomials over `K`. -/
private noncomputable abbrev interp (K : Type u) [CommRing K] (n : ℕ) :=
  arithInterpretationWith K (C : K → MvPolynomial (Fin (n * n)) K)

private theorem synthesis_const (a : K)
    {s : Set ((Fin (n * n) → MvPolynomial (Fin (n * n)) K) → MvPolynomial (Fin (n * n)) K)} :
    Synthesis (interp K n) s {fun _ => C a} 1 :=
  Synthesis.arith_const a

/-- One stage of Bird's algorithm costs at most `3 * n + 3` gates per entry. -/
private theorem synthesis_stage_succ (t : ℕ) :
    Synthesis (interp K n) (inputs (n * n) ∪ (constants K n ∪ stageSet K n t))
      (stageSet K n (t + 1)) (n * n * (3 * n + 3)) := by
  set s := inputs (n * n) ∪ (constants K n ∪ stageSet K n t)
  have hA (i j : Fin n) : (fun x => entries x i j) ∈ s := Or.inl ⟨finProdFinEquiv (i, j), rfl⟩
  have hF (i j : Fin n) : (fun x => stage t x i j) ∈ s := Or.inr (Or.inr ⟨(i, j), rfl⟩)
  have h0 : (fun _ => 0) ∈ s := Or.inr (Or.inl (Or.inl rfl))
  have hm1 : (fun _ => -1) ∈ s := Or.inr (Or.inl (Or.inr rfl))
  have hentry (p : Fin n × Fin n) :
      Synthesis (interp K n) s {fun x => stage (t + 1) x p.1 p.2} (3 * n + 3) := by
    obtain ⟨i, j⟩ := p
    have hD := Synthesis.arith_sum (constant := C) (Finset.Ioi i) (fun k x => stage t x k k)
      (fun _ => 0) h0 fun k _ => Synthesis.of_mem (hF k k)
    have hnegD := Synthesis.combine (Synthesis.of_mem (I := interp K n) hm1) hD
      (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    have hP := Synthesis.combine hnegD (Synthesis.of_mem (I := interp K n) (hA i j))
      (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    have hT := Synthesis.arith_sum (constant := C) (Finset.Ioi i)
      (fun k x => stage t x i k * entries x k j) (fun _ => 1) h0
      fun k _ => Synthesis.arith_mul (hF i k) (hA k j)
    have hE := Synthesis.combine hP hT
      (Synthesis.arith_add (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    refine hE.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr (funext fun x => ?_)) ?_
    · simp only [Function.iterate_succ_apply', BirdDet.Spec.stepEntry_eq, Matrix.of_apply]
      ring
    · have hcard : (Finset.Ioi i).card ≤ n := (Finset.card_le_univ _).trans (by simp)
      simp only [Finset.sum_const, smul_eq_mul]
      lia
  have := Synthesis.family _ _ hentry
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    smul_eq_mul] using this

/-- The first `t` stages of Bird's algorithm, with the constants zero and minus one. -/
private theorem synthesis_stages (t : ℕ) :
    Synthesis (interp K n) (inputs (n * n)) (constants K n ∪ stageSet K n t)
      (2 + t * (n * n * (3 * n + 3))) := by
  induction t with
  | zero =>
    have h0 : Synthesis (interp K n) (inputs (n * n)) {fun _ => 0} 1 := by
      simpa only [map_zero] using synthesis_const (n := n) (0 : K)
    have hm1 : Synthesis (interp K n) (inputs (n * n)) {fun _ => -1} 1 := by
      simpa only [map_neg, map_one] using synthesis_const (n := n) (-1 : K)
    have hA : Synthesis (interp K n) (inputs (n * n)) (stageSet K n 0) 0 :=
      Synthesis.of_subset (by rintro _ ⟨⟨i, j⟩, rfl⟩; exact ⟨finProdFinEquiv (i, j), rfl⟩)
    exact ((h0.union hm1).union hA).mono Set.Subset.rfl
      (by rw [constants, Set.insert_eq]) (by simp)
  | succ t ih =>
    refine (ih.comp (synthesis_stage_succ t)).mono Set.Subset.rfl
      (Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right)
      (le_of_eq (by ring))

/-- Bird's algorithm synthesizes the determinant with at most `3 * n ^ 4 + 4` gates. -/
private theorem synthesis_det (n : ℕ) :
    Synthesis (interp K n) (inputs (n * n)) {fun x => (entries x).det} (3 * n ^ 4 + 4) := by
  cases n with
  | zero =>
    refine (synthesis_const (n := 0) (1 : K)).mono Set.Subset.rfl
      (Set.singleton_subset_iff.mpr (funext fun x => ?_)) (by simp)
    simp
  | succ k =>
    have hlast : Synthesis (interp K (k + 1))
        (inputs ((k + 1) * (k + 1)) ∪ (constants K (k + 1) ∪ stageSet K (k + 1) k))
        {fun x => C ((-1) ^ k) * stage k x 0 0} 2 :=
      Synthesis.combine (synthesis_const _) (Synthesis.of_mem (Or.inr (Or.inr ⟨(0, 0), rfl⟩)))
        (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))
    refine ((synthesis_stages k).trans hlast).mono Set.Subset.rfl
      (Set.singleton_subset_iff.mpr (funext fun x => ?_)) ?_
    · rw [det_eq_birdDetSpec, BirdDet.Spec.birdDetSpec_succ]
      simp
    · have : k * (k + 2) ≤ (k + 1) ^ 2 := by nlinarith
      nlinarith

/-- **The determinant has small circuits** [Bird2011]: the generic `n × n` determinant is computed
by an arithmetic circuit with at most `3 * n ^ 4 + 4` gates, over every commutative ring `K`. -/
theorem exists_circuit_det (n : ℕ) : ∃ c : Circuit (arithSignature K) (n * n) 1,
    c.polynomial 0 = (genericMatrix K n).det ∧ c.size ≤ 3 * n ^ 4 + 4 :=
  (synthesis_det n).exists_circuit_polynomial

end Synthesis

/-- The circuits of `exists_circuit_det` are universal: the same circuit evaluates the determinant
of every `n × n` matrix over every commutative `K`-algebra, its entries supplied in row-major
order. -/
theorem exists_circuit_det_eval (n : ℕ) : ∃ c : Circuit (arithSignature K) (n * n) 1,
    c.size ≤ 3 * n ^ 4 + 4 ∧ ∀ {R : Type*} [CommRing R] [Algebra K R]
      (A : Matrix (Fin n) (Fin n) R),
      c.eval (arithInterpretationWith K (algebraMap K R))
        (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) 0 = A.det := by
  obtain ⟨c, hc, hsize⟩ := exists_circuit_det (K := K) n
  refine ⟨c, hsize, fun A => ?_⟩
  rw [← c.aeval_polynomial, hc, AlgHom.map_det]
  congr 1
  ext i j
  simp only [genericMatrix, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X,
    Equiv.symm_apply_apply]

/-- **The determinant is in VP** [Valiant1979Algebra]: over every commutative ring, the family of
generic determinants has `n * n` variables, degree at most `n` and arithmetic circuits with at most
`3 * n ^ 4 + 4` gates. -/
theorem detFamily_mem_VP : detFamily K ∈ VP K := by
  choose c hc hsize using exists_circuit_det (K := K)
  refine ⟨⟨by fun_prop, PolynomiallyBounded.id.mono_of_le fun n =>
    totalDegree_det_genericMatrix_le n⟩, c, PolynomiallyBounded.mono_of_le (by fun_prop) hsize, hc⟩

end Cslib.Circuits.Arithmetic
