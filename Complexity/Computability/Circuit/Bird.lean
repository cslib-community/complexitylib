/-
Copyright (c) 2026 Paul Cadman, OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman, OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Array
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-!
# Shared correctness bridges for Bird's determinant algorithm

These commutative-ring bridges connect the flat-array implementation and the matrix specification
of Bird's division-free algorithm. They form a lightweight shared dependency of the integer
staged algorithm and the arithmetic-circuit synthesis, without importing either client hierarchy.
No algorithm or resource bound is introduced here.

## Main results

* `Cslib.Circuits.Bird.sumFrom_eq_sum_Ico`, `Cslib.Circuits.Bird.sumFrom_fin_tail`: suffix sums.
* `Cslib.Circuits.Bird.iterate_array_spec`, `Cslib.Circuits.Bird.array_spec`: array/matrix bridges.
* `Cslib.Circuits.Bird.spec_eq_det`: the matrix specification computes the determinant.

## References

* [R. S. Bird, *A simple division-free algorithm for computing determinants*][Bird2011].
* The proofs restate private declarations from Paul Cadman's Mathlib module
  `Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean` (Copyright 2026, Apache 2.0).
  They consolidate the local generic-ring and integer restatements previously in
  `Complexity/Computability/Circuit/Arithmetic/Determinant.lean` and
  `Complexity/Computability/Circuit/Rational/Determinant.lean`.
* The integer restatement came from OpenAI's formalization [OpenAI2026RationalHitting], revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a, via the complexitylib port
  [Schlesinger2026RationalHitting], revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Bird

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The recursive suffix sum is the sum over a natural-number interval. -/
theorem sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih =>
    rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

/-- A suffix starting after a finite index is the sum over its strict upper interval. -/
theorem sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [sumFrom_eq_sum_Ico]
  calc _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by
         congr
         ext
         simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
         lia
       _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
       _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
       _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- Iterated flat-array stages agree with iterated matrix stages. -/
theorem iterate_array_spec (A : Array R) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [Function.iterate_succ_apply', BirdDet.stepEntry_eq, BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail, ih, Matrix.of_apply, BirdDet.get_eq]

/-- The flat-array determinant agrees with the matrix specification, including dimension zero. -/
theorem array_spec (A : Array R) (hA : A.size = n * n) :
    BirdDet.birdDet n A = BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero, BirdDet.Spec.birdDetSpec_zero]
  | succ k =>
    simp [BirdDet.birdDet_succ, BirdDet.Spec.birdDetSpec_succ, ← iterate_array_spec A hA k]

/-- Bird's matrix specification computes the determinant over every commutative ring. -/
theorem spec_eq_det (A : Matrix (Fin n) (Fin n) R) : BirdDet.Spec.birdDet A = A.det := by
  let a := Array.ofFn fun k : Fin (n * n) => A k.divNat k.modNat
  have ha : a.size = n * n := Array.size_ofFn
  have he : Matrix.ofArray a ha = A := Matrix.ofArray_ofFn A
  rw [← he, ← array_spec a ha, ← BirdDet.det_eq_birdDet a ha]

end Cslib.Circuits.Bird
