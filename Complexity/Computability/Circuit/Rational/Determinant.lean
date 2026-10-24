/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.EncodingBounds
public import Complexity.Computability.Circuit.Bird
import Batteries.Data.Vector.Lemmas

/-!
# A staged division-free integer determinant

An executable determinant for integer matrices. It runs the stages of Bird's division-free
algorithm, but stores every intermediate stage as a dense table of row vectors, so that each stage
is computed from the materialized previous one. This is meant to avoid recomputation: Mathlib's
`BirdDet.birdDet` represents each stage as a function whose entries are recomputed recursively,
and `Matrix.det` is a permutation sum. No bound on the number of ring
operations is proved here; the result is proved equal to `Matrix.det`.

## Main definitions

* `Rational.DeterminantAlgorithm.Table`: a dense square integer matrix.
* `Rational.DeterminantAlgorithm.denote`, `Rational.DeterminantAlgorithm.tabulate`: conversion
  between tables and matrices.
* `Rational.DeterminantAlgorithm.determinant`: the staged determinant.

## Main results

* `Rational.DeterminantAlgorithm.determinant_eq`: the staged determinant is `Matrix.det`.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Determinant.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
* The shared bridge lemmas in `Complexity/Computability/Circuit/Bird.lean` restate lemmas private in
  Mathlib's development
  (`Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean`, Copyright (c) 2026 Paul
  Cadman, Apache 2.0).
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.DeterminantAlgorithm
open Matrix
open scoped BigOperators

/-- A dense square integer matrix stored as a vector of row vectors. -/
abbrev Table (n : ℕ) := Vector (Vector ℤ n) n

/-- Read a dense integer table as a matrix. -/
def denote {n : ℕ} (A : Table n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (A.get i).get j

/-- Materialize every entry of an integer matrix into a dense table. -/
def tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Table n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

@[simp] lemma denote_tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    denote (tabulate A) = A := by
  ext i j
  simp [denote, tabulate]

/-- One division-free Bird determinant stage on stored tables. -/
def step {n : ℕ} (A F : Table n) : Table n :=
  tabulate (BirdDet.Spec.stepEntry (denote A) (denote F))

/-- Iterate the division-free determinant stage. -/
def stages {n : ℕ} (A : Table n) : ℕ → Table n
  | 0 => A
  | k + 1 => step A (stages A k)

private lemma stages_spec {n : ℕ} (A : Table n) (k : ℕ) :
    denote (stages A k) = (BirdDet.Spec.stepEntry (denote A))^[k] (denote A) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [stages, step, denote_tabulate, Function.iterate_succ_apply', ih]

/-- Compute the determinant from the final Bird stage, including dimension zero. -/
def determinant : {n : ℕ} → Table n → ℤ
  | 0, _ => 1
  | k + 1, A => (-1 : ℤ) ^ k * denote (stages A k) 0 0

/-! ### Compatibility bridges

The public integer-specialized interfaces are retained. Their proofs use the shared
commutative-ring bridges in `Complexity/Computability/Circuit/Bird.lean`. -/

lemma sumFrom_eq_sum_Ico {n lo : ℕ} (f : ℕ → ℤ) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k :=
  Bird.sumFrom_eq_sum_Ico f

lemma sumFrom_fin_tail {n : ℕ} (i : Fin n) (f : ℕ → ℤ) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val :=
  Bird.sumFrom_fin_tail i f

lemma iterate_array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j :=
  Bird.iterate_array_spec A hA t i j

lemma array_spec {n : ℕ} (A : Array ℤ) (hA : A.size = n * n) :
    BirdDet.birdDet n A = BirdDet.Spec.birdDet (.ofArray A hA) :=
  Bird.array_spec A hA

lemma spec_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    BirdDet.Spec.birdDet A = A.det :=
  Bird.spec_eq_det A

/-- A genuine executable determinant, not `Matrix.det`'s permutation sum. -/
theorem determinant_eq {n : ℕ} (A : Table n) : determinant A = (denote A).det := by
  rw [← spec_eq_det]
  cases n with
  | zero => simp only [determinant, BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp only [determinant, stages_spec, BirdDet.Spec.birdDetSpec_succ]

end Rational.DeterminantAlgorithm

end Cslib.Circuits
