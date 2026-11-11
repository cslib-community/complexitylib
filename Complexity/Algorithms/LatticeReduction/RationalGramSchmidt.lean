/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact rational Gram–Schmidt on the rows of a matrix

The LLL algorithm of [LenstraLenstraLovasz1982] computes the Gram–Schmidt vectors `b*ᵢ` and the
coefficients `μᵢⱼ` of an integer basis exactly, over `ℚ`. This file provides that computation on
the rows of a `Vector (Vector ℚ m) n` and proves that it agrees with Mathlib's real
`InnerProductSpace.gramSchmidt` after the coordinate embedding
`Cslib.Algorithms.LatticeReduction.ratToEuclidean : (Fin m → ℚ) → EuclideanSpace ℝ (Fin m)`.

`Cslib.Algorithms.LatticeReduction.gramSchmidtRowsAux bq t` orthogonalizes rows `0, …, t - 1`,
each with one pass over the earlier rows (formulas (1.2)–(1.3) of [LenstraLenstraLovasz1982]), so
`n` rows cost `O(n² m)` rational operations. The rows are data, not functions, so each `b*ⱼ` is
computed once.

## Main definitions

* `Cslib.Algorithms.LatticeReduction.ratToEuclidean`: a rational vector as a point of `ℝᵐ`.
* `Cslib.Algorithms.LatticeReduction.projCoeff`: the coefficient `⟨g, v⟩ / ⟨g, g⟩`.
* `Cslib.Algorithms.LatticeReduction.gramSchmidtRowsAux`: exact Gram–Schmidt on rows.

## Main results

* `Cslib.Algorithms.LatticeReduction.gramSchmidtRowsAux_spec`: the computed rows are the real
  Gram–Schmidt vectors.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {m n : ℕ}

/-! ### Rational vectors in Euclidean space -/

/-- A rational vector as a point of Euclidean space. -/
noncomputable def ratToEuclidean (v : Fin m → ℚ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun k => (v k : ℝ)

@[simp] theorem ratToEuclidean_apply (v : Fin m → ℚ) (k : Fin m) :
    ratToEuclidean v k = (v k : ℝ) := by
  simp only [ratToEuclidean, PiLp.toLp_apply]

theorem ratToEuclidean_sub_sum {ι : Type*} (v : Fin m → ℚ) (s : Finset ι) (c : ι → ℚ)
    (g : ι → Fin m → ℚ) :
    ratToEuclidean (fun k => v k - ∑ j ∈ s, c j * g j k) =
      ratToEuclidean v - ∑ j ∈ s, (c j : ℝ) • ratToEuclidean (g j) := by
  ext k; simp [ratToEuclidean]

theorem inner_ratToEuclidean (v w : Fin m → ℚ) :
    inner ℝ (ratToEuclidean v) (ratToEuclidean w) = ((dotProduct v w : ℚ) : ℝ) := by
  simp [ratToEuclidean, PiLp.inner_apply, dotProduct, mul_comm]

theorem norm_sq_ratToEuclidean (v : Fin m → ℚ) :
    ‖ratToEuclidean v‖ ^ 2 = ((dotProduct v v : ℚ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_ratToEuclidean]

/-- The projection coefficient `⟨g, v⟩ / ⟨g, g⟩`. -/
def projCoeff (g v : Fin m → ℚ) : ℚ :=
  dotProduct g v / dotProduct g g

theorem cast_projCoeff (g v : Fin m → ℚ) :
    (projCoeff g v : ℝ) =
      inner ℝ (ratToEuclidean g) (ratToEuclidean v) / ‖ratToEuclidean g‖ ^ 2 := by
  rw [projCoeff, Rat.cast_div, inner_ratToEuclidean, norm_sq_ratToEuclidean]

/-! ### Exact Gram–Schmidt on rows -/

/-- The rows `0, …, t - 1` of the Gram–Schmidt orthogonalization of the rows of `bq`; the other
rows are those of `bq`. Each row costs `O(n m)` rational operations. -/
def gramSchmidtRowsAux (bq : Vector (Vector ℚ m) n) : ℕ → Vector (Vector ℚ m) n
  | 0 => bq
  | t + 1 =>
    let G := gramSchmidtRowsAux bq t
    if h : t < n then
      let c : Vector ℚ n := Vector.ofFn fun j =>
        projCoeff (fun k : Fin m => G[j][k]) (fun k : Fin m => bq[t][k])
      G.set t (Vector.ofFn fun k : Fin m =>
        bq[t][k] - ∑ j ∈ Finset.Iio (⟨t, h⟩ : Fin n), c[j] * G[j][k])
    else G

theorem gramSchmidtRowsAux_spec (bq : Vector (Vector ℚ m) n) : ∀ (t : ℕ) (i : Fin n), (i : ℕ) < t →
    ratToEuclidean (fun k : Fin m => (gramSchmidtRowsAux bq t)[i][k]) =
      gramSchmidt ℝ (fun l : Fin n => ratToEuclidean fun k : Fin m => bq[l][k]) i := by
  intro t
  induction t with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ t ih =>
    intro i hi
    by_cases h : t < n
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · have hne : t ≠ (i : ℕ) := by omega
        simp only [gramSchmidtRowsAux, h, dite_true, Fin.getElem_fin, Vector.getElem_set_ne _ _ hne]
        simpa only [Fin.getElem_fin] using ih i hi
      · obtain rfl : i = ⟨t, h⟩ := Fin.ext hi
        simp only [gramSchmidtRowsAux, h, dite_true, Fin.getElem_fin, Vector.getElem_set_self,
          Vector.getElem_ofFn]
        rw [ratToEuclidean_sub_sum]
        have hdef :=
          gramSchmidt_def'' ℝ (fun l : Fin n => ratToEuclidean fun k : Fin m => bq[l][k]) ⟨t, h⟩
        simp only [Fin.getElem_fin] at hdef
        rw [eq_sub_of_add_eq hdef.symm]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : (j : ℕ) < t := Fin.lt_def.1 (Finset.mem_Iio.1 hj)
        have hj'' := ih j hj'
        simp only [Fin.getElem_fin] at hj''
        rw [cast_projCoeff, hj'']
        simp
    · simp only [gramSchmidtRowsAux, h, dite_false]
      exact ih i (by omega)

end Cslib.Algorithms.LatticeReduction
