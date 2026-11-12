/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.BitString.SubsetSum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

/-!
# Binary subset sums of modular matrix rows

Uniform modular matrices give two-universal hashing of one binary row, for every positive modulus.
Many independent binary rows may use the same public matrix, with a statistical-distance loss
linear in their count. No whole-matrix universality or pointwise assertion about a fixed matrix is
needed.

## Main results

* `Cslib.BitString.SubsetSum.uniform_vecMul_sub`: distinct rows give a uniform difference.
* `Cslib.BitString.SubsetSum.vecMul_collision_probability`: exact modular collision probability.
* `Cslib.BitString.SubsetSum.dist_mul_le`: the joint bound with the entire public matrix retained.
* `Cslib.BitString.SubsetSum.dist_bind_mul_le`: continuation-form shared-matrix bound.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.2]
  [GentrySahaiWaters2013]
-/

public section

namespace Cslib.BitString.SubsetSum

open Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators Matrix

variable {ι κ ρ R : Type*} [Fintype ι] [Ring R]

/-- Modular multiplication by a binary row is a subset sum of the matrix rows. -/
theorem hash_eq_vecMul (A : ι → κ → R) (r : ι → Bool) :
    hash A r = (fun i => (r i).toNat : ι → R) ᵥ* Matrix.of A := by
  ext j
  simp only [hash, Finset.sum_apply, Matrix.vecMul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  cases r i <;> simp

/-- Multiplication by a binary matrix applies the same subset-sum hash to every row. -/
theorem hashRows_eq_mul (A : ι → κ → R) (r : ρ → ι → Bool) :
    hashRows A r = (Matrix.of r).map (fun bit => (bit.toNat : R)) * Matrix.of A := by
  funext i
  exact hash_eq_vecMul A (r i)

open Classical in
private theorem uniform_matrix_eq_map {a b V : Type*} [Fintype a] [Fintype b] [Fintype V]
    [DecidableEq a] [DecidableEq b]
    [Inhabited V] : PMF.uniformOfFintype (Matrix a b V) =
      (PMF.uniformOfFintype (a → b → V)).map Matrix.of :=
  (PMF.uniformOfFintype_map_equiv Matrix.of).symm

open Classical in
/-- For distinct binary rows, their modular-product difference is uniform for any positive q. -/
theorem uniform_vecMul_sub {q m d : ℕ} [NeZero q] (x y : Fin m → Bool) (hxy : x ≠ y) :
    (PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).map
      (fun A => (fun i => ((x i).toNat : ZMod q)) ᵥ* A -
        (fun i => ((y i).toNat : ZMod q)) ᵥ* A) =
      PMF.uniformOfFintype (Fin d → ZMod q) := by
  have hA := uniform_matrix_eq_map (a := Fin m) (b := Fin d) (V := ZMod q)
  rw [hA, PMF.map_comp]
  simpa only [hash_eq_vecMul, Function.comp_def] using
    uniform_hash_sub (G := Fin d → ZMod q) x y hxy

open Classical in
/-- Binary rows collide modulo q with probability exactly `1 / q^d`, without primality. -/
theorem vecMul_collision_probability {q m d : ℕ} [NeZero q]
    (x y : Fin m → Bool) (hxy : x ≠ y) :
    (∑ A : Matrix (Fin m) (Fin d) (ZMod q),
      if (fun i => ((x i).toNat : ZMod q)) ᵥ* A =
          (fun i => ((y i).toNat : ZMod q)) ᵥ* A then
        ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))) A).toReal else 0) =
      ((q : ℝ) ^ d)⁻¹ := by
  have h := congrArg (fun p : PMF (Fin d → ZMod q) => (p 0).toReal)
    (uniform_vecMul_sub (d := d) (q := q) x y hxy)
  rw [map_apply_toReal] at h
  simpa [sub_eq_zero, eq_comm] using h

open Classical in
/-- Independent binary rows share one uniform public matrix. The comparison retains that matrix;
the replacement modular matrix is independent of it. -/
theorem dist_mul_le {q m d : ℕ} [NeZero q] {Rows : Type*} [Fintype Rows] [DecidableEq Rows] :
    dist
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin m) Bool)).map
          (fun r => (A, r.map (fun bit => (bit.toNat : ZMod q)) * A))))
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin d) (ZMod q))).map (A, ·))) ≤
      Fintype.card Rows * Real.sqrt ((q : ℝ) ^ d / (2 : ℝ) ^ m) / 2 := by
  let convert := fun p : (Fin m → Fin d → ZMod q) × (Rows → Fin d → ZMod q) =>
    (Matrix.of p.1, Matrix.of p.2)
  let real := seededHash (PMF.uniformOfFintype (Fin m → Fin d → ZMod q))
    (PMF.uniformOfFintype (Rows → Fin m → Bool)) hashRows
  let ideal := (PMF.uniformOfFintype (Fin m → Fin d → ZMod q)).bind
    (fun A => (PMF.uniformOfFintype (Rows → Fin d → ZMod q)).map (A, ·))
  have h := (dist_map_le real ideal convert).trans
    (dist_hashRows_le (ι := Fin m) (κ := Rows) (G := Fin d → ZMod q))
  rw [uniform_matrix_eq_map (a := Fin m) (b := Fin d) (V := ZMod q),
    uniform_matrix_eq_map (a := Rows) (b := Fin m) (V := Bool),
    uniform_matrix_eq_map (a := Rows) (b := Fin d) (V := ZMod q)]
  have of_matrix (M : Matrix Rows (Fin d) (ZMod q)) : Matrix.of M = M := rfl
  simpa [real, ideal, convert, seededHash, hashRows_eq_mul, of_matrix, PMF.map_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def] using h

open Classical in
/-- Leftover-hash lemma in continuation (`bind`) form: any downstream randomized computation
observing the shared uniform matrix `A` and its binary-row hash matrix `r * A` has total
variation distance at most `|Rows| * √(q^d / 2^m) / 2` from observing `A` and an independent
uniform modular matrix `U`. -/
theorem dist_bind_mul_le {q m d : ℕ} [NeZero q] {Rows γ : Type*}
    [Fintype Rows] [DecidableEq Rows] [Fintype γ]
    (cont : Matrix (Fin m) (Fin d) (ZMod q) → Matrix Rows (Fin d) (ZMod q) → PMF γ) :
    dist
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin m) Bool)).bind (fun r =>
          cont A (r.map (fun bit => (bit.toNat : ZMod q)) * A))))
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin d) (ZMod q))).bind (fun U =>
          cont A U))) ≤
      Fintype.card Rows * Real.sqrt ((q : ℝ) ^ d / (2 : ℝ) ^ m) / 2 := by
  have h1 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin m) Bool)).bind (fun r =>
          cont A (r.map (fun bit => (bit.toNat : ZMod q)) * A)))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin m) Bool)).map
          (fun r => (A, r.map (fun bit => (bit.toNat : ZMod q)) * A)))).bind
        (fun p => cont p.1 p.2) := by
    rw [PMF.bind_bind]
    congr 1 with A
    rw [PMF.bind_map]
    rfl
  have h2 :
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin d) (ZMod q))).bind (fun U =>
          cont A U))) =
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod q))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix Rows (Fin d) (ZMod q))).map (A, ·))).bind
        (fun p => cont p.1 p.2) := by
    rw [PMF.bind_bind]
    congr 1 with A
    rw [PMF.bind_map]
    rfl
  rw [h1, h2]
  exact (dist_bind_le _ _ _).trans dist_mul_le

end Cslib.BitString.SubsetSum
