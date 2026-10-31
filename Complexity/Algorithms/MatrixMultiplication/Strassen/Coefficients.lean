/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Strassen.Defs
public import Complexity.Foundations.Data.Nat.Morton

/-!
# Morton coefficient blocks for the existing cyclic integer ring

This is a mathematical readback specification, not an algorithm input. It relates actual
contiguous coefficient quarters to the existing quotient-ring matrices. The coefficient
ring and native signed encoding are unchanged. The quadrant argument adapts the matrix
layout part of pinned Spec/Sec3/Theorem17/Strassen.lean at revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5, using functions instead of list padding.
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Strassen

open Cslib.CyclicIntRing

/-- Flatten a cyclic-ring matrix into contiguous coefficient blocks in Morton order. -/
@[expose] noncomputable def coefficients {p : ℕ} (hp : p ≠ 0)
    (M : ℕ → ℕ → CyclicIntRing p) (i : ℕ) : ℤ :=
  coeff hp (i % p) (M (Nat.Morton.row (i / p)) (Nat.Morton.column (i / p)))

/-- Ring addition becomes pointwise signed coefficient addition. -/
theorem coefficients_add {p : ℕ} (hp : p ≠ 0) (M N : ℕ → ℕ → CyclicIntRing p) :
    coefficients hp (M + N) = coefficients hp M + coefficients hp N := by
  funext i
  simp only [coefficients, Pi.add_apply, map_add]

/-- Ring subtraction becomes pointwise signed coefficient subtraction. -/
theorem coefficients_sub {p : ℕ} (hp : p ≠ 0) (M N : ℕ → ℕ → CyclicIntRing p) :
    coefficients hp (M - N) = coefficients hp M - coefficients hp N := by
  funext i
  simp only [coefficients, Pi.sub_apply, map_sub]

/-- Four ring-matrix quadrants in the same order as their contiguous native arrays. -/
@[expose] def submatrix {R : Type*} (k t : ℕ) (M : ℕ → ℕ → R) : ℕ → ℕ → R :=
  fun a b => M (a + t / 2 * 2 ^ k) (b + t % 2 * 2 ^ k)

/-- The native quarter pointer selects exactly the corresponding ring-matrix quadrant. -/
theorem quarter_coefficients {p : ℕ} (hp : p ≠ 0) (k : ℕ)
    (M : ℕ → ℕ → CyclicIntRing p) {t i : ℕ} (ht : t < 4) (hi : i < 4 ^ k * p) :
    quarter (4 ^ k * p) t (coefficients hp M) i =
      coefficients hp (submatrix k t M) i := by
  have hm : t * (4 ^ k * p) + i = p * (t * 4 ^ k) + i := by ring
  have hz : i / p < 4 ^ k := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hp)).mpr hi
  have hrc := Nat.Morton.row_column_quadrant ht hz
  simp only [quarter, coefficients, hm,
    Nat.mul_add_div (Nat.pos_of_ne_zero hp), Nat.mul_add_mod]
  rw [hrc.1, hrc.2]
  rfl

/-- A side-one matrix is one actual cyclic coefficient block. -/
theorem coefficients_of_lt {p i : ℕ} (hp : p ≠ 0) (M : ℕ → ℕ → CyclicIntRing p)
    (hi : i < p) : coefficients hp M i = coeff hp i (M 0 0) := by
  simp only [coefficients, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi,
    Nat.Morton.row_zero, Nat.Morton.column_zero]

/-- An actual Morton coefficient address reads exactly the requested ring entry and degree. -/
theorem coefficients_at {p r : ℕ} (hp : p ≠ 0) (M : ℕ → ℕ → CyclicIntRing p)
    (a b : ℕ) (hr : r < p) :
    coefficients hp M (Nat.Morton.index a b * p + r) = coeff hp r (M a b) := by
  have hm : Nat.Morton.index a b * p + r = p * Nat.Morton.index a b + r := by ring
  simp only [coefficients, hm, Nat.mul_add_div (Nat.pos_of_ne_zero hp), Nat.mul_add_mod,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, Nat.add_zero,
    Nat.Morton.row_index, Nat.Morton.column_index]

end Cslib.Algorithms.MatrixMultiplication.Strassen
