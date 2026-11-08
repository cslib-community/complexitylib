/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# `L^p` norms on finite types

The *`L^p` norm* of a real function `f` on a finite type `α`, for the uniform distribution,
is `‖f‖_p = (𝔼_x |f x| ^ p) ^ (1 / p)` (`Cslib.lpNorm`) [O'Donnell, Section 1.3][ODonnell2014].
Its `p`-th power is the `p`-th absolute moment (`Cslib.lpNorm_rpow`), `‖f‖_2` is the square root
of the second moment (`Cslib.lpNorm_two`), and `‖f‖_1` is the mean absolute value
(`Cslib.lpNorm_one`). See `Complexity.Foundations.Analysis.LpNormMeasure` for its agreement with
Mathlib's `MeasureTheory.lpNorm`.

The norm is invariant under equivalences (`Cslib.lpNorm_equiv`), on a product `α × β` it is the
iterated norm (`Cslib.lpNorm_prod`), and on a subsingleton type it is the absolute value
(`Cslib.lpNorm_subsingleton`).

## Main definitions

* `Cslib.lpNorm`: the `L^p` norm `‖f‖_p` of a real function on a finite type.

## Main results

* `Cslib.lpNorm_rpow`, `Cslib.lpNorm_two`, `Cslib.lpNorm_two_sq`, `Cslib.lpNorm_one`: the `p`-th
  power of `‖f‖_p` is the `p`-th absolute moment, `‖f‖_2` is the root mean square, and `‖f‖_1` is
  the mean absolute value.
* `Cslib.lpNorm_equiv`, `Cslib.lpNorm_prod`, `Cslib.lpNorm_subsingleton`: invariance under
  equivalence, iterated norm on a product, and value on a subsingleton type.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib

open Finset
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The **`L^p` norm** `‖f‖_p = (𝔼_x |f x| ^ p) ^ (1 / p)` of a real function on a finite type, for
the uniform distribution. -/
noncomputable def lpNorm (p : ℝ) (f : α → ℝ) : ℝ :=
  (𝔼 x, |f x| ^ p) ^ p⁻¹

/-- The `p`-th absolute moment is nonnegative. -/
theorem expect_abs_rpow_nonneg (p : ℝ) (f : α → ℝ) : 0 ≤ 𝔼 x, |f x| ^ p :=
  expect_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) p

/-- The `L^p` norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (f : α → ℝ) : 0 ≤ lpNorm p f :=
  Real.rpow_nonneg (expect_abs_rpow_nonneg p f) _

/-- The `p`-th power of `‖f‖_p` is the `p`-th absolute moment. -/
theorem lpNorm_rpow {p : ℝ} (hp : p ≠ 0) (f : α → ℝ) :
    lpNorm p f ^ p = 𝔼 x, |f x| ^ p :=
  Real.rpow_inv_rpow (expect_abs_rpow_nonneg p f) hp

/-- `‖f‖_2` is the root mean square of `f`. -/
theorem lpNorm_two (f : α → ℝ) : lpNorm 2 f = √(𝔼 x, f x ^ 2) := by
  have h (x : α) : |f x| ^ (2 : ℝ) = f x ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  simp only [lpNorm, h, Real.sqrt_eq_rpow, one_div]

/-- The square of `‖f‖_2` is the second moment of `f`. -/
theorem lpNorm_two_sq (f : α → ℝ) : lpNorm 2 f ^ 2 = 𝔼 x, f x ^ 2 := by
  rw [lpNorm_two, Real.sq_sqrt (expect_nonneg fun _ _ => sq_nonneg _)]

/-- `‖f‖_1` is the mean absolute value of `f`. -/
theorem lpNorm_one (f : α → ℝ) : lpNorm 1 f = 𝔼 x, |f x| := by
  simp only [lpNorm, Real.rpow_one, inv_one]

/-! ### Equivalences, products, and subsingletons -/

/-- An equivalence of finite domains preserves the `L^p` norm. -/
theorem lpNorm_equiv (e : α ≃ β) (p : ℝ) (f : β → ℝ) :
    lpNorm p (f ∘ e) = lpNorm p f := by
  rw [lpNorm, Fintype.expect_equiv e (fun x => |(f ∘ e) x| ^ p) (fun y => |f y| ^ p) fun _ => rfl,
    lpNorm]

/-- **The `L^p` norm on a product is the iterated norm**: the norm over `α` of the norms over
`β`. -/
theorem lpNorm_prod (p : ℝ) (f : α × β → ℝ) :
    lpNorm p f = lpNorm p fun a => lpNorm p fun b => f (a, b) := by
  by_cases hp : p = 0
  · simp [lpNorm, hp]
  · rw [lpNorm, Fintype.expect_prod_type, lpNorm]
    congr 1
    refine expect_congr rfl fun a _ => ?_
    rw [abs_of_nonneg (lpNorm_nonneg _ _), lpNorm_rpow hp]

/-- On a type with at most one element, the `L^p` norm at a point is the absolute value. -/
theorem lpNorm_subsingleton [Subsingleton α] {p : ℝ} (hp : p ≠ 0) (f : α → ℝ) (x : α) :
    lpNorm p f = |f x| := by
  have : Nonempty α := ⟨x⟩
  have h : (fun y : α => |f y| ^ p) = fun _ => |f x| ^ p :=
    funext fun y => by rw [Subsingleton.elim y x]
  rw [lpNorm, h, Fintype.expect_const, Real.rpow_rpow_inv (abs_nonneg _) hp]

end Cslib
