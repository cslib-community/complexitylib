/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Simplex dictionaries and pivoting

This module sets up the dictionaries of the simplex method ([Chvatal1983], Chapters 2 and 3) over
an arbitrary field, with the order-dependent statements over a linearly ordered field (`ℚ`, `ℝ`,
…), and proves that pivoting preserves the solution set, the objective, and feasibility, together
with the two stopping certificates: optimality and unboundedness.

## Model

The variables are indexed by a finite linearly ordered type `ι`. A `Dictionary ι K` consists of a
set `basis` of basic variables, and for each basic `i` a row expressing it through the nonbasic
variables, `x i = rhs i + ∑ j ∉ basis, coeff i j * x j`, together with an objective row
`objConst + ∑ j ∉ basis, objCoeff j * x j`. Entries of `rhs`, `coeff` and `objCoeff` outside these
index ranges are ignored. `IsSolution D x` says that `x : ι → K` satisfies every row (no sign
condition), and `D.value x` is the objective at `x`. The linear program described by `D` is to
maximize `D.value x` over `D.feasibleSet = {x | D.IsSolution x ∧ 0 ≤ x}`. Two dictionaries are
`Equivalent` when they have the same solutions and agree on the objective there.

The basic solution `D.basicSolution` sets the nonbasic variables to `0`; `D` is `Feasible` when
it is nonnegative, that is `0 ≤ rhs i` for every basic `i`.

## Source mapping

[Chvatal1983], Chapter 2, writes a dictionary as `x_i = b_i - ∑ a_ij x_j`, `z = v + ∑ c_j x_j`;
here the sign of the coefficients is absorbed into `coeff`, so `coeff i j = -a_ij`. Pivoting
on a basic `r` (leaving) and a nonbasic `s` (entering) with `coeff r s ≠ 0` solves row `r` for
`x s` and substitutes into the other rows and the objective (`pivot`); `pivot` sets the entries
outside the new index ranges to `0`. The entering variable increases along the edge
`D.basicSolution + t • D.ray s`; the ratio test bounds `t` by `D.ratio s r = rhs r / -coeff r s`
for the rows with `coeff r s < 0`.

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.Dictionary`: a simplex dictionary.
* `Dictionary.IsSolution`, `Dictionary.value`, `Dictionary.feasibleSet`: the linear program it
  describes; `Dictionary.Equivalent`: equivalence of dictionaries.
* `Dictionary.basicSolution`, `Dictionary.Feasible`: the basic solution and feasibility.
* `Dictionary.pivot`, `Dictionary.ray`, `Dictionary.ratio`: pivoting, the edge direction of an
  entering variable and the ratio test.

## Main results

* `Dictionary.equivalent_pivot`: a pivot on a nonzero coefficient yields an equivalent dictionary.
* `Dictionary.basicSolution_pivot`, `Dictionary.objConst_pivot`: the pivot moves the basic
  solution along the edge of the entering variable by the ratio of the leaving row.
* `Dictionary.feasible_pivot`, `Dictionary.objConst_le_pivot`: under the ratio test the pivot
  preserves feasibility, and with a nonnegative reduced cost it does not decrease the objective.
* `Dictionary.isGreatest_value`: if no reduced cost is positive, the basic solution of a feasible
  dictionary is optimal.
* `Dictionary.not_bddAbove_value`: if an entering variable has no leaving row, the objective is
  unbounded on the feasible set.

## References

* [V. Chvátal, *Linear Programming*][Chvatal1983]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

/-- A **simplex dictionary** ([Chvatal1983], Chapter 2) on the variables `ι`: each basic variable
`i ∈ basis` is expressed as `x i = rhs i + ∑ j ∉ basis, coeff i j * x j`, and the objective as
`objConst + ∑ j ∉ basis, objCoeff j * x j`. Entries outside these index ranges are ignored. -/
structure Dictionary (ι K : Type*) where
  /-- The basic variables. -/
  basis : Finset ι
  /-- The constant term of the row of each basic variable. -/
  rhs : ι → K
  /-- `coeff i j` is the coefficient of the nonbasic `x j` in the row of the basic `x i`. -/
  coeff : ι → ι → K
  /-- The constant term of the objective row: the objective value of the basic solution. -/
  objConst : K
  /-- The reduced costs: `objCoeff j` is the coefficient of the nonbasic `x j` in the
  objective row. -/
  objCoeff : ι → K

namespace Dictionary

open Finset

variable {ι K : Type*}

section Field

variable [Field K]

/-- `x` satisfies every row of `D`. No sign condition is imposed. -/
@[expose] def IsSolution [Fintype ι] [DecidableEq ι] (D : Dictionary ι K) (x : ι → K) : Prop :=
  ∀ i ∈ D.basis, x i = D.rhs i + ∑ j ∈ D.basisᶜ, D.coeff i j * x j

/-- The objective of `D` at `x`. -/
@[expose] def value [Fintype ι] [DecidableEq ι] (D : Dictionary ι K) (x : ι → K) : K :=
  D.objConst + ∑ j ∈ D.basisᶜ, D.objCoeff j * x j

/-- The basic solution of `D`: the nonbasic variables are `0`, so each basic `x i` is
`rhs i`. -/
@[expose] def basicSolution [DecidableEq ι] (D : Dictionary ι K) (i : ι) : K :=
  if i ∈ D.basis then D.rhs i else 0

/-- `D` and `D'` describe the same linear program: they have the same solutions, and their
objectives agree on them. -/
structure Equivalent [Fintype ι] [DecidableEq ι] (D D' : Dictionary ι K) : Prop where
  isSolution_iff : ∀ x, D.IsSolution x ↔ D'.IsSolution x
  value_eq : ∀ x, D.IsSolution x → D.value x = D'.value x

/-- The **pivot** of `D` on the leaving basic variable `r` and the entering nonbasic variable `s`
([Chvatal1983], Chapter 2): row `r` is solved for `x s`, which is substituted into the other rows
and into the objective. The new basis is `insert s (D.basis.erase r)`. Entries outside the new
index ranges are set to `0`. The result is meaningful when `r ∈ D.basis`, `s ∉ D.basis` and
`D.coeff r s ≠ 0`. -/
@[expose] def pivot [DecidableEq ι] (D : Dictionary ι K) (r s : ι) : Dictionary ι K where
  basis := insert s (D.basis.erase r)
  rhs i :=
    if i = s then -D.rhs r / D.coeff r s
    else if i ∈ D.basis ∧ i ≠ r then D.rhs i - D.coeff i s * D.rhs r / D.coeff r s
    else 0
  coeff i j :=
    if j = s ∨ j ∈ D.basis ∧ j ≠ r then 0
    else if i = s then (if j = r then 1 / D.coeff r s else -D.coeff r j / D.coeff r s)
    else if i ∈ D.basis ∧ i ≠ r then
      (if j = r then D.coeff i s / D.coeff r s
        else D.coeff i j - D.coeff i s * D.coeff r j / D.coeff r s)
    else 0
  objConst := D.objConst - D.objCoeff s * D.rhs r / D.coeff r s
  objCoeff j :=
    if j = s ∨ j ∈ D.basis ∧ j ≠ r then 0
    else if j = r then D.objCoeff s / D.coeff r s
    else D.objCoeff j - D.objCoeff s * D.coeff r j / D.coeff r s

/-- The edge direction of the nonbasic variable `s`: increasing `x s` by `t` while keeping the
other nonbasic variables at `0` changes each basic `x i` by `t * coeff i s`. -/
@[expose] def ray [DecidableEq ι] (D : Dictionary ι K) (s i : ι) : K :=
  if i = s then 1 else if i ∈ D.basis then D.coeff i s else 0

/-- The ratio test: when `coeff i s < 0`, row `i` stays nonnegative along the edge of `s` for
step lengths up to `rhs i / -coeff i s`. -/
@[expose] def ratio (D : Dictionary ι K) (s i : ι) : K := D.rhs i / -D.coeff i s

variable [Fintype ι] [DecidableEq ι] (D : Dictionary ι K)

namespace Equivalent

@[refl] protected theorem refl : D.Equivalent D := ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩

variable {D} {D' D'' : Dictionary ι K}

@[symm] protected theorem symm (h : D.Equivalent D') : D'.Equivalent D :=
  ⟨fun x => (h.isSolution_iff x).symm,
    fun x hx => (h.value_eq x ((h.isSolution_iff x).2 hx)).symm⟩

@[trans] protected theorem trans (h : D.Equivalent D') (h' : D'.Equivalent D'') :
    D.Equivalent D'' :=
  ⟨fun x => (h.isSolution_iff x).trans (h'.isSolution_iff x),
    fun x hx => (h.value_eq x hx).trans (h'.value_eq x ((h.isSolution_iff x).1 hx))⟩

end Equivalent

omit [Fintype ι] in
theorem basicSolution_of_mem {i : ι} (hi : i ∈ D.basis) : D.basicSolution i = D.rhs i :=
  ite_eq_left hi

omit [Fintype ι] in
theorem basicSolution_of_notMem {i : ι} (hi : i ∉ D.basis) : D.basicSolution i = 0 :=
  ite_eq_right hi

theorem isSolution_basicSolution : D.IsSolution D.basicSolution := by
  intro i hi
  rw [Finset.sum_eq_zero fun j hj => by
    rw [D.basicSolution_of_notMem (Finset.mem_compl.1 hj), mul_zero], add_zero,
    D.basicSolution_of_mem hi]

/-- A solution vanishing off the basis is the basic solution. -/
theorem eq_basicSolution_of_isSolution {x : ι → K} (hx : D.IsSolution x)
    (h0 : ∀ j ∉ D.basis, x j = 0) : x = D.basicSolution := by
  funext i
  by_cases hi : i ∈ D.basis
  · rw [hx i hi, Finset.sum_eq_zero fun j hj => by rw [h0 j (Finset.mem_compl.1 hj), mul_zero],
      add_zero, D.basicSolution_of_mem hi]
  · rw [h0 i hi, D.basicSolution_of_notMem hi]

theorem value_basicSolution : D.value D.basicSolution = D.objConst := by
  rw [value, Finset.sum_eq_zero fun j hj => by
    rw [D.basicSolution_of_notMem (Finset.mem_compl.1 hj), mul_zero], add_zero]

/-! ### Pivoting -/

omit [Fintype ι] in
theorem pivot_basis (r s : ι) : (D.pivot r s).basis = insert s (D.basis.erase r) := rfl

omit [Fintype ι] in
theorem mem_pivot_basis {r s i : ι} :
    i ∈ (D.pivot r s).basis ↔ i = s ∨ i ∈ D.basis ∧ i ≠ r := by
  rw [pivot_basis, Finset.mem_insert, Finset.mem_erase, and_comm]

omit [Fintype ι] in
theorem card_pivot_basis {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis) :
    #(D.pivot r s).basis = #D.basis := by
  rw [pivot_basis, Finset.card_insert_of_notMem fun h => hs (Finset.mem_of_mem_erase h),
    Finset.card_erase_of_mem hr, Nat.sub_add_cancel (Finset.card_pos.2 ⟨r, hr⟩)]

private theorem sum_compl_pivot {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis) (f : ι → K) :
    ∑ j ∈ (D.pivot r s).basisᶜ, f j = f r + ∑ j ∈ D.basisᶜ.erase s, f j := by
  have hrs : r ≠ s := fun h => hs (h ▸ hr)
  have : (D.pivot r s).basisᶜ = insert r (D.basisᶜ.erase s) := by
    ext j
    simp only [Finset.mem_compl, mem_pivot_basis, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro h
      by_cases hjr : j = r
      · exact .inl hjr
      · exact .inr ⟨fun hjs => h (.inl hjs), fun hj => h (.inr ⟨hj, hjr⟩)⟩
    · rintro (rfl | ⟨hjs, hj⟩) (hjs' | ⟨hj', hjr⟩)
      · exact hrs hjs'
      · exact hjr rfl
      · exact hjs hjs'
      · exact hj hj'
  rw [this, Finset.sum_insert (by simp [hr])]

private theorem sum_compl_eq_add {s : ι} (hs : s ∉ D.basis) (f : ι → K) :
    ∑ j ∈ D.basisᶜ, f j = f s + ∑ j ∈ D.basisᶜ.erase s, f j :=
  (Finset.add_sum_erase _ _ (Finset.mem_compl.2 hs)).symm

omit [Field K] in
private theorem mem_compl_erase {s j : ι} (hj : j ∈ D.basisᶜ.erase s) :
    j ≠ s ∧ j ∉ D.basis :=
  ⟨Finset.ne_of_mem_erase hj, Finset.mem_compl.1 (Finset.mem_of_mem_erase hj)⟩

/-- A pivot on a nonzero coefficient preserves the solutions. -/
theorem isSolution_pivot_iff {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis)
    (ha : D.coeff r s ≠ 0) {x : ι → K} : (D.pivot r s).IsSolution x ↔ D.IsSolution x := by
  have hrs : r ≠ s := fun h => hs (h ▸ hr)
  set R : ι → K := fun i => ∑ j ∈ D.basisᶜ.erase s, D.coeff i j * x j with hR
  -- the old row `i` with `x s` split off
  have hold : ∀ i, D.rhs i + ∑ j ∈ D.basisᶜ, D.coeff i j * x j =
      D.rhs i + D.coeff i s * x s + R i := fun i => by
    rw [D.sum_compl_eq_add hs, add_assoc]
  -- the new row `s`
  have hnew_s : (D.pivot r s).rhs s +
      ∑ j ∈ (D.pivot r s).basisᶜ, (D.pivot r s).coeff s j * x j =
      (x r - D.rhs r - R r) / D.coeff r s := by
    rw [D.sum_compl_pivot hr hs]
    have hsum : ∑ j ∈ D.basisᶜ.erase s, (D.pivot r s).coeff s j * x j =
        -(R r / D.coeff r s) := by
      simp only [hR]
      rw [Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hjs, hj⟩ := D.mem_compl_erase hj
      have hjr : j ≠ r := fun h => hj (h ▸ hr)
      simp only [pivot, hjs, hj, false_and, or_self, ite_false, ite_true, hjr]
      ring
    rw [hsum]
    simp only [pivot, ite_true, hrs, hr, false_or, ne_eq, not_true_eq_false, and_false, ite_false]
    field_simp
    ring
  -- the new row `i` for an old basic `i ≠ r`
  have hnew_i : ∀ i ∈ D.basis, i ≠ r →
      (D.pivot r s).rhs i + ∑ j ∈ (D.pivot r s).basisᶜ, (D.pivot r s).coeff i j * x j =
      D.rhs i + D.coeff i s * ((x r - D.rhs r - R r) / D.coeff r s) + R i := by
    intro i hi hir
    have his : i ≠ s := fun h => hs (h ▸ hi)
    rw [D.sum_compl_pivot hr hs]
    have hsum : ∑ j ∈ D.basisᶜ.erase s, (D.pivot r s).coeff i j * x j =
        R i - D.coeff i s * (R r / D.coeff r s) := by
      simp only [hR]
      rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain ⟨hjs, hj⟩ := D.mem_compl_erase hj
      have hjr : j ≠ r := fun h => hj (h ▸ hr)
      simp only [pivot, hjs, hj, false_and, or_self, ite_false, his, hi, hir, ne_eq,
        not_false_eq_true, and_self, ite_true, hjr]
      ring
    rw [hsum]
    simp only [pivot, his, hi, hir, ne_eq, not_false_eq_true, and_self, ite_true, ite_false,
      hrs, hr, false_or, not_true_eq_false, and_false]
    field_simp
    ring
  constructor
  · intro h i hi
    have hxs : x s = (x r - D.rhs r - R r) / D.coeff r s := by
      rw [← hnew_s]; exact h s (D.mem_pivot_basis.2 (.inl rfl))
    by_cases hir : i = r
    · subst hir
      rw [hold, hxs]
      field_simp
      ring
    · rw [hold, hxs, ← hnew_i i hi hir]
      exact h i (D.mem_pivot_basis.2 (.inr ⟨hi, hir⟩))
  · intro h i hi
    have hxr := h r hr
    rw [hold] at hxr
    have hxs : x s = (x r - D.rhs r - R r) / D.coeff r s := by
      field_simp
      linear_combination -hxr
    rcases D.mem_pivot_basis.1 hi with rfl | ⟨hi, hir⟩
    · rw [hnew_s, ← hxs]
    · rw [hnew_i i hi hir, ← hxs, ← hold]
      exact h i hi

/-- A pivot on a nonzero coefficient preserves the objective on solutions. -/
theorem value_pivot {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis) (ha : D.coeff r s ≠ 0)
    {x : ι → K} (hx : D.IsSolution x) : (D.pivot r s).value x = D.value x := by
  have hrs : r ≠ s := fun h => hs (h ▸ hr)
  set R : ι → K := fun i => ∑ j ∈ D.basisᶜ.erase s, D.coeff i j * x j with hR
  have hxr := hx r hr
  rw [D.sum_compl_eq_add hs] at hxr
  have hsum : ∑ j ∈ D.basisᶜ.erase s, (D.pivot r s).objCoeff j * x j =
      ∑ j ∈ D.basisᶜ.erase s, D.objCoeff j * x j - D.objCoeff s * (R r / D.coeff r s) := by
    simp only [hR]
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjs, hj⟩ := D.mem_compl_erase hj
    have hjr : j ≠ r := fun h => hj (h ▸ hr)
    simp only [pivot, hjs, hj, false_and, or_self, ite_false, hjr]
    ring
  rw [value, value, D.sum_compl_pivot hr hs, hsum, D.sum_compl_eq_add hs]
  simp only [pivot, hrs, hr, false_or, ne_eq, not_true_eq_false, and_false, ite_false, ite_true]
  have hxs : x s = (x r - D.rhs r - R r) / D.coeff r s := by
    rw [eq_div_iff ha]
    simp only [hR]
    linear_combination -hxr
  rw [hxs]
  field_simp
  ring

/-- **Pivoting yields an equivalent dictionary** ([Chvatal1983], Chapter 2): a pivot on a basic
`r`, a nonbasic `s` and a nonzero coefficient `D.coeff r s` preserves the solutions and the
objective. -/
theorem equivalent_pivot {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis)
    (ha : D.coeff r s ≠ 0) : D.Equivalent (D.pivot r s) :=
  ⟨fun _ => (D.isSolution_pivot_iff hr hs ha).symm,
    fun _ hx => (D.value_pivot hr hs ha hx).symm⟩

/-! ### The edge direction of an entering variable -/

private theorem sum_mul_ray {s : ι} (hs : s ∉ D.basis) (f : ι → K) :
    ∑ j ∈ D.basisᶜ, f j * D.ray s j = f s := by
  rw [Finset.sum_eq_single_of_mem s (Finset.mem_compl.2 hs) fun j hj hjs => by
    rw [ray, ite_eq_right hjs, ite_eq_right (Finset.mem_compl.1 hj), mul_zero]]
  rw [ray, ite_eq_left rfl, mul_one]

omit [Fintype ι] in
theorem ray_self (s : ι) : D.ray s s = 1 := ite_eq_left rfl

omit [Fintype ι] in
theorem ray_of_mem {s i : ι} (hi : i ∈ D.basis) (hs : s ∉ D.basis) :
    D.ray s i = D.coeff i s := by
  rw [ray, ite_eq_right (show i ≠ s from fun h => hs (h ▸ hi)), ite_eq_left hi]

omit [Fintype ι] in
theorem ray_of_notMem {s i : ι} (hi : i ∉ D.basis) (his : i ≠ s) : D.ray s i = 0 := by
  rw [ray, ite_eq_right his, ite_eq_right hi]

/-- Moving a solution along the edge of a nonbasic variable keeps it a solution. -/
theorem isSolution_add_smul_ray {s : ι} (hs : s ∉ D.basis) {x : ι → K} (hx : D.IsSolution x)
    (t : K) : D.IsSolution (x + t • D.ray s) := by
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [hx i hi, D.ray_of_mem hi hs]
  have : ∑ j ∈ D.basisᶜ, D.coeff i j * (t * D.ray s j) = t * D.coeff i s := by
    rw [← D.sum_mul_ray hs (fun j => t * D.coeff i j)]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- Along the edge of a nonbasic `s` the objective changes at rate `objCoeff s`. -/
theorem value_add_smul_ray {s : ι} (hs : s ∉ D.basis) (x : ι → K) (t : K) :
    D.value (x + t • D.ray s) = D.value x + t * D.objCoeff s := by
  simp only [value, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have : ∑ j ∈ D.basisᶜ, D.objCoeff j * (t * D.ray s j) = t * D.objCoeff s := by
    rw [← D.sum_mul_ray hs (fun j => t * D.objCoeff j)]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

omit [Fintype ι] in
/-- The pivot on `r` and `s` moves the basic solution along the edge of `s` by the ratio of
row `r`. -/
theorem basicSolution_pivot [Finite ι] {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis)
    (ha : D.coeff r s ≠ 0) :
    (D.pivot r s).basicSolution = D.basicSolution + D.ratio s r • D.ray s := by
  have := Fintype.ofFinite ι
  have hrs : r ≠ s := fun h => hs (h ▸ hr)
  refine ((D.pivot r s).eq_basicSolution_of_isSolution ((D.isSolution_pivot_iff hr hs ha).2
    (D.isSolution_add_smul_ray hs D.isSolution_basicSolution _)) fun j hj => ?_).symm
  rw [mem_pivot_basis, not_or, not_and_or, not_not] at hj
  obtain ⟨hjs, hj | rfl⟩ := hj
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D.basicSolution_of_notMem hj,
      D.ray_of_notMem hj hjs, mul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D.basicSolution_of_mem hr,
      D.ray_of_mem hr hs, ratio]
    field_simp
    ring

omit [Fintype ι] in
/-- The pivot on `r` and `s` changes the objective value of the basic solution by
`objCoeff s * ratio s r`. -/
theorem objConst_pivot (r s : ι) :
    (D.pivot r s).objConst = D.objConst + D.objCoeff s * D.ratio s r := by
  simp only [pivot, ratio, div_neg]
  ring

end Field

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `D` is **feasible** when its basic solution is nonnegative ([Chvatal1983], Chapter 2). -/
@[expose] def Feasible (D : Dictionary ι K) : Prop := ∀ i ∈ D.basis, 0 ≤ D.rhs i

/-- The feasible set of the linear program described by `D`. -/
def feasibleSet [Fintype ι] [DecidableEq ι] (D : Dictionary ι K) : Set (ι → K) :=
  {x | D.IsSolution x ∧ 0 ≤ x}

variable [Fintype ι] [DecidableEq ι] (D : Dictionary ι K)

omit [IsStrictOrderedRing K] in
theorem mem_feasibleSet {x : ι → K} : x ∈ D.feasibleSet ↔ D.IsSolution x ∧ 0 ≤ x := Iff.rfl

omit [Fintype ι] [IsStrictOrderedRing K] in
theorem feasible_iff_nonneg_basicSolution : D.Feasible ↔ 0 ≤ D.basicSolution := by
  constructor
  · intro h i
    by_cases hi : i ∈ D.basis
    · rw [D.basicSolution_of_mem hi]; exact h i hi
    · rw [D.basicSolution_of_notMem hi]; rfl
  · intro h i hi
    rw [← D.basicSolution_of_mem hi]; exact h i

omit [Fintype ι] [DecidableEq ι] in
theorem ratio_nonneg (hD : D.Feasible) {s r : ι} (hr : r ∈ D.basis) (har : D.coeff r s < 0) :
    0 ≤ D.ratio s r :=
  div_nonneg (hD r hr) (neg_nonneg.2 har.le)

omit [Fintype ι] in
/-- **The ratio test preserves feasibility** ([Chvatal1983], Chapter 2): pivoting a feasible
dictionary on a row `r` with `coeff r s < 0` of minimal ratio yields a feasible dictionary. -/
theorem feasible_pivot [Finite ι] (hD : D.Feasible) {r s : ι} (hr : r ∈ D.basis) (hs : s ∉ D.basis)
    (har : D.coeff r s < 0)
    (hmin : ∀ i ∈ D.basis, D.coeff i s < 0 → D.ratio s r ≤ D.ratio s i) :
    (D.pivot r s).Feasible := by
  rw [feasible_iff_nonneg_basicSolution, D.basicSolution_pivot hr hs har.ne]
  have hθ := D.ratio_nonneg hD hr har
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases his : i = s
  · subst his
    rw [D.basicSolution_of_notMem hs, D.ray_self, zero_add, mul_one]
    exact hθ
  by_cases hi : i ∈ D.basis
  · rw [D.basicSolution_of_mem hi, D.ray_of_mem hi hs]
    rcases lt_or_ge (D.coeff i s) 0 with hneg | hnonneg
    · have h := hmin i hi hneg
      simp only [ratio] at h ⊢
      rw [le_div_iff₀ (neg_pos.2 hneg)] at h
      linarith
    · exact add_nonneg (hD i hi) (mul_nonneg hθ hnonneg)
  · rw [D.basicSolution_of_notMem hi, D.ray_of_notMem hi his, mul_zero, add_zero]

omit [Fintype ι] in
/-- A pivot on a row `r` with `coeff r s < 0` of a feasible dictionary, entering a variable with
nonnegative reduced cost, does not decrease the objective value of the basic solution. -/
theorem objConst_le_pivot (hD : D.Feasible) {r s : ι} (hr : r ∈ D.basis)
    (har : D.coeff r s < 0) (hc : 0 ≤ D.objCoeff s) : D.objConst ≤ (D.pivot r s).objConst := by
  rw [objConst_pivot]
  exact le_add_of_nonneg_right (mul_nonneg hc (D.ratio_nonneg hD hr har))

theorem value_le_objConst (h : ∀ j ∉ D.basis, D.objCoeff j ≤ 0) {x : ι → K} (hx : 0 ≤ x) :
    D.value x ≤ D.objConst :=
  add_le_of_nonpos_right (Finset.sum_nonpos fun j hj =>
    mul_nonpos_of_nonpos_of_nonneg (h j (Finset.mem_compl.1 hj)) (hx j))

/-- **Optimality certificate** ([Chvatal1983], Chapter 2): if no reduced cost of a feasible
dictionary is positive, its basic solution is optimal, with value `objConst`. -/
theorem isGreatest_value (hD : D.Feasible) (h : ∀ j ∉ D.basis, D.objCoeff j ≤ 0) :
    IsGreatest (D.value '' D.feasibleSet) D.objConst :=
  ⟨⟨D.basicSolution, ⟨D.isSolution_basicSolution,
      (D.feasible_iff_nonneg_basicSolution).1 hD⟩, D.value_basicSolution⟩,
    by rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact D.value_le_objConst h hx⟩

omit [Fintype ι] in
theorem ray_nonneg {s : ι} (hs : s ∉ D.basis) (h : ∀ i ∈ D.basis, 0 ≤ D.coeff i s) :
    0 ≤ D.ray s := by
  intro i
  by_cases his : i = s
  · rw [his, ray_self]; exact zero_le_one
  by_cases hi : i ∈ D.basis
  · rw [D.ray_of_mem hi hs]; exact h i hi
  · rw [D.ray_of_notMem hi his]; rfl

/-- **Unboundedness certificate** ([Chvatal1983], Chapter 2): if a nonbasic variable of a
feasible dictionary has a positive reduced cost and no row bounds its increase, the objective is
unbounded on the feasible set. -/
theorem not_bddAbove_value (hD : D.Feasible) {s : ι} (hs : s ∉ D.basis)
    (hc : 0 < D.objCoeff s) (h : ∀ i ∈ D.basis, 0 ≤ D.coeff i s) :
    ¬BddAbove (D.value '' D.feasibleSet) := by
  rintro ⟨M, hM⟩
  set t := (|M - D.objConst| + 1) / D.objCoeff s
  have ht : 0 ≤ t := div_nonneg (by positivity) hc.le
  have hmem : D.basicSolution + t • D.ray s ∈ D.feasibleSet :=
    ⟨D.isSolution_add_smul_ray hs D.isSolution_basicSolution t,
      fun i => add_nonneg ((D.feasible_iff_nonneg_basicSolution).1 hD i)
        (mul_nonneg ht (D.ray_nonneg hs h i))⟩
  have hle := hM ⟨_, hmem, rfl⟩
  rw [D.value_add_smul_ray hs, D.value_basicSolution, div_mul_cancel₀ _ hc.ne'] at hle
  have := le_abs_self (M - D.objConst)
  linarith

omit [IsStrictOrderedRing K] in
theorem feasibleSet_eq {D' : Dictionary ι K} (h : D.Equivalent D') :
    D.feasibleSet = D'.feasibleSet := by
  ext x
  exact and_congr_left' (h.isSolution_iff x)

omit [IsStrictOrderedRing K] in
/-- Equivalent dictionaries describe the same linear program. -/
theorem image_value_feasibleSet_eq {D' : Dictionary ι K} (h : D.Equivalent D') :
    D.value '' D.feasibleSet = D'.value '' D'.feasibleSet := by
  rw [← D.feasibleSet_eq h]
  exact Set.image_congr fun x hx => h.value_eq x hx.1

end Ordered

end Dictionary

end Cslib.Algorithms.Lean.Simplex
