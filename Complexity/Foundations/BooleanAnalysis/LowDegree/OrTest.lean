/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-!
# A seeded low-degree test for OR modulo two

Let `F` be a vector space over `𝔽₂` with a basis indexed by `κ`, and give every position `w` of a
finite set `A` a vector `e w ∈ F`. The integer function
`orTest b e A y = 1 - ∏_{j ∈ κ} (1 - ∑_{w ∈ A} [e w]_j y_w)`, where `[·]_j` is the `j`-th
coordinate, has degree at most `|κ|` in the bits `y`, and modulo `2` it is nonzero exactly when
`∑_{w ∈ A, y_w} e w ≠ 0` (`Cslib.BitString.orTest_emod_two_ne_zero_iff`). That sum is `0` when no
bit is true, so `orTest` computes the OR of the bits of `A` whenever the vectors of the true bits do
not sum to `0`.

With `F` a finite field and `e w = r ^ idx w` for an injective `idx : A → [0, N)` and a seed
`r ∈ F`, the sum is the value at `r` of the nonzero polynomial `∑_{w ∈ A, y_w} X ^ idx w` when some
bit is true. It has fewer than `N` roots (`Cslib.BitString.card_filter_sum_pow_eq_zero_le`), so for
any fixed bits all but fewer than `N` seeds give the OR. This is a seeded form of the probabilistic
polynomial for OR of Razborov [Razborov1987] and Smolensky [Smolensky1987], with seeds from the
powering construction of Alon, Goldreich, Håstad and Peralta [AlonGoldreichHastadPeralta1992,
Section 3]. Beigel and Tarui instead isolate a true bit by the Valiant–Vazirani lemma
[BeigelTarui1994, Lemma 2.3]; both give `O(log s)` seed bits and degree.

## Main definitions

* `Cslib.BitString.orTest`: the seeded OR test.

## Main results

* `Cslib.BitString.orTest_emod_two_ne_zero_iff`: what the test computes modulo two.
* `Cslib.BitString.orTest_mem_lowDegree`: its degree is at most the dimension.

## References

* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost k-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib.BitString

open Finset

variable {F κ ι : Type*} [AddCommGroup F] [Module (ZMod 2) F] [Fintype κ]

/-- **The seeded OR test** `1 - ∏_{j ∈ κ} (1 - ∑_{w ∈ A} [e w]_j y_w)`, where `[·]_j` is the
`j`-th coordinate in the basis `b` of `F` over `𝔽₂`, read as `0` or `1`. -/
noncomputable def orTest (b : Module.Basis κ (ZMod 2) F) (e : ι → F) (A : Finset ι)
    (y : ι → Bool) : ℤ :=
  1 - ∏ j, (1 - ∑ w ∈ A, ((b.repr (e w) j).val : ℤ) * bitVal ℤ (y w))

/-- An element of `𝔽₂` is `0` or `1`. -/
private theorem zmod_two_eq_zero_or_eq_one : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- The OR test reads only the bits of `A`. -/
theorem orTest_congr (b : Module.Basis κ (ZMod 2) F) (e : ι → F) (A : Finset ι) {y y' : ι → Bool}
    (h : ∀ w ∈ A, y w = y' w) : orTest b e A y = orTest b e A y' := by
  simp only [orTest]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun w hw => by rw [h w hw]]

/-- **What the OR test computes.** Modulo two, `orTest b e A y` is nonzero exactly when the vectors
`e w` of the true bits `w ∈ A` do not sum to `0`. -/
theorem orTest_emod_two_ne_zero_iff (b : Module.Basis κ (ZMod 2) F) (e : ι → F) (A : Finset ι)
    (y : ι → Bool) : orTest b e A y % 2 ≠ 0 ↔ ∑ w ∈ A with y w = true, e w ≠ 0 := by
  classical
  set P := ∑ w ∈ A with y w = true, e w
  have hcoord : ∀ j, ((∑ w ∈ A, ((b.repr (e w) j).val : ℤ) * bitVal ℤ (y w) : ℤ) : ZMod 2) =
      b.repr P j := by
    intro j
    rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_filter, Int.cast_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    cases y w <;> simp [bitVal]
  have hcast : ((orTest b e A y : ℤ) : ZMod 2) = 1 - ∏ j, (1 - b.repr P j) := by
    simp only [orTest, Int.cast_sub, Int.cast_one, Int.cast_prod, hcoord]
  have hmod : orTest b e A y % 2 ≠ 0 ↔ ((orTest b e A y : ℤ) : ZMod 2) ≠ 0 := by
    rw [Ne, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    rfl
  rw [hmod, hcast, Ne, sub_eq_zero, eq_comm]
  have hprod : ∏ j, (1 - b.repr P j) = 1 ↔ b.repr P = 0 := by
    constructor
    · intro h
      ext j
      rcases zmod_two_eq_zero_or_eq_one (b.repr P j) with hj | hj
      · exact hj
      · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; rfl)] at h
        exact absurd h (by decide)
    · intro h
      simp [h]
  rw [hprod, LinearEquiv.map_eq_zero_iff]

/-- **The OR test has degree at most the dimension.** If each bit `g w v` is a function of degree
at most `1` of `v`, then `orTest b e A (g · v)` has degree at most `|κ|` in `v`. -/
theorem orTest_mem_lowDegree {T : Type*} (b : Module.Basis κ (ZMod 2) F) (e : ι → F)
    (A : Finset ι) {g : ι → (T → Bool) → Bool}
    (hg : ∀ w ∈ A, (fun v => bitVal ℤ (g w v)) ∈ lowDegree ℤ T 1) :
    (fun v => orTest b e A fun w => g w v) ∈ lowDegree ℤ T (Fintype.card κ) := by
  have h : (fun v => orTest b e A fun w => g w v) =
      1 - ∏ j, (1 - ∑ w ∈ A, ((b.repr (e w) j).val : ℤ) • fun v => bitVal ℤ (g w v)) := by
    funext v
    simp only [orTest, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  rw [h]
  refine one_sub_mem_lowDegree ?_
  have := prod_mem_lowDegree (Finset.univ : Finset κ) (a := 1)
    (f := fun j => 1 - ∑ w ∈ A, ((b.repr (e w) j).val : ℤ) • fun v => bitVal ℤ (g w v))
    fun j _ => one_sub_mem_lowDegree
      (sum_mem_lowDegree _ fun w hw => Submodule.smul_mem _ _ (hg w hw))
  simpa using this

end Cslib.BitString
