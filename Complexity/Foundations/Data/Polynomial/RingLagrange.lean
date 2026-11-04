/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Lagrange.lean`)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange interpolation over a commutative ring

Mathlib's `Lagrange.interpolate` works over a field. Over a commutative ring `R`, interpolation at
nodes `v i`, `i ∈ s`, still works when the nodes have *unit differences*: every `v i - v j` with
`i ≠ j` is a unit. Galois rings such as `(ℤ / 2 ^ p)[U] / (f)` are the motivating example; they
are not domains, but lifts of distinct residue-field elements differ by units.

The Lagrange basis polynomial at `i` is `∏_{j ∈ s, j ≠ i} (X - v j) / (v i - v j)`, where the
division is multiplication by `Ring.inverse (v i - v j)` (`Lagrange.ringBasis`). It is one at
`v i` and zero at the other nodes, so `Lagrange.ringInterpolate s v r = ∑ i ∈ s, r i • basis i`
takes the value `r i` at `v i`. A polynomial of degree less than `#s` that vanishes at all nodes is
zero, because the factors `X - v i` are pairwise coprime; hence every polynomial of degree less
than `#s` is the interpolant of its values (`Lagrange.eq_ringInterpolate`). Over a field these
are Mathlib's `Lagrange.basis` and `Lagrange.interpolate`
(`Lagrange.ringInterpolate_eq_interpolate`).

## Main definitions

* `Lagrange.ringBasis`: the Lagrange basis polynomial, with `Ring.inverse` for division.
* `Lagrange.ringInterpolate`: Lagrange interpolation over a commutative ring, as a linear map.

## Main results

* `Lagrange.eval_ringInterpolate_at_node`: the interpolant takes the prescribed values.
* `Lagrange.degree_ringInterpolate_lt`: it has degree less than the number of nodes.
* `Lagrange.eq_zero_of_degree_lt_of_eval_eq_zero`: uniqueness at nodes with unit differences.
* `Lagrange.eq_ringInterpolate`: a polynomial of degree less than `#s` is the interpolant of its
  values.
* `Lagrange.ringInterpolate_eq_interpolate`: over a field, this is `Lagrange.interpolate`.
-/

public section

namespace Lagrange

open Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → R}
  {i j : ι}

/-- The Lagrange basis polynomial `∏_{j ∈ s, j ≠ i} (X - v j) / (v i - v j)` over a commutative
ring, where division by `v i - v j` is multiplication by `Ring.inverse (v i - v j)`. When the nodes
have unit differences it is one at `v i` and zero at the other nodes. -/
@[expose] noncomputable def ringBasis (s : Finset ι) (v : ι → R) (i : ι) : R[X] :=
  ∏ j ∈ s.erase i, C (Ring.inverse (v i - v j)) * (X - C (v j))

/-- **Lagrange interpolation over a commutative ring**: `∑ i ∈ s, r i • ringBasis s v i`. At nodes
with unit differences, it is the unique polynomial of degree less than `#s` taking the value `r i`
at `v i`. -/
@[expose] noncomputable def ringInterpolate (s : Finset ι) (v : ι → R) : (ι → R) →ₗ[R] R[X] where
  toFun r := ∑ i ∈ s, C (r i) * ringBasis s v i
  map_add' r r' := by
    simp only [Pi.add_apply, C_add, add_mul, sum_add_distrib]
  map_smul' c r := by
    simp only [Pi.smul_apply, smul_eq_mul, C_mul, RingHom.id_apply, smul_sum, mul_assoc,
      smul_eq_C_mul]

theorem ringInterpolate_apply (s : Finset ι) (v : ι → R) (r : ι → R) :
    ringInterpolate s v r = ∑ i ∈ s, C (r i) * ringBasis s v i :=
  rfl

/-- The basis polynomial at `i` is one at its own node. -/
theorem eval_ringBasis_self (hvs : (s : Set ι).Pairwise fun i j => IsUnit (v i - v j))
    (hi : i ∈ s) : (ringBasis s v i).eval (v i) = 1 := by
  rw [ringBasis, eval_prod]
  refine prod_eq_one fun j hj => ?_
  obtain ⟨hji, hj⟩ := mem_erase.mp hj
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C]
  exact Ring.inverse_mul_cancel _ (hvs hi hj (Ne.symm hji))

/-- The basis polynomial at `i` vanishes at every other node. -/
theorem eval_ringBasis_of_ne (hij : i ≠ j) (hj : j ∈ s) : (ringBasis s v i).eval (v j) = 0 := by
  rw [ringBasis, eval_prod]
  refine prod_eq_zero (mem_erase.mpr ⟨Ne.symm hij, hj⟩) ?_
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]

theorem natDegree_ringBasis_le (s : Finset ι) (v : ι → R) (i : ι) :
    (ringBasis s v i).natDegree ≤ #(s.erase i) := by
  refine (natDegree_prod_le _ _).trans
    ((sum_le_sum fun j _ => ?_).trans_eq (card_eq_sum_ones _).symm)
  exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)

/-- The basis polynomial at a node has degree less than the number of nodes. -/
theorem degree_ringBasis_lt (hi : i ∈ s) : (ringBasis s v i).degree < #s := by
  refine (degree_le_natDegree).trans_lt ?_
  have h := natDegree_ringBasis_le s v i
  rw [card_erase_of_mem hi] at h
  have hs : 0 < #s := card_pos.mpr ⟨i, hi⟩
  exact_mod_cast (show (ringBasis s v i).natDegree < #s by omega)

/-- The interpolant has degree less than the number of nodes. -/
theorem degree_ringInterpolate_lt (r : ι → R) : (ringInterpolate s v r).degree < #s := by
  rw [← mem_degreeLT, ringInterpolate_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (mem_degreeLT.mpr (degree_ringBasis_lt hi))

/-- **The interpolant takes the prescribed values** at nodes with unit differences. -/
theorem eval_ringInterpolate_at_node (hvs : (s : Set ι).Pairwise fun i j => IsUnit (v i - v j))
    (r : ι → R) (hi : i ∈ s) : (ringInterpolate s v r).eval (v i) = r i := by
  rw [ringInterpolate_apply, eval_finsetSum, sum_eq_single_of_mem i hi, eval_mul, eval_C,
    eval_ringBasis_self hvs hi, mul_one]
  intro j _ hji
  rw [eval_mul, eval_ringBasis_of_ne hji hi, mul_zero]

omit [DecidableEq ι] in
/-- **Uniqueness of interpolation over a commutative ring.** A polynomial of degree less than
`#s` that vanishes at nodes with unit differences is zero: the factors `X - v i` are pairwise
coprime, so their product, of degree `#s`, divides it. -/
theorem eq_zero_of_degree_lt_of_eval_eq_zero
    (hvs : (s : Set ι).Pairwise fun i j => IsUnit (v i - v j)) {f : R[X]} (hf : f.degree < #s)
    (h0 : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  nontriviality R
  by_contra hne
  have hdvd : nodal s v ∣ f := by
    rw [nodal]
    refine prod_dvd_of_coprime (fun i hi j hj hij => ?_) fun i hi => ?_
    · exact isCoprime_X_sub_C_of_isUnit_sub (hvs hi hj hij)
    · exact dvd_iff_isRoot.mpr (h0 i hi)
  exact nodal_monic.not_dvd_of_degree_lt hne (by rwa [degree_nodal]) hdvd

/-- **Every polynomial of degree less than `#s` is the interpolant of its values** at nodes with
unit differences. -/
theorem eq_ringInterpolate (hvs : (s : Set ι).Pairwise fun i j => IsUnit (v i - v j))
    {f : R[X]} (hf : f.degree < #s) : f = ringInterpolate s v (fun i => f.eval (v i)) := by
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_eq_zero hvs
    ((degree_sub_le _ _).trans_lt (max_lt hf (degree_ringInterpolate_lt _))) fun i hi => ?_)
  rw [eval_sub, eval_ringInterpolate_at_node hvs _ hi, sub_self]

/-- Over a field, `ringBasis` is Mathlib's `Lagrange.basis`. -/
theorem ringBasis_eq_basis {F : Type*} [Field F] (s : Finset ι) (v : ι → F) (i : ι) :
    ringBasis s v i = Lagrange.basis s v i := by
  simp only [ringBasis, Lagrange.basis, basisDivisor, Ring.inverse_eq_inv']

/-- Over a field, `ringInterpolate` is Mathlib's `Lagrange.interpolate`. -/
theorem ringInterpolate_eq_interpolate {F : Type*} [Field F] (s : Finset ι) (v : ι → F) :
    ringInterpolate s v = interpolate s v := by
  ext r : 1
  simp only [ringInterpolate_apply, interpolate_apply, ringBasis_eq_basis]

end Lagrange
