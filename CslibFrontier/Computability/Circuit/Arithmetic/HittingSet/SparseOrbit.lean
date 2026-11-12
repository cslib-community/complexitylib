/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
public import CslibFrontier.Foundations.Data.MvPolynomial.LinearSubstitution
public import CslibFrontier.Foundations.Data.MvPolynomial.SparseShift
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial hitting sets for sparse affine orbits

Over a field `F` of characteristic zero, the *affine orbit* of the `n`-variate polynomials with
at most `s` monomials consists of the polynomials `f = p (A x + b)` with `p` such a polynomial,
`A` an invertible matrix and `b` a point. [Bhargava and Sengupta][BhargavaSengupta2026] give an
explicit hitting set of size `(n ^ 2 + 1) (2 d B + 1)`, where `B = n s ^ 2 + s`, for the
polynomials of degree at most `d` in this orbit (Theorem 1.2, items 1 and 2, of the source).

The points are `a (β) + t ^ B • G (t)` for `β = 0, …, n ^ 2` and `t = 0, …, 2 d B`, where
`a (β) = (β, β ^ 2, …, β ^ n)` and `G` is the logarithmic curve truncated below degree `B`
(`logCurve`). For a nonzero `f = p (A x + b)` of the class, one of any `n ^ 2 + 1` values of `β`
makes all coordinates of `u = A a (β) + b` nonzero (Lemma 1.6 of the source). Then
`f (a (β) + x) = g (A x)` for the translate `g = p (X + u)`, and by Lemma 3.2 of the source
(`MvPolynomial.finrank_iteratedPDerivSpan_homogeneousComponent_shift_le`) the partial derivatives
of the lowest homogeneous component `h` of `g`, of degree `m` say, span a space of dimension at
most `s`; so do those of `h (A x)`. Hence `h (A G (t))` is not divisible by `t ^ B`
(`not_X_pow_dvd_aeval_logCurve`), while `f (a (β) + t ^ B • G (t))` is the sum of
`t ^ (B m) * h (A G (t))` and a multiple of `t ^ (B (m + 1))`. So this univariate polynomial is
nonzero; its degree is at most `2 d B`, so it is nonzero at one of the values of `t`.

## Departures from the source

The source uses Hasse derivatives; here Lemma 3.2 is proved with ordinary partial derivatives.
The source's curve is `-ln (1 - i t)` truncated at degree `B`; here it is the library's curve
`ln (1 + (i + 1) t)` truncated below degree `B`, for which the multiplicity bound is available.
The source splits `f (a (β) + t ^ B • G (t))` into all homogeneous components of `f (a (β) + x)`;
here it is split into the lowest component of `g` and the rest, substituting `A G (t)` into
`g` rather than `G (t)` into `g (A x)`.

## Main definitions

* `sparseOrbitCurve`: the curve `t ↦ a (β) + t ^ B • G (t)`.
* `sparseOrbitHittingSet`: its points at `β = 0, …, n ^ 2` and `t = 0, …, 2 d (n s ^ 2 + s)`.

## Main results

* `isHittingSet_sparseOrbitHittingSet`, `card_sparseOrbitHittingSet_le`: the hitting set and its
  size.

## References

* [V. Bhargava, A. K. Sengupta, *Polynomial identity testing and lower bounds for sparse affine
  orbits*][BhargavaSengupta2026], Theorem 1.2 and Lemma 1.6
-/

@[expose] public section

open scoped Polynomial

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] (n : ℕ)

/-- The curve `t ↦ (β, β ^ 2, …, β ^ n) + t ^ B • G (t)`, for the logarithmic curve `G` truncated
below degree `B`. -/
noncomputable def sparseOrbitCurve (B : ℕ) (β : F) (i : Fin n) : F[X] :=
  Polynomial.C (β ^ ((i : ℕ) + 1)) + Polynomial.X ^ B * logCurve F n B i

open scoped Classical in
/-- The points of the curves `sparseOrbitCurve` for `β = 0, 1, …, n ^ 2` at
`t = 0, 1, …, 2 * d * (n * s ^ 2 + s)`. -/
noncomputable def sparseOrbitHittingSet (n s d : ℕ) : Finset (Fin n → F) :=
  (range (n ^ 2 + 1) ×ˢ range (2 * d * (n * s ^ 2 + s) + 1)).image fun (kl : ℕ × ℕ) (i : Fin n) =>
    (sparseOrbitCurve F n (n * s ^ 2 + s) (kl.1 : F) i).eval (kl.2 : F)

variable {F n}

theorem card_sparseOrbitHittingSet_le (s d : ℕ) :
    (sparseOrbitHittingSet F n s d).card ≤ (n ^ 2 + 1) * (2 * d * (n * s ^ 2 + s) + 1) := by
  classical
  exact card_image_le.trans_eq (by rw [card_product, card_range, card_range])

private theorem natDegree_sparseOrbitCurve_le (B : ℕ) (β : F) (i : Fin n) :
    (sparseOrbitCurve F n B β i).natDegree ≤ 2 * B := by
  have hB := natDegree_logCurve_le (F := F) B i
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (Polynomial.natDegree_mul_le.trans ?_))
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le _
  · rw [Polynomial.natDegree_X_pow]
    omega

/-- **Lemma 1.6 of the source**, the choice of the parameter. For an invertible matrix `A`, one
of the values `β = 0, …, n ^ 2` makes all coordinates of `A (β, β ^ 2, …, β ^ n) + b` nonzero. -/
private theorem exists_forall_sum_mul_pow_add_ne_zero {A : Matrix (Fin n) (Fin n) F}
    (hA : IsUnit A.det) (b : Fin n → F) :
    ∃ k ∈ range (n ^ 2 + 1), ∀ i, ∑ j, A i j * (k : F) ^ ((j : ℕ) + 1) + b i ≠ 0 := by
  classical
  set q : Fin n → F[X] := fun i =>
    ∑ j, Polynomial.C (A i j) * Polynomial.X ^ ((j : ℕ) + 1) + Polynomial.C (b i) with hq
  have heval (i : Fin n) (x : F) : (q i).eval x = ∑ j, A i j * x ^ ((j : ℕ) + 1) + b i := by
    simp [hq, Polynomial.eval_finsetSum]
  have hne (i : Fin n) : q i ≠ 0 := fun h0 =>
    hA.ne_zero (Matrix.det_eq_zero_of_row_eq_zero i fun j => by
      have h := congrArg (fun p : F[X] => p.coeff ((j : ℕ) + 1)) h0
      simpa [hq, Polynomial.coeff_C, Polynomial.coeff_X_pow, Fin.val_inj] using h)
  have hdeg (i : Fin n) : (q i).natDegree ≤ n :=
    (Polynomial.natDegree_add_le _ _).trans (max_le
      (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans j.2)
      ((Polynomial.natDegree_C _).trans_le (Nat.zero_le _)))
  by_contra hall
  refine prod_ne_zero_iff.2 (fun i _ => hne i)
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (∏ i, q i)
      ((range (n ^ 2 + 1)).image fun k : ℕ => (k : F)) ?_ ?_)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    obtain ⟨i, hi⟩ : ∃ i, ∑ j, A i j * (k : F) ^ ((j : ℕ) + 1) + b i = 0 :=
      not_forall_not.1 fun h => hall ⟨k, hk, h⟩
    rw [Polynomial.eval_prod]
    exact prod_eq_zero (mem_univ i) (by rw [heval, hi])
  · rw [card_image_of_injective _ Nat.cast_injective, card_range]
    refine Nat.lt_succ_of_le ((Polynomial.natDegree_prod_le _ _).trans ?_)
    calc ∑ i, (q i).natDegree ≤ ∑ _i : Fin n, n := sum_le_sum fun i _ => hdeg i
      _ = n ^ 2 := by simp [sq]

/-- For a nonzero polynomial `p` with at most `s` monomials, an invertible matrix `A` and a
parameter `β` at which all coordinates of `A (β, β ^ 2, …, β ^ n) + b` are nonzero, the
polynomial `p (A x + b)` does not vanish on the curve `sparseOrbitCurve` of `β`. -/
private theorem aeval_sparseOrbitCurve_ne_zero {p : MvPolynomial (Fin n) F}
    {A : Matrix (Fin n) (Fin n) F} {b : Fin n → F} {s : ℕ} (hs : p.support.card ≤ s)
    (hA : IsUnit A.det) (hp : p ≠ 0) {β : F}
    (hu : ∀ i, ∑ j, A i j * β ^ ((j : ℕ) + 1) + b i ≠ 0) :
    aeval (sparseOrbitCurve F n (n * s ^ 2 + s) β)
      (aeval (fun i => ∑ j, C (A i j) * X j + C (b i)) p) ≠ 0 := by
  classical
  set B := n * s ^ 2 + s with hB
  set u : Fin n → F := fun i => ∑ j, A i j * β ^ ((j : ℕ) + 1) + b i with hudef
  set g : MvPolynomial (Fin n) F := shift u p with hg
  set z : Fin n → F[X] := fun i => ∑ j, Polynomial.C (A i j) * logCurve F n B j with hz
  -- the restriction to the curve is `g (t ^ B • A G (t))`
  have hP : aeval (sparseOrbitCurve F n B β) (aeval (fun i => ∑ j, C (A i j) * X j + C (b i)) p) =
      aeval (fun i => Polynomial.X ^ B * z i) g := by
    rw [hg, shift, comp_aeval_apply, comp_aeval_apply]
    refine congrArg (fun L => aeval L p) (funext fun i => ?_)
    simp only [map_add, map_sum, map_mul, aeval_C, aeval_X, Polynomial.algebraMap_eq,
      sparseOrbitCurve, hz, hudef, mul_add, sum_add_distrib, mul_sum]
    rw [add_right_comm, add_comm]
    refine congrArg₂ (· + ·) (sum_congr rfl fun j _ => by ring) rfl
  -- the lowest homogeneous component `h` of `g`
  have hg0 : g ≠ 0 := fun h0 =>
    hp (shift_injective (algebraMap F F).injective u (h0.trans (map_zero _).symm))
  have hex : ∃ m, homogeneousComponent m g ≠ 0 :=
    not_forall_not.1 fun h => hg0 (eq_zero_of_homogeneousComponent_eq_zero fun j =>
      not_not.1 (h j))
  set m := Nat.find hex with hmdef
  have hm : ∀ j < m, homogeneousComponent j g = 0 := fun j hj => not_not.1 (Nat.find_min hex hj)
  set h := homogeneousComponent m g with hh
  have hh0 : h ≠ 0 := Nat.find_spec hex
  -- `h (A G (t))` is not divisible by `t ^ B`
  obtain ⟨hfin, hrank⟩ := finrank_iteratedPDerivSpan_homogeneousComponent_shift_le hu hm
  have hQ : ¬ Polynomial.X ^ B ∣ aeval z h := by
    have hz' : aeval z h = aeval (logCurve F n B) (linearSubst A h) := by
      rw [linearSubst, comp_aeval_apply]
      refine congrArg (fun L => aeval L h) (funext fun i => ?_)
      simp only [hz, map_sum, map_mul, aeval_C, aeval_X, Polynomial.algebraMap_eq]
    rw [hz']
    exact not_X_pow_dvd_aeval_logCurve
      (V := (iteratedPDerivSpan h).map (linearSubst A).toLinearMap)
      (fun i q hq => pderiv_mem_map_linearSubst A
        (fun i q hq => pderiv_mem_iteratedPDerivSpan i hq) i hq)
      ((Submodule.finrank_map_le _ _).trans (hrank.trans hs))
      (Submodule.mem_map_of_mem (self_mem_iteratedPDerivSpan h))
      fun h0 => hh0 (linearSubst_injective hA (h0.trans (map_zero _).symm))
  -- the rest of `g` contributes a multiple of `t ^ (B (m + 1))`
  have hrest : Polynomial.X ^ (B * m + B) ∣ aeval (fun i => Polynomial.X ^ B * z i) (g - h) := by
    have h1 : ∀ j < m + 1, homogeneousComponent j (g - h) = 0 := fun j hj => by
      rw [map_sub, hh, homogeneousComponent_of_mem (homogeneousComponent_mem m g)]
      split_ifs with hjm
      · rw [hjm, sub_self]
      · rw [hm j (by omega), sub_zero]
    have h2 := pow_dvd_aeval_mul_left h1 (Polynomial.X ^ B) z
    rwa [← pow_mul, Nat.mul_succ] at h2
  intro h0
  rw [hP, ← add_sub_cancel h g, map_add,
    aeval_mul_left_of_isHomogeneous (homogeneousComponent_isHomogeneous m g), ← pow_mul] at h0
  refine hQ ((mul_dvd_mul_iff_left (pow_ne_zero (B * m) Polynomial.X_ne_zero)).1 ?_)
  rw [← pow_add, eq_neg_of_add_eq_zero_left h0]
  exact (dvd_neg.2 hrest)

/-- **Theorem 1.2 of the source.** The set `sparseOrbitHittingSet F n s d` is a hitting set for
the polynomials `p (A x + b)` of degree at most `d`, where `p` has at most `s` monomials and `A`
is an invertible matrix. -/
theorem isHittingSet_sparseOrbitHittingSet (s d : ℕ) :
    IsHittingSet (sparseOrbitHittingSet F n s d)
      {f | f.totalDegree ≤ d ∧ ∃ (p : MvPolynomial (Fin n) F) (A : Matrix (Fin n) (Fin n) F)
        (b : Fin n → F), p.support.card ≤ s ∧ IsUnit A.det ∧
          f = aeval (fun i => ∑ j, C (A i j) * X j + C (b i)) p} := by
  rintro f ⟨hd, p, A, b, hs, hA, rfl⟩ hf0
  classical
  set B := n * s ^ 2 + s with hB
  obtain ⟨k, hk, hu⟩ := exists_forall_sum_mul_pow_add_ne_zero hA b
  have hne := aeval_sparseOrbitCurve_ne_zero hs hA
    (fun h0 => hf0 (by rw [h0, map_zero])) hu
  have hdeg : (aeval (sparseOrbitCurve F n B (k : F))
      (aeval (fun i => ∑ j, C (A i j) * X j + C (b i)) p)).natDegree < 2 * d * B + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_aeval_le_mul
      (natDegree_sparseOrbitCurve_le B (k : F)) _).trans ?_)
    calc _ ≤ d * (2 * B) := Nat.mul_le_mul_right _ hd
      _ = 2 * d * B := by ring
  by_contra hall
  refine hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    ((range (2 * d * B + 1)).image fun l : ℕ => (l : F)) ?_ ?_)
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hx
    rw [eval_polynomial_aeval]
    exact not_not.1 fun h =>
      hall ⟨_, mem_image.2 ⟨(k, l), mem_product.2 ⟨hk, hl⟩, rfl⟩, h⟩
  · rwa [card_image_of_injective _ Nat.cast_injective, card_range]

end Cslib.Circuits.Arithmetic
