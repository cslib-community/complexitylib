/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.KernelVector
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Sudan interpolants, weighted degree, and elimination

Let `w : ι → F` be a received word and let `α` be distinct evaluation points. Sudan's list decoder
[Sudan1997], [GuruswamiRudraSudan2019] for polynomials `P` of degree at most `d` needs a nonzero
bivariate polynomial `Q(X, Y)` of `(1, d)`-weighted degree at most `D`
(`Cslib.Code.Sudan.WeightedDegreeLE`), that is with `a + d * b ≤ D` for each of its monomials
`X ^ a * Y ^ b`, vanishing at the `n` points `(α i, w i)` (`Cslib.Code.Sudan.IsInterpolant`).
Such a `Q` is a nonzero solution of `n` linear equations in its coefficients, so it exists as soon
as there are more than `n` monomials of `(1, d)`-weighted degree at most `D`
(`Cslib.Code.Sudan.exists_isInterpolant`); for `d ≥ 1` there are at least
`(D + 1) * (D + 2) / (2 * d)` of them
(`Cslib.Code.Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials`). If `P` has degree at most
`d`, then `Q(X, P(X))` has degree at most `D`
(`Cslib.Code.Sudan.WeightedDegreeLE.natDegree_eval_le`) and vanishes at every point where `P`
agrees with `w`; when there are more than `D` of them it is zero, so `Y - P(X)` divides `Q(X, Y)`
(`Cslib.Code.Sudan.IsInterpolant.X_sub_C_dvd`): `P` is a root of `Q` viewed as a polynomial in `Y`
over `F[X]`.

This module also computes an explicit interpolant by linear algebra, choosing one of least
`Y`-degree: for `j = 0, 1, …, D / d` it finds a kernel vector of the interpolation matrix
restricted to the monomials of `Y`-degree at most `j` (`Cslib.LinearAlgebra.kernelVec`), and takes
the first nonzero one (`Cslib.Code.Sudan.interpolant`). When `d ≥ 1` and there are more monomials
than points this is an interpolant (`Cslib.Code.Sudan.isInterpolant_interpolant`), and no
interpolant has smaller `Y`-degree (`Cslib.Code.Sudan.natDegree_interpolant_le`).

Least `Y`-degree makes every polynomial `P` of degree at most `d` with more than `D` agreements a
*simple* root of `Q`, viewed as a polynomial in `Y`: if `(Y - P)²` divided `Q`, then `Q / (Y - P)`
would be an interpolant of smaller `Y`-degree. On division by `Y - P` the bound `D` on the
weighted degree drops to `D - d` (`Cslib.Code.Sudan.add_mul_add_one_le_of_mul`, an upper bound),
so `Q = (Y - P) * S` where `S(X, P(X))` is a nonzero polynomial of degree at most `D - d`
(`Cslib.Code.Sudan.exists_eq_mul_eval_ne_zero`). Simplicity is what lets the root `P` be lifted
from a single known value by Newton iteration (`Cslib.Code.henselValue_eq`).

## Main definitions

* `Cslib.Code.Sudan.monomials`: the monomials of bounded weighted degree.
* `Cslib.Code.Sudan.WeightedDegreeLE`: bivariate polynomials of bounded `(1, d)`-weighted degree.
* `Cslib.Code.Sudan.bivariateOf`: the bivariate polynomial with given coefficients on a set of
  monomials.
* `Cslib.Code.Sudan.IsInterpolant`: the bivariate interpolants of a received word.
* `Cslib.Code.Sudan.monomialsUpTo`: the monomials of bounded weighted degree and bounded
  `Y`-degree.
* `Cslib.Code.Sudan.interpMatrix`: the interpolation matrix on a set of monomials.
* `Cslib.Code.Sudan.coeffsOf`: the coefficients on a set of monomials given by a vector indexed by
  its enumeration.
* `Cslib.Code.Sudan.kernelVecUpTo`: the kernel vector of the interpolation matrix on the monomials
  of `Y`-degree at most `j`.
* `Cslib.Code.Sudan.interpolantCoeffs`: the coefficients of the first nonzero kernel vector.
* `Cslib.Code.Sudan.interpolant`: an interpolant of least `Y`-degree, by elimination.

## Main results

* `Cslib.Code.Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials`: counting the monomials.
* `Cslib.Code.Sudan.WeightedDegreeLE.natDegree_mul_le`,
  `Cslib.Code.Sudan.IsInterpolant.natDegree_mul_le`: the `Y`-degree under a weighted-degree bound.
* `Cslib.Code.Sudan.WeightedDegreeLE.natDegree_eval_le`: the degree of `Q(X, P(X))`.
* `Cslib.Code.Sudan.exists_isInterpolant`: interpolants exist when there are more than `n`
  monomials.
* `Cslib.Code.Sudan.IsInterpolant.eval_eq_zero`, `Cslib.Code.Sudan.IsInterpolant.X_sub_C_dvd`,
  `Cslib.Code.Sudan.IsInterpolant.mem_roots`: root containment, the polynomials with large agreement
  are roots of every interpolant.
* `Cslib.Code.Sudan.weightedDegreeLE_interpolant`, `Cslib.Code.Sudan.isInterpolant_interpolant`:
  the elimination interpolant has bounded weighted degree and is an interpolant.
* `Cslib.Code.Sudan.natDegree_interpolant_le`: it has least `Y`-degree.
* `Cslib.Code.Sudan.add_mul_add_one_le_of_mul`: division by `Y - P` lowers the weighted degree
  by `d`.
* `Cslib.Code.Sudan.exists_eq_mul_eval_ne_zero`: polynomials with large agreement are simple roots
  of an interpolant of least `Y`-degree.

## References

* [M. Sudan, *Decoding of Reed Solomon codes beyond the error-correction bound*][Sudan1997]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code.Sudan

open Finset Polynomial Cslib.LinearAlgebra
open scoped Polynomial.Bivariate

variable {F ι : Type*} [Field F]

/-! ### Monomials and weighted degree -/

/-- The exponents `(a, b)` with `a, b ≤ D` of the monomials `X ^ a * Y ^ b` of `(1, d)`-weighted
degree `a + d * b` at most `D`. For `d ≥ 1` the bound `b ≤ D` holds for all of them. -/
def monomials (d D : ℕ) : Finset (ℕ × ℕ) :=
  {ab ∈ range (D + 1) ×ˢ range (D + 1) | ab.1 + d * ab.2 ≤ D}

/-- `(a, b)` is in `monomials d D` exactly when `a ≤ D`, `b ≤ D` and `a + d * b ≤ D`. -/
theorem mem_monomials {d D : ℕ} {ab : ℕ × ℕ} :
    ab ∈ monomials d D ↔ ab.1 ≤ D ∧ ab.2 ≤ D ∧ ab.1 + d * ab.2 ≤ D := by
  simp only [monomials, mem_filter, mem_product, mem_range, Nat.lt_succ_iff, and_assoc]

/-- `∑ j < n, 2 * (j + 1) = n * (n + 1)`. -/
private theorem sum_range_two_mul_add_one (n : ℕ) :
    ∑ j ∈ range n, 2 * (j + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-- **Counting monomials.** For `w ≥ 1` there are at least `(D + 1) * (D + 2) / (2 * w)` monomials
of `(1, w)`-weighted degree at most `D`: for each `j ≤ D` there are `j / w + 1 ≥ (j + 1) / w` of
weighted degree exactly `j`. -/
theorem add_one_mul_add_two_le_two_mul_mul_card_monomials {w : ℕ} (hw : 1 ≤ w) (D : ℕ) :
    (D + 1) * (D + 2) ≤ 2 * w * #(monomials w D) := by
  -- the monomials of weighted degree `j`
  let fiber : ℕ → Finset (ℕ × ℕ) := fun j => {ab ∈ monomials w D | ab.1 + w * ab.2 = j}
  have hcard : #(monomials w D) = ∑ j ∈ range (D + 1), #(fiber j) :=
    card_eq_sum_card_fiberwise fun ab hab =>
      mem_range.2 (Nat.lt_succ_of_le (mem_monomials.1 hab).2.2)
  have hfiber (j : ℕ) (hj : j ∈ range (D + 1)) : j / w + 1 ≤ #(fiber j) := by
    have hjD := Nat.lt_succ_iff.1 (mem_range.1 hj)
    calc j / w + 1 = #((range (j / w + 1)).image fun b => (j - w * b, b)) := by
          rw [card_image_of_injective _ fun b b' h => (Prod.ext_iff.1 h).2, card_range]
      _ ≤ #(fiber j) := by
          refine card_le_card fun ab hab => ?_
          obtain ⟨b, hb, rfl⟩ := mem_image.1 hab
          have hb : w * b ≤ j :=
            (Nat.mul_le_mul_left w (Nat.lt_succ_iff.1 (mem_range.1 hb))).trans (Nat.mul_div_le j w)
          have hbj : b ≤ j := (Nat.le_mul_of_pos_left b hw).trans hb
          refine mem_filter.2 ⟨mem_monomials.2 ⟨?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
  calc (D + 1) * (D + 2) = ∑ j ∈ range (D + 1), 2 * (j + 1) := (sum_range_two_mul_add_one _).symm
    _ ≤ ∑ j ∈ range (D + 1), 2 * w * #(fiber j) := by
        refine sum_le_sum fun j hj => ?_
        rw [mul_assoc]
        exact Nat.mul_le_mul_left 2 ((Nat.lt_mul_div_succ j hw).trans_le
          (Nat.mul_le_mul_left w (hfiber j hj)))
    _ = 2 * w * #(monomials w D) := by rw [← mul_sum, hcard]

/-- `Q` has `(1, d)`-weighted degree at most `D`: every nonzero coefficient `Q_{a,b} X ^ a Y ^ b`
has `a + d * b ≤ D`. -/
def WeightedDegreeLE (d D : ℕ) (Q : F[X][Y]) : Prop :=
  ∀ a b, (Q.coeff b).coeff a ≠ 0 → a + d * b ≤ D

/-- The zero polynomial has `(1, d)`-weighted degree at most `D`. -/
@[simp]
theorem weightedDegreeLE_zero (d D : ℕ) : WeightedDegreeLE d D (0 : F[X][Y]) := by
  intro a b hab
  simp at hab

/-- Monotonicity of `(1, d)`-weighted degree in the bound `D`. -/
theorem WeightedDegreeLE.mono {d D D' : ℕ} {Q : F[X][Y]} (hQ : WeightedDegreeLE d D Q)
    (hD : D ≤ D') : WeightedDegreeLE d D' Q :=
  fun a b hab => (hQ a b hab).trans hD

/-- If `Q` has `(1, d)`-weighted degree at most `D`, its `Y`-degree satisfies
`deg_Y Q * d ≤ D`. -/
theorem WeightedDegreeLE.natDegree_mul_le {d D : ℕ} {Q : F[X][Y]}
    (hQ : WeightedDegreeLE d D Q) : Q.natDegree * d ≤ D := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp
  · have hlead : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.2 hQ0
    have := hQ _ _ (leadingCoeff_ne_zero.2 hlead)
    rw [mul_comm]
    omega

/-- Evaluating `Q(X, P(X))` at `x` evaluates `Q` at `(x, P(x))`. -/
theorem _root_.Polynomial.eval_eval_eq_evalEval {R : Type*} [CommSemiring R] (Q : R[X][Y])
    (P : R[X]) (x : R) : (Q.eval P).eval x = Q.evalEval x (P.eval x) := by
  rw [← map_evalRingHom_eval, eval_map]
  exact (hom_eval₂ Q (RingHom.id _) (evalRingHom x) P).trans (by rw [RingHom.comp_id]; rfl)

/-- Substituting `Y = P(X)`, with `P` of degree at most `d`, into a bivariate polynomial of
`(1, d)`-weighted degree at most `E` gives a polynomial of degree at most `E`. -/
theorem WeightedDegreeLE.natDegree_eval_le {d E : ℕ} {S : F[X][Y]} {P : F[X]}
    (hS : WeightedDegreeLE d E S) (hP : P.natDegree ≤ d) : (S.eval P).natDegree ≤ E := by
  rw [eval_eq_sum_range]
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rcases eq_or_ne (S.coeff b) 0 with h0 | h0
  · simp [h0]
  have := hS _ b (leadingCoeff_ne_zero.2 h0)
  calc (S.coeff b * P ^ b).natDegree ≤ (S.coeff b).natDegree + b * P.natDegree :=
        Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left natDegree_pow_le _)
    _ ≤ (S.coeff b).natDegree + d * b := by
        rw [mul_comm d]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left b hP) _
    _ ≤ E := this

/-! ### Bivariate polynomials from coefficients -/

/-- The bivariate polynomial with coefficient `c m` at `X ^ m.1 * Y ^ m.2` for `m ∈ M`. -/
noncomputable def bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) : F[X][Y] :=
  ∑ m ∈ M, monomial m.2 (monomial m.1 (c m))

/-- The coefficient of `X ^ a * Y ^ b` in `bivariateOf M c` is `c (a, b)` when `(a, b) ∈ M`, and
zero otherwise. -/
@[simp]
theorem coeff_coeff_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (a b : ℕ) :
    ((bivariateOf M c).coeff b).coeff a = if (a, b) ∈ M then c (a, b) else 0 := by
  classical
  simp only [bivariateOf, finsetSum_coeff]
  rw [Finset.sum_congr rfl fun m _ => (?_ :
    ((monomial m.2 (monomial m.1 (c m))).coeff b).coeff a = if (a, b) = m then c m else 0)]
  · exact Finset.sum_ite_eq M (a, b) c
  · obtain ⟨a', b'⟩ := m
    simp only [coeff_monomial, Prod.mk.injEq]
    by_cases hb : b' = b
    · subst hb
      by_cases ha : a' = a
      · subst ha
        simp
      · simp [coeff_monomial, ha, Ne.symm ha]
    · simp [hb, Ne.symm hb]

/-- The value of `bivariateOf M c` at `(x, y)` is `∑ m ∈ M, c m * x ^ m.1 * y ^ m.2`. -/
theorem evalEval_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (x y : F) :
    (bivariateOf M c).evalEval x y = ∑ m ∈ M, c m * x ^ m.1 * y ^ m.2 := by
  simp only [bivariateOf, evalEval_finsetSum]
  refine sum_congr rfl fun m _ => ?_
  simp [evalEval, eval_monomial, mul_assoc]

/-- `bivariateOf M c` depends only on the values of `c` on `M`. -/
theorem bivariateOf_congr {M : Finset (ℕ × ℕ)} {c c' : ℕ × ℕ → F} (h : ∀ m ∈ M, c m = c' m) :
    bivariateOf M c = bivariateOf M c' :=
  sum_congr rfl fun m hm => by rw [h m hm]

/-- A bivariate polynomial whose monomials lie in `M` is `bivariateOf M` of its coefficients. -/
theorem eq_bivariateOf {Q : F[X][Y]} {M : Finset (ℕ × ℕ)}
    (h : ∀ a b, (Q.coeff b).coeff a ≠ 0 → (a, b) ∈ M) :
    Q = bivariateOf M fun m => (Q.coeff m.2).coeff m.1 := by
  ext b a
  rw [coeff_coeff_bivariateOf]
  split_ifs with hab
  · rfl
  · by_contra hne
    exact hab (h a b hne)

/-- `bivariateOf M c` has `(1, d)`-weighted degree at most `D` when `M ⊆ monomials d D`. -/
theorem weightedDegreeLE_bivariateOf {M : Finset (ℕ × ℕ)} {d D : ℕ} (hM : M ⊆ monomials d D)
    (c : ℕ × ℕ → F) : WeightedDegreeLE d D (bivariateOf M c) := by
  intro a b hab
  rw [coeff_coeff_bivariateOf] at hab
  split_ifs at hab with h
  · exact (mem_monomials.1 (hM h)).2.2
  · exact absurd rfl hab

/-! ### Sudan interpolants -/

/-- `Q` is a *Sudan interpolant* for the received word `w` with evaluation points `α`, weight `d`
and weighted degree `D`: a nonzero bivariate polynomial of `(1, d)`-weighted degree at most `D`
that vanishes at the points `(α i, w i)`. -/
structure IsInterpolant (α w : ι → F) (d D : ℕ) (Q : F[X][Y]) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- Every monomial `X ^ a * Y ^ b` of `Q` has `(1, d)`-weighted degree `a + d * b` at most
  `D`. -/
  weightedDegree_le : WeightedDegreeLE d D Q
  /-- The interpolant vanishes at the points `(α i, w i)`. -/
  evalEval_eq_zero : ∀ i, Q.evalEval (α i) (w i) = 0

variable {α w : ι → F} {d D : ℕ} {Q : F[X][Y]}

/-- The `Y`-degree of a Sudan interpolant: `deg_Y Q * d ≤ D`. -/
theorem IsInterpolant.natDegree_mul_le (hQ : IsInterpolant α w d D Q) :
    Q.natDegree * d ≤ D :=
  hQ.weightedDegree_le.natDegree_mul_le

variable [Fintype ι]

/-- **Interpolation.** If there are more than `n` monomials of `(1, d)`-weighted degree at most
`D`, every received word has a Sudan interpolant: the `n` conditions `Q (α i, w i) = 0` are linear
in the coefficients of `Q`. -/
theorem exists_isInterpolant (α w : ι → F)
    (hn : Fintype.card ι < #(monomials d D)) : ∃ Q, IsInterpolant α w d D Q := by
  classical
  let M := monomials d D
  let A : Matrix ι M F := Matrix.of fun i m => α i ^ m.1.1 * w i ^ m.1.2
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        Fintype.card_coe])
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hc0
  let c' : ℕ × ℕ → F := fun m' => if h : m' ∈ M then c ⟨m', h⟩ else 0
  refine ⟨bivariateOf M c', fun h => hm ?_, weightedDegreeLE_bivariateOf Subset.rfl c',
    fun i => ?_⟩
  · have := coeff_coeff_bivariateOf M c' m.1.1 m.1.2
    rw [h] at this
    simpa [c', m.2] using this.symm
  · rw [evalEval_bivariateOf, ← sum_attach]
    have := congrFun (LinearMap.mem_ker.1 hc) i
    simpa [A, c', Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using this

variable [DecidableEq F]

/-- **Root containment.** With distinct points, if `P` has degree at most `d` and agrees with the
received word at more than `D` points, then `Q(X, P(X)) = 0` for every Sudan interpolant `Q`. -/
theorem IsInterpolant.eval_eq_zero (hα : Function.Injective α) (hQ : IsInterpolant α w d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) : Q.eval P = 0 := by
  let agree : Finset ι := {i | P.eval (α i) = w i}
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (agree.image α) ?_ fun x hx => ?_
  · rw [card_image_of_injective _ hα]
    exact (degree_le_natDegree.trans
      (Nat.cast_le.2 (hQ.weightedDegree_le.natDegree_eval_le hP))).trans_lt
      (by exact_mod_cast hagree)
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    rw [eval_eval_eq_evalEval, (mem_filter.1 hi).2, hQ.evalEval_eq_zero]

/-- **Root containment.** With distinct points, if `P` has degree at most `d` and agrees with the
received word at more than `D` points, then `Y - P(X)` divides every Sudan interpolant
`Q(X, Y)`. -/
theorem IsInterpolant.X_sub_C_dvd (hα : Function.Injective α) (hQ : IsInterpolant α w d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) : Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- With distinct points, a polynomial of degree at most `d` that agrees with the received word
at more than `D` points is a root of every Sudan interpolant, as a polynomial in `Y`. -/
theorem IsInterpolant.mem_roots (hα : Function.Injective α) (hQ : IsInterpolant α w d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) : P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

/-! ### The interpolation matrix -/

/-- The monomials of `(1, d)`-weighted degree at most `D` and `Y`-degree at most `j`. -/
def monomialsUpTo (d D j : ℕ) : Finset (ℕ × ℕ) := (monomials d D).filter fun m => m.2 ≤ j

/-- The interpolation matrix: its rows are the points `(α i, w i)` (enumerated by
`Fintype.equivFin ι`), its columns the monomials of `M` (enumerated by `M.equivFin`), and its
entries the values of the monomials at the points. -/
noncomputable def interpMatrix (α w : ι → F) (M : Finset (ℕ × ℕ)) :
    Fin (Fintype.card ι) → Fin #M → F :=
  fun t m => α ((Fintype.equivFin ι).symm t) ^ (M.equivFin.symm m : ℕ × ℕ).1 *
    w ((Fintype.equivFin ι).symm t) ^ (M.equivFin.symm m : ℕ × ℕ).2

/-- The coefficients on `M` given by a vector indexed by the enumeration of `M`, and zero
elsewhere. -/
noncomputable def coeffsOf (M : Finset (ℕ × ℕ)) (u : Fin #M → F) (m : ℕ × ℕ) : F :=
  if h : m ∈ M then u (M.equivFin ⟨m, h⟩) else 0

omit [DecidableEq F] in
/-- The product of a row of the interpolation matrix with a vector `u` is the value at the row's
point of the polynomial with coefficients `u`. -/
theorem interpMatrix_dotProduct (α w : ι → F) (M : Finset (ℕ × ℕ)) (u : Fin #M → F)
    (i : ι) :
    interpMatrix α w M (Fintype.equivFin ι i) ⬝ᵥ u =
      (bivariateOf M (coeffsOf M u)).evalEval (α i) (w i) := by
  rw [evalEval_bivariateOf, dotProduct]
  have h := Equiv.sum_comp M.equivFin.symm
    (fun m : M => α i ^ (m : ℕ × ℕ).1 * w i ^ (m : ℕ × ℕ).2 * u (M.equivFin m))
  simp only [Equiv.apply_symm_apply] at h
  rw [← Finset.sum_coe_sort M (fun m => coeffsOf M u m * α i ^ m.1 * w i ^ m.2)]
  simp only [interpMatrix, Equiv.symm_apply_apply]
  rw [h]
  refine Fintype.sum_congr _ _ fun m => ?_
  simp only [coeffsOf, Finset.coe_mem, dite_true, Subtype.coe_eta]
  ring

/-! ### The interpolant of least `Y`-degree -/

/-- The kernel vector of the interpolation matrix on the monomials of `Y`-degree at most `j`. -/
noncomputable def kernelVecUpTo (α w : ι → F) (d D j : ℕ) : Fin #(monomialsUpTo d D j) → F :=
  kernelVec (interpMatrix α w (monomialsUpTo d D j))

/-- The coefficients of the interpolant: those of the first nonzero kernel vector among
`j = 0, 1, …, D / d`. -/
noncomputable def interpolantCoeffs (α w : ι → F) (d D : ℕ) : ℕ × ℕ → F :=
  ∑ j : Fin (D / d + 1),
    firstFlags (fun j : Fin (D / d + 1) => if kernelVecUpTo α w d D j = 0 then (0 : F) else 1) j •
      coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j)

/-- **An interpolant of least `Y`-degree**, computed by elimination. -/
noncomputable def interpolant (α w : ι → F) (d D : ℕ) : F[X][Y] :=
  bivariateOf (monomials d D) (interpolantCoeffs α w d D)

/-- The elimination interpolant always has `(1, d)`-weighted degree at most `D`. -/
theorem weightedDegreeLE_interpolant (α w : ι → F) (d D : ℕ) :
    WeightedDegreeLE d D (interpolant α w d D) :=
  weightedDegreeLE_bivariateOf Subset.rfl _

omit [Fintype ι] [DecidableEq F] in
/-- The monomials of an interpolant lie in `monomials d D`. -/
private theorem mem_monomials_of_isInterpolant {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d)
    {Q : F[X][Y]} (hQ : IsInterpolant α w d D Q) {a b : ℕ}
    (hab : (Q.coeff b).coeff a ≠ 0) : (a, b) ∈ monomials d D := by
  have h := hQ.weightedDegree_le a b hab
  refine mem_monomials.2 ⟨by omega, ?_, h⟩
  nlinarith

/-- An interpolant of `Y`-degree at most `j` gives a nonzero kernel vector on the monomials of
`Y`-degree at most `j`. -/
private theorem kernelVecUpTo_ne_zero {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d) {Q : F[X][Y]}
    (hQ : IsInterpolant α w d D Q) {j : ℕ} (hj : Q.natDegree ≤ j) :
    kernelVecUpTo α w d D j ≠ 0 := by
  have hsupp : ∀ a b, (Q.coeff b).coeff a ≠ 0 → (a, b) ∈ monomialsUpTo d D j := fun a b hab =>
    mem_filter.2 ⟨mem_monomials_of_isInterpolant hd hQ hab,
      (le_natDegree_of_ne_zero fun h => hab (by rw [h, coeff_zero])).trans hj⟩
  refine kernelVec_ne_zero _ ⟨fun m =>
    (Q.coeff ((monomialsUpTo d D j).equivFin.symm m : ℕ × ℕ).2).coeff
      ((monomialsUpTo d D j).equivFin.symm m : ℕ × ℕ).1, ?_, funext fun t => ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, Q.coeff b ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ.ne_zero (Polynomial.ext fun b => by rw [h b, coeff_zero])
    obtain ⟨a, ha⟩ : ∃ a, (Q.coeff b).coeff a ≠ 0 := by
      by_contra h
      push Not at h
      exact hb (Polynomial.ext fun a => by rw [h a, coeff_zero])
    intro h0
    have := congrFun h0 ((monomialsUpTo d D j).equivFin ⟨(a, b), hsupp a b ha⟩)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    exact ha this
  · change interpMatrix α w (monomialsUpTo d D j) t ⬝ᵥ _ = 0
    obtain ⟨i, rfl⟩ := (Fintype.equivFin ι).surjective t
    rw [interpMatrix_dotProduct, ← hQ.evalEval_eq_zero i]
    congr 1
    refine (bivariateOf_congr fun m hm => ?_).trans (eq_bivariateOf hsupp).symm
    simp only [coeffsOf, dite_eq_left hm, Equiv.symm_apply_apply]

/-- The interpolant is `bivariateOf` of the first nonzero kernel vector, at an index `j` below
which all kernel vectors vanish. -/
private theorem exists_interpolant_eq {α w : ι → F} {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) :
    ∃ j : Fin (D / d + 1), kernelVecUpTo α w d D j ≠ 0 ∧
      (∀ i < j, kernelVecUpTo α w d D i = 0) ∧
      interpolantCoeffs α w d D = coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_isInterpolant α w hn
  have hdeg : Q₀.natDegree ≤ D / d := (Nat.le_div_iff_mul_le hd).2 hQ₀.natDegree_mul_le
  obtain h | h := sum_firstFlags_smul_eq
      (fun j : Fin (D / d + 1) => if kernelVecUpTo α w d D j = 0 then (0 : F) else 1)
      (fun j => coeffsOf (monomialsUpTo d D j) (kernelVecUpTo α w d D j))
  · exfalso
    have := congrFun h.1 ⟨Q₀.natDegree, Nat.lt_succ_of_le hdeg⟩
    simp only [Pi.zero_apply, ite_eq_left_iff, one_ne_zero, imp_false, not_not] at this
    exact kernelVecUpTo_ne_zero hd hQ₀ le_rfl this
  · obtain ⟨j, hj, hlt, hsum⟩ := h
    refine ⟨j, fun h => hj (by simp [h]), fun i hi => ?_, hsum⟩
    have := hlt i hi
    simpa using this

/-- **The elimination interpolant is an interpolant.** With `d ≥ 1` and more monomials of
`(1, d)`-weighted degree at most `D` than points, `interpolant α w d D` is a Sudan interpolant of
weight `d` and weighted degree `D`. -/
theorem isInterpolant_interpolant (α w : ι → F) {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) :
    IsInterpolant α w d D (interpolant α w d D) := by
  obtain ⟨j, hj, -, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  set M := monomialsUpTo d D (j : ℕ)
  have hsub : M ⊆ monomials d D := filter_subset _ _
  have hcoeff : ∀ a b, ((interpolant α w d D).coeff b).coeff a =
      coeffsOf M (kernelVecUpTo α w d D j) (a, b) := by
    intro a b
    rw [interpolant, coeff_coeff_bivariateOf, hcoeffs]
    split_ifs with h
    · rfl
    · simp only [coeffsOf]
      rw [dite_eq_right fun h' => absurd (hsub h') h]
  refine ⟨fun h0 => hj ?_, weightedDegreeLE_interpolant α w d D, fun i => ?_⟩
  · funext m
    have := hcoeff (M.equivFin.symm m : ℕ × ℕ).1 (M.equivFin.symm m : ℕ × ℕ).2
    rw [h0] at this
    simp only [coeff_zero, coeffsOf, Prod.mk.eta, coe_mem, dite_eq_left, Subtype.coe_eta,
      Equiv.apply_symm_apply] at this
    exact this.symm
  · have hzero : interpMatrix α w M (Fintype.equivFin ι i) ⬝ᵥ kernelVecUpTo α w d D j = 0 :=
      congrFun (mulVec_kernelVec _) _
    rw [interpMatrix_dotProduct, evalEval_bivariateOf] at hzero
    rw [interpolant, hcoeffs, evalEval_bivariateOf, ← hzero]
    refine (Finset.sum_subset hsub fun m _ hm => ?_).symm
    simp only [coeffsOf]
    rw [dite_eq_right fun h => absurd h hm, zero_mul, zero_mul]

/-- **The elimination interpolant has least `Y`-degree** among all Sudan interpolants. -/
theorem natDegree_interpolant_le (α w : ι → F) {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι < #(monomials d D)) {Q : F[X][Y]}
    (hQ : IsInterpolant α w d D Q) :
    (interpolant α w d D).natDegree ≤ Q.natDegree := by
  obtain ⟨j, -, hlt, hcoeffs⟩ := exists_interpolant_eq (α := α) (w := w) hd hn
  have hdeg : Q.natDegree ≤ D / d := (Nat.le_div_iff_mul_le hd).2 hQ.natDegree_mul_le
  have hj : (j : ℕ) ≤ Q.natDegree := by
    by_contra h
    push Not at h
    exact kernelVecUpTo_ne_zero hd hQ le_rfl
      (hlt ⟨Q.natDegree, Nat.lt_succ_of_le hdeg⟩ (Fin.lt_def.2 h))
  refine (natDegree_le_iff_coeff_eq_zero.2 fun b hb => ?_).trans hj
  ext a
  rw [interpolant, coeff_coeff_bivariateOf, hcoeffs, coeff_zero]
  split_ifs
  · simp only [coeffsOf]
    split_ifs with h
    · exact absurd (mem_filter.1 h).2 (not_le.2 hb)
    · rfl
  · rfl

/-! ### Simplicity of the roots -/

omit [Fintype ι] [DecidableEq F] in
/-- If `(a₀, b₀)` maximizes the `(1, d)`-weighted degree of `S` and `b₀` is largest among those
maximizers, then `X ^ a₀ * Y ^ (b₀ + 1)` has a nonzero coefficient in `(Y - C P) * S`. -/
private theorem coeff_X_sub_C_mul_ne_zero {d a₀ b₀ : ℕ} {P : F[X]} (hP : P.natDegree ≤ d)
    {S : F[X][Y]} (ha₀ : (S.coeff b₀).coeff a₀ ≠ 0)
    (hle : ∀ a b, (S.coeff b).coeff a ≠ 0 → a + d * b ≤ a₀ + d * b₀)
    (hbmax : ∀ a b, (S.coeff b).coeff a ≠ 0 → a + d * b = a₀ + d * b₀ → b ≤ b₀) :
    (((Y - C P) * S).coeff (b₀ + 1)).coeff a₀ ≠ 0 := by
  rw [mul_comm, coeff_mul_X_sub_C, coeff_sub, mul_comm, coeff_mul]
  have hzero : ∑ x ∈ antidiagonal a₀, P.coeff x.1 * (S.coeff (b₀ + 1)).coeff x.2 = 0 := by
    refine sum_eq_zero fun ⟨i, j⟩ hij => ?_
    rw [mem_antidiagonal] at hij
    by_cases hPi : P.coeff i = 0
    · rw [hPi, zero_mul]
    by_cases hSj : (S.coeff (b₀ + 1)).coeff j = 0
    · rw [hSj, mul_zero]
    exfalso
    have hi : i ≤ d := (le_natDegree_of_ne_zero hPi).trans hP
    have hj := hle j (b₀ + 1) hSj
    have hjM : j + d * (b₀ + 1) = a₀ + d * b₀ := by nlinarith
    have := hbmax j (b₀ + 1) hSj hjM
    omega
  rw [hzero, sub_zero]
  exact ha₀

omit [Fintype ι] [DecidableEq F] in
/-- **Division by `Y - P` lowers the weighted degree bound by `d`.** If `P` has degree at most `d`
and `(Y - P) * S` has `(1, d)`-weighted degree at most `D`, then every monomial `X ^ a * Y ^ b` of
`S` has `a + d * (b + 1) ≤ D`. -/
theorem add_mul_add_one_le_of_mul {d D : ℕ} {P : F[X]} (hP : P.natDegree ≤ d) {S : F[X][Y]}
    (h : WeightedDegreeLE d D ((Y - C P) * S)) :
    ∀ a b, (S.coeff b).coeff a ≠ 0 → a + d * (b + 1) ≤ D := by
  classical
  -- the monomials of `S`
  let supp : Finset (ℕ × ℕ) := S.support.biUnion fun b => (S.coeff b).support.image (·, b)
  have hmem : ∀ a b, (S.coeff b).coeff a ≠ 0 ↔ (a, b) ∈ supp := by
    intro a b
    simp only [supp, mem_biUnion, mem_image, mem_support_iff, Prod.mk.injEq]
    constructor
    · intro hab
      exact ⟨b, fun h => hab (by rw [h, coeff_zero]), a, hab, rfl, rfl⟩
    · rintro ⟨b', -, a', ha', rfl, rfl⟩
      exact ha'
  intro a b hab
  have hne : supp.Nonempty := ⟨(a, b), (hmem a b).1 hab⟩
  -- the largest weighted degree, and the largest `Y`-degree attaining it
  set M₀ := supp.sup' hne fun p => p.1 + d * p.2
  have hle : ∀ p ∈ supp, p.1 + d * p.2 ≤ M₀ := fun p hp => le_sup' (fun p => p.1 + d * p.2) hp
  have htop : (supp.filter fun p => p.1 + d * p.2 = M₀).Nonempty := by
    obtain ⟨p, hp, hpeq⟩ := exists_mem_eq_sup' hne fun p => p.1 + d * p.2
    exact ⟨p, mem_filter.2 ⟨hp, hpeq.symm⟩⟩
  obtain ⟨⟨a₀, b₀⟩, hp₀, hb₀⟩ := exists_mem_eq_sup' htop Prod.snd
  obtain ⟨hp₀, hM₀⟩ := mem_filter.1 hp₀
  have hbmax : ∀ p ∈ supp, p.1 + d * p.2 = M₀ → p.2 ≤ b₀ := fun p hp hpM => by
    rw [show b₀ = (a₀, b₀).2 from rfl, ← hb₀]
    exact le_sup' Prod.snd (mem_filter.2 ⟨hp, hpM⟩)
  simp only at hM₀
  have hcoeff := coeff_X_sub_C_mul_ne_zero hP ((hmem a₀ b₀).2 hp₀)
    (fun a' b' hab' => hM₀ ▸ hle (a', b') ((hmem a' b').1 hab'))
    (fun a' b' hab' hM => hbmax (a', b') ((hmem a' b').1 hab') (hM.trans hM₀))
  have hD := h a₀ (b₀ + 1) hcoeff
  have hab' := hle (a, b) ((hmem a b).1 hab)
  simp only at hab'
  nlinarith

omit [Fintype ι] [DecidableEq F] in
/-- The value at `(x, y)` of `(Y - P) * S`. -/
private theorem evalEval_X_sub_C_mul (P : F[X]) (S : F[X][Y]) (x y : F) :
    ((Y - C P) * S).evalEval x y = (y - P.eval x) * S.evalEval x y := by
  rw [evalEval_mul, evalEval_sub, evalEval_X, evalEval_C]

/-- **Large agreement gives simple roots.** Let `Q` be a Sudan interpolant of least `Y`-degree for
weight `d` and weighted degree `D`, with distinct points. If `P` has degree at most `d` and agrees
with the received word at more than `D` points, then `Q = (Y - P) * S` where `S(X, P(X))` is a
nonzero polynomial of degree at most `D - d`. -/
theorem exists_eq_mul_eval_ne_zero {α w : ι → F} {d D : ℕ} (hα : Function.Injective α)
    {Q : F[X][Y]} (hQ : IsInterpolant α w d D Q)
    (hmin : ∀ Q', IsInterpolant α w d D Q' → Q.natDegree ≤ Q'.natDegree) {P : F[X]}
    (hP : P.natDegree ≤ d) (hagree : D < #{i | P.eval (α i) = w i}) :
    ∃ S : F[X][Y], Q = (Y - C P) * S ∧ S.eval P ≠ 0 ∧ (S.eval P).natDegree ≤ D - d := by
  obtain ⟨S, rfl⟩ := hQ.X_sub_C_dvd hα hP hagree
  have hwd := add_mul_add_one_le_of_mul hP hQ.weightedDegree_le
  have hSwd : WeightedDegreeLE d (D - d) S := fun a b hab => by
    have := hwd a b hab
    rw [mul_add, mul_one] at this
    omega
  have hS0 : S ≠ 0 := fun h => hQ.ne_zero (by rw [h, mul_zero])
  refine ⟨S, rfl, fun hSP => ?_, hSwd.natDegree_eval_le hP⟩
  -- otherwise `S` is an interpolant of smaller `Y`-degree
  obtain ⟨S₂, rfl⟩ := dvd_iff_isRoot.2 hSP
  have hS : IsInterpolant α w d D ((Y - C P) * S₂) := by
    refine ⟨hS0, fun a b hab => ?_, fun i => ?_⟩
    · have := hwd a b hab
      nlinarith
    · have h := hQ.evalEval_eq_zero i
      rw [evalEval_X_sub_C_mul, evalEval_X_sub_C_mul] at h
      rw [evalEval_X_sub_C_mul]
      by_cases hi : w i - P.eval (α i) = 0
      · rw [hi, zero_mul]
      · have h' := mul_eq_zero.1 h
        rcases h' with h' | h'
        · exact absurd h' hi
        · exact h'
  have hmon : (Y - C P).Monic := monic_X_sub_C P
  have := hmin _ hS
  rw [hmon.natDegree_mul' (by simpa using hS0), natDegree_X_sub_C] at this
  omega

end Cslib.Code.Sudan
