/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Shifting the variables of a multivariate polynomial

`MvPolynomial.shift a` is the substitution `X i ↦ X i + C (a i)`. The point `a` may have
coordinates in an algebra `A` over the coefficient ring `R`, so that a polynomial over a field can
be shifted by a point with polynomial coordinates; the result is a polynomial over `A`.

## Main definitions

* `MvPolynomial.shift`: the algebra homomorphism `f ↦ f (X + a)`.

## Main results

* `MvPolynomial.eval_shift`: evaluating a shift evaluates at the translated point.
* `MvPolynomial.coeff_zero_shift`: the constant coefficient of a shift is the value at the point.
* `MvPolynomial.pderiv_shift`: shifting commutes with partial derivatives.
* `MvPolynomial.degreeOf_shift_le`: shifting does not increase the degree in a variable.
* `MvPolynomial.degreeOf_coeff_shift_le`: a degree bound for the coefficients of a shift by a
  point with polynomial coordinates.
* `MvPolynomial.natDegree_coeff_shift_le`: the same for a point whose coordinates are univariate
  polynomials.
* `MvPolynomial.shift_injective`: shifting is injective when `R → A` is.
* `MvPolynomial.aeval_X_eq_map`: substituting the variables over an algebra is a base change.
* `MvPolynomial.map_shift`: shifting commutes with a change of the ring of the point.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R A B : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The shift `f ↦ f (X + a)` by a point `a` with coordinates in an `R`-algebra. -/
noncomputable def shift (a : σ → A) : MvPolynomial σ R →ₐ[R] MvPolynomial σ A :=
  aeval fun i => X i + C (a i)

theorem shift_X (a : σ → A) (i : σ) : shift a (X i : MvPolynomial σ R) = X i + C (a i) :=
  aeval_X _ i

/-- Shifting commutes with a homomorphism applied to the coordinates of the point. -/
theorem map_shift [CommSemiring B] [Algebra R B] (φ : A →ₐ[R] B) (a : σ → A)
    (f : MvPolynomial σ R) : map (φ : A →+* B) (shift a f) = shift (fun i => φ (a i)) f := by
  have h := comp_aeval (R := R) (f := fun i => (X i + C (a i) : MvPolynomial σ A)) (mapAlgHom φ)
  simpa [shift] using DFunLike.congr_fun h f

/-- Evaluating a shifted polynomial at `b` evaluates the polynomial at `b + a`. -/
theorem eval_shift (a b : σ → R) (f : MvPolynomial σ R) :
    eval b (shift a f) = eval (fun i => b i + a i) f := by
  have h := DFunLike.congr_fun (comp_aeval (R := R)
    (f := fun i => (X i + C (a i) : MvPolynomial σ R)) (aeval b : MvPolynomial σ R →ₐ[R] R)) f
  simpa [shift, aeval_eq_eval] using h

/-- The constant coefficient of a shifted polynomial is the value of the polynomial at the
point. -/
theorem coeff_zero_shift (a : σ → R) (f : MvPolynomial σ R) : (shift a f).coeff 0 = eval a f := by
  have h := eval_shift a 0 f
  rwa [eval_zero, constantCoeff_eq,
    show (fun i => (0 : σ → R) i + a i) = a from funext fun i => zero_add _] at h

/-- Shifting commutes with partial derivatives. -/
theorem pderiv_shift (a : σ → A) (i : σ) (f : MvPolynomial σ R) :
    pderiv i (shift a f) = shift a (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C r => simp [shift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, map_add, shift_X, Derivation.leibniz, hp, pderiv_X, pderiv_C, smul_eq_mul,
      Pi.single_apply]
    split_ifs <;> simp

/-- A polynomial of degree at most `δ` in each of its finitely many variables has total degree
at most `δ` times the number of variables. -/
theorem totalDegree_le_card_mul_of_degreeOf_le [Fintype σ] {f : MvPolynomial σ R} {δ : ℕ}
    (hdeg : ∀ i, f.degreeOf i ≤ δ) : f.totalDegree ≤ Fintype.card σ * δ :=
  Finset.sup_le fun m hm =>
    calc (m.sum fun _ e => e) ≤ ∑ j ∈ m.support, δ :=
          Finset.sum_le_sum fun j _ => (monomial_le_degreeOf j hm).trans (hdeg j)
      _ ≤ Fintype.card σ * δ := by
          rw [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)

/-- A polynomial of degree at most one in each of its finitely many variables has total degree
at most the number of variables. -/
theorem totalDegree_le_card_of_degreeOf_le_one [Fintype σ] {f : MvPolynomial σ R}
    (hmul : ∀ i, f.degreeOf i ≤ 1) : f.totalDegree ≤ Fintype.card σ :=
  (totalDegree_le_card_mul_of_degreeOf_le hmul).trans_eq (mul_one _)

/-- Substituting the variables of the polynomial ring over an algebra is a base change. -/
theorem aeval_X_eq_map (p : MvPolynomial σ R) :
    aeval (fun i => (X i : MvPolynomial σ A)) p = map (algebraMap R A) p := by
  rw [map_eq_eval₂Hom_C_comp, aeval_eq_eval₂Hom]
  rfl

/-- Shifting does not increase the degree in a variable. -/
theorem degreeOf_shift_le (a : σ → A) (f : MvPolynomial σ R) (i : σ) :
    (shift a f).degreeOf i ≤ f.degreeOf i := by
  classical
  rw [shift, aeval_def, eval₂_eq]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [algebraMap_apply, degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have hle : ∀ j ∈ m.support,
      degreeOf i ((X j + C (a j) : MvPolynomial σ A) ^ m j) ≤ if j = i then m j else 0 := by
    intro j _
    refine (degreeOf_pow_le _ _ _).trans ?_
    have h1 : degreeOf i (X j + C (a j) : MvPolynomial σ A) ≤ degreeOf i (X j : MvPolynomial σ A) :=
      (degreeOf_add_le _ _ _).trans (by rw [degreeOf_C, max_eq_left (Nat.zero_le _)])
    split_ifs with h
    · have hX : degreeOf i (X j : MvPolynomial σ A) ≤ 1 := degreeOf_le_iff.2 fun d hd => by
        rw [Finset.mem_singleton.1 (support_monomial_subset hd), Finsupp.single_apply]
        split_ifs
        exact le_rfl
      exact (Nat.mul_le_mul_left _ (h1.trans hX)).trans_eq (mul_one _)
    · rw [Nat.le_zero.1 (h1.trans_eq (degreeOf_X_of_ne (Ne.symm h))), mul_zero]
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_ite_eq' m.support i]
  split_ifs
  · exact monomial_le_degreeOf i hm
  · exact Nat.zero_le _

end CommSemiring

section Coefficients

variable [CommSemiring R] {τ : Type*}

/-- A bound for the coefficients of a shift in terms of a degree-like function `D` on the ring of
the point: if `D` is at most `d` on the coordinates of the point, it is at most
`f.totalDegree * d` on every coefficient of the shifted polynomial. -/
private theorem degree_coeff_shift_le {A : Type*} [CommSemiring A] [Algebra R A] (D : A → ℕ)
    (h0 : D 0 = 0) (h1 : D 1 = 0) (hadd : ∀ x y, D (x + y) ≤ max (D x) (D y))
    (hmul : ∀ x y, D (x * y) ≤ D x + D y) (hR : ∀ r, D (algebraMap R A r) = 0) (a : σ → A)
    (f : MvPolynomial σ R) {d : ℕ} (ha : ∀ j, D (a j) ≤ d) (m : σ →₀ ℕ) :
    D ((shift a f).coeff m) ≤ f.totalDegree * d := by
  classical
  have hmulc : ∀ {P Q : MvPolynomial σ A} {B₁ B₂ : ℕ}, (∀ m, D (P.coeff m) ≤ B₁) →
      (∀ m, D (Q.coeff m) ≤ B₂) → ∀ m, D ((P * Q).coeff m) ≤ B₁ + B₂ := by
    intro P Q B₁ B₂ hP hQ m
    rw [coeff_mul]
    exact Finset.sum_induction _ (D · ≤ B₁ + B₂) (fun x y hx hy => (hadd x y).trans (max_le hx hy))
      (h0.le.trans (Nat.zero_le _)) fun x _ => (hmul _ _).trans (add_le_add (hP _) (hQ _))
  have hone : ∀ m : σ →₀ ℕ, D ((1 : MvPolynomial σ A).coeff m) ≤ 0 := fun m => by
    rw [coeff_one]
    split_ifs
    exacts [h1.le, h0.le]
  have hX : ∀ (j : σ) (m : σ →₀ ℕ), D ((X j + C (a j) : MvPolynomial σ A).coeff m) ≤ d :=
    fun j m => by
    rw [show (X j + C (a j) : MvPolynomial σ A).coeff m =
      (X j : MvPolynomial σ A).coeff m + (C (a j)).coeff m from rfl, coeff_X, coeff_C]
    refine (hadd _ _).trans (max_le ?_ ?_) <;> split_ifs
    exacts [h1.le.trans (Nat.zero_le _), h0.le.trans (Nat.zero_le _), ha j,
      h0.le.trans (Nat.zero_le _)]
  have hpow : ∀ (j : σ) (e : ℕ) (m : σ →₀ ℕ),
      D (((X j + C (a j) : MvPolynomial σ A) ^ e).coeff m) ≤ e * d := by
    intro j e
    induction e with
    | zero => intro m; rw [pow_zero, zero_mul]; exact hone m
    | succ e ih => intro m; rw [pow_succ, Nat.succ_mul]; exact hmulc ih (hX j) m
  have hprod : ∀ (s : Finset σ) (e : σ → ℕ) (m : σ →₀ ℕ),
      D ((∏ j ∈ s, (X j + C (a j) : MvPolynomial σ A) ^ e j).coeff m) ≤ (∑ j ∈ s, e j) * d := by
    intro s e
    induction s using Finset.induction_on with
    | empty => intro m; rw [Finset.prod_empty, Finset.sum_empty, zero_mul]; exact hone m
    | insert j s hj ih =>
      intro m
      rw [Finset.prod_insert hj, Finset.sum_insert hj, add_mul]
      exact hmulc (hpow j _) ih m
  rw [shift, aeval_def, eval₂_eq, coeff_sum]
  refine Finset.sum_induction _ (D · ≤ f.totalDegree * d)
    (fun x y hx hy => (hadd x y).trans (max_le hx hy)) (h0.le.trans (Nat.zero_le _))
    fun m' hm' => ?_
  rw [algebraMap_apply, coeff_C_mul]
  refine (hmul _ _).trans ?_
  rw [hR, zero_add]
  exact (hprod _ _ _).trans (Nat.mul_le_mul_right _ (le_totalDegree hm'))

/-- When the point has polynomial coordinates of degree at most `d` in a variable `i`, every
coefficient of the shifted polynomial has degree at most `f.totalDegree * d` in `i`. -/
theorem degreeOf_coeff_shift_le (a : σ → MvPolynomial τ R) (f : MvPolynomial σ R) (i : τ) {d : ℕ}
    (ha : ∀ j, (a j).degreeOf i ≤ d) (m : σ →₀ ℕ) :
    ((shift a f).coeff m).degreeOf i ≤ f.totalDegree * d :=
  degree_coeff_shift_le (A := MvPolynomial τ R) (degreeOf i) (degreeOf_zero i) (degreeOf_one i)
    (degreeOf_add_le i) (degreeOf_mul_le i) (fun r => by rw [algebraMap_eq, degreeOf_C]) a f ha m

/-- When the point has coordinates that are univariate polynomials of degree at most `d`, every
coefficient of the shifted polynomial has degree at most `f.totalDegree * d`. -/
theorem natDegree_coeff_shift_le {A : Type*} [CommSemiring A] [Algebra R A] (a : σ → Polynomial A)
    (f : MvPolynomial σ R) {d : ℕ} (ha : ∀ j, (a j).natDegree ≤ d) (m : σ →₀ ℕ) :
    ((shift a f).coeff m).natDegree ≤ f.totalDegree * d :=
  degree_coeff_shift_le (A := Polynomial A) Polynomial.natDegree Polynomial.natDegree_zero
    Polynomial.natDegree_one Polynomial.natDegree_add_le (fun _ _ => Polynomial.natDegree_mul_le)
    (fun r => (congrArg _ (Polynomial.algebraMap_apply r)).trans (Polynomial.natDegree_C _))
    a f ha m

end Coefficients

section CommRing

variable [CommRing R] [CommRing A] [Algebra R A]

/-- Shifting by `-a` undoes shifting by `a`. -/
theorem shift_neg_shift (a : σ → R) (f : MvPolynomial σ R) :
    shift (fun i => -a i) (shift a f) = f := by
  rw [shift, shift, ← AlgHom.comp_apply, comp_aeval]
  simpa using aeval_X_left_apply f

/-- Shifting is injective when the coefficient ring embeds into the ring of the point. -/
theorem shift_injective (hRA : Function.Injective (algebraMap R A)) (a : σ → A) :
    Function.Injective (shift a : MvPolynomial σ R → MvPolynomial σ A) := by
  have h : ((aeval fun i => X i - C (a i) : MvPolynomial σ A →ₐ[A] MvPolynomial σ A).restrictScalars
      R).comp (shift a) = aeval (fun i => (X i : MvPolynomial σ A)) := by
    rw [shift, comp_aeval]
    congr 1
    funext i
    simp
  have hinj : Function.Injective (aeval (fun i => (X i : MvPolynomial σ A)) :
      MvPolynomial σ R → MvPolynomial σ A) := by
    rw [show (aeval (fun i => (X i : MvPolynomial σ A)) : MvPolynomial σ R → MvPolynomial σ A) =
      map (algebraMap R A) from funext aeval_X_eq_map]
    exact map_injective _ hRA
  exact Function.Injective.of_comp (f := (aeval fun i => X i - C (a i) :
    MvPolynomial σ A →ₐ[A] MvPolynomial σ A)) (by rw [← h] at hinj; exact hinj)

end CommRing

end MvPolynomial
