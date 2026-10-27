/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Mobius
public import Complexity.Foundations.Data.MvPolynomial.CoefficientDegree
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-!
# Affine Taylor substitutions and restricted-subset jet coefficients

Given scalar replacement rows `P f v : ι → Polynomial A` for multivariate polynomial factors
`Φ f : MvPolynomial (κ f) A` over any commutative ring `A`, equation (3.3) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] forms the univariate sum
`replacedSum s Φ P = ∑ x : ι → Bool, ∏ f ∈ s, Φ_f(⟨P_{f,v}(T), x⟩)` in `Polynomial A`.

In §3.4 (equations (3.7)–(3.10), p. 24), fixing an evaluation node `t : A` and an original Boolean
assignment `x : ι → Bool`, each factor input is split into its scalar baseline at `t` plus formal
variables `X i` multiplied by the scalar Taylor corrections
`taylor t (P f v i) - C ((P f v i).eval t)` (`Cslib.AffineTaylor.affineInput`). Because every
scalar Taylor correction has zero constant coefficient
(`Cslib.AffineTaylor.coeff_zero_taylor_sub_C_eval`), the `j`-th outer Taylor coefficient of the
full factor product `Cslib.AffineTaylor.factorProduct` has multivariate total degree at most `j`
(`Cslib.AffineTaylor.totalDegree_coeff_factorProduct_le`). Evaluating the formal variables
diagonally at `x` recovers `Polynomial.taylor t (replacedSum s Φ P)`
(`Cslib.AffineTaylor.taylor_replacedSum_eq_sum_map_eval`), and Boolean Möbius reconstruction then
expresses every jet coefficient of order `j ≤ q` through restricted sums with `G_x` still indexed
by the original assignment `x`
(`Cslib.AffineTaylor.coeff_taylor_replacedSum_eq_restricted_subsets`).

No quotient ring truncation, Hermite interpolation, or enumeration complexity claim is made here.

## Main definitions

* `Cslib.AffineTaylor.affineInput`: the affine/Taylor input polynomial in
  `Polynomial (MvPolynomial ι A)` (equation (3.7)).
* `Cslib.AffineTaylor.affineFactor`: a single multivariate factor evaluated at `affineInput`.
* `Cslib.AffineTaylor.factorProduct`: the full affine/Taylor factor product `G_x(X, z)` over
  `f ∈ s` (equation (3.8)).
* `Cslib.AffineTaylor.replacedSum`: the scalar polynomial `H(T)` summed over the Boolean cube
  (equation (3.3)).

## Main results

* `Cslib.AffineTaylor.coeff_zero_taylor_sub_C_eval`,
  `Cslib.AffineTaylor.X_dvd_taylor_sub_C_eval`: every scalar Taylor correction has zero constant
  term and is divisible by `X`.
* `Cslib.AffineTaylor.totalDegree_coeff_affineInput_le`,
  `Cslib.AffineTaylor.totalDegree_coeff_affineFactor_le`,
  `Cslib.AffineTaylor.totalDegree_coeff_factorProduct_le`: multivariate degree bound `≤ j` on the
  `j`-th Taylor coefficient (equation (3.9)).
* `Cslib.AffineTaylor.map_eval_self_factorProduct`,
  `Cslib.AffineTaylor.taylor_replacedSum_eq_sum_map_eval`: diagonal evaluation at `x` recovers the
  Taylor shift `H(t + z)` (equation (3.8)).
* `Cslib.AffineTaylor.coeff_taylor_replacedSum_eq_restricted_subsets`: exact restricted-subset
  identity for `[z^j] H(t + z)` whenever `j ≤ q` (equations (3.9)–(3.10)).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.1 equation (3.3) and
  §3.4 equations (3.7)–(3.10), p. 24.
-/

public section

open scoped BigOperators
open Finset Cslib.BitString

namespace Cslib.AffineTaylor

variable {A : Type*} [CommRing A]

/-! ### Scalar Taylor corrections -/

/-- Subtracting `p.eval t` from the Taylor shift `Polynomial.taylor t p` kills the constant
coefficient (`[z^0] (p(t + z) - p(t)) = 0`). -/
theorem coeff_zero_taylor_sub_C_eval (t : A) (p : Polynomial A) :
    (Polynomial.taylor t p - Polynomial.C (p.eval t)).coeff 0 = 0 := by
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff_zero, Polynomial.coeff_C_zero, sub_self]

/-- Every scalar Taylor correction `p(t + z) - p(t)` is divisible by the outer variable `X`. -/
theorem X_dvd_taylor_sub_C_eval (t : A) (p : Polynomial A) :
    Polynomial.X ∣ Polynomial.taylor t p - Polynomial.C (p.eval t) :=
  Polynomial.X_dvd_iff.mpr (coeff_zero_taylor_sub_C_eval t p)

/-! ### Affine/Taylor inputs and factor products -/

section Substitutions

variable {ι F : Type*} {κ : F → Type*}

/-- The affine/Taylor input polynomial `⟨row(t), x⟩ + ⟨Δrow(z), X⟩` in
`Polynomial (MvPolynomial ι A)` (equation (3.7) of [OpenAI2026ETH]). The outer indeterminate is
the Taylor variable `z`, the constant baseline captures `x` at node `t`, and each formal variable
`X i` carries the zero-constant scalar correction `taylor t (row i) - C ((row i).eval t)`. -/
@[expose] noncomputable def affineInput [Fintype ι]
    (row : ι → Polynomial A) (t : A) (x : ι → Bool) : Polynomial (MvPolynomial ι A) :=
  Polynomial.C (MvPolynomial.C (∑ i : ι, (row i).eval t * bitVal A (x i))) +
    ∑ i : ι, Polynomial.C (MvPolynomial.X i) *
      (Polynomial.taylor t (row i) - Polynomial.C ((row i).eval t)).map MvPolynomial.C

/-- A single multivariate factor `Φ` evaluated at the affine/Taylor input rows for node `t` and
Boolean assignment `x`. -/
@[expose] noncomputable def affineFactor [Fintype ι] {σ : Type*}
    (Φ : MvPolynomial σ A) (rows : σ → ι → Polynomial A) (t : A) (x : ι → Bool) :
    Polynomial (MvPolynomial ι A) :=
  MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C) (fun v => affineInput (rows v) t x) Φ

/-- The full affine/Taylor factor product `G_x(X, z)` over all factors `f ∈ s`
(equation (3.8) of [OpenAI2026ETH]). -/
@[expose] noncomputable def factorProduct [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) : Polynomial (MvPolynomial ι A) :=
  ∏ f ∈ s, affineFactor (Φ f) (P f) t x

open Classical in
/-- The univariate polynomial `H(T) = ∑ x, ∏ f ∈ s, Φ_f(⟨P_{f,v}(T), x⟩)` summed over all Boolean
assignments `x : ι → Bool` (equation (3.3) of [OpenAI2026ETH]). -/
@[expose] noncomputable def replacedSum [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A) :
    Polynomial A :=
  ∑ x : ι → Bool, ∏ f ∈ s,
    MvPolynomial.aeval (fun v => ∑ i : ι, P f v i * Polynomial.C (bitVal A (x i))) (Φ f)

@[simp]
theorem factorProduct_empty [Fintype ι]
    (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) :
    factorProduct (∅ : Finset F) Φ P t x = 1 :=
  Finset.prod_empty

@[simp]
theorem replacedSum_empty [Fintype ι]
    (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A) :
    replacedSum (∅ : Finset F) Φ P = (2 : Polynomial A) ^ Fintype.card ι := by
  classical
  simp only [replacedSum, Finset.prod_empty, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

/-- `affineInput` depends on the Boolean assignment `x` only through its scalar baseline
`∑ i, (row i).eval t * bitVal A (x i)` at node `t`. -/
theorem affineInput_congr_baseline [Fintype ι]
    {row : ι → Polynomial A} {t : A} {x x' : ι → Bool}
    (h : ∑ i : ι, (row i).eval t * bitVal A (x i) = ∑ i : ι, (row i).eval t * bitVal A (x' i)) :
    affineInput row t x = affineInput row t x' := by
  simp only [affineInput, h]

/-- `affineFactor` depends on `x` only through the scalar baselines of its rows at node `t`. -/
theorem affineFactor_congr_baseline [Fintype ι] {σ : Type*}
    (Φ : MvPolynomial σ A) {rows : σ → ι → Polynomial A} {t : A} {x x' : ι → Bool}
    (h : ∀ v, ∑ i : ι, (rows v i).eval t * bitVal A (x i) =
      ∑ i : ι, (rows v i).eval t * bitVal A (x' i)) :
    affineFactor Φ rows t x = affineFactor Φ rows t x' := by
  simp only [affineFactor]
  congr 1
  funext v
  exact affineInput_congr_baseline (h v)

/-! ### Coefficient total-degree bounds -/

/-- Every outer Taylor coefficient `j` of `affineInput` has multivariate total degree at most `j`
in the formal variables `X`. -/
theorem totalDegree_coeff_affineInput_le [Fintype ι]
    (row : ι → Polynomial A) (t : A) (x : ι → Bool) (j : ℕ) :
    ((affineInput row t x).coeff j).totalDegree ≤ j := by
  rw [affineInput, Polynomial.coeff_add]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · by_cases hj : j = 0
    · subst j
      simp only [Polynomial.coeff_C_zero, MvPolynomial.totalDegree_C, le_refl]
    · rw [Polynomial.coeff_C_of_ne_zero hj]
      exact Nat.zero_le j
  · rw [Polynomial.finsetSum_coeff]
    refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
    exact MvPolynomial.totalDegree_coeff_X_mul_map_le i _ (coeff_zero_taylor_sub_C_eval t (row i)) j

/-- Every outer Taylor coefficient `j` of `affineFactor` has multivariate total degree at most `j`
in the formal variables `X`. -/
theorem totalDegree_coeff_affineFactor_le [Fintype ι] {σ : Type*}
    (Φ : MvPolynomial σ A) (rows : σ → ι → Polynomial A) (t : A) (x : ι → Bool) (j : ℕ) :
    ((affineFactor Φ rows t x).coeff j).totalDegree ≤ j :=
  MvPolynomial.totalDegree_coeff_eval₂_le Φ (fun v => affineInput (rows v) t x)
    (fun v k => totalDegree_coeff_affineInput_le (rows v) t x k) j

/-- Every outer Taylor coefficient `j` of the full factor product `factorProduct` has multivariate
total degree at most `j` in the formal variables `X` (equation (3.9) of [OpenAI2026ETH]). -/
theorem totalDegree_coeff_factorProduct_le [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) (j : ℕ) :
    ((factorProduct s Φ P t x).coeff j).totalDegree ≤ j := by
  suffices h : ∀ k, ((factorProduct s Φ P t x).coeff k).totalDegree ≤ k from h j
  unfold factorProduct
  induction s using Finset.cons_induction with
  | empty =>
      intro k
      have h1 := MvPolynomial.totalDegree_coeff_eval₂_le (ι := ι) (1 : MvPolynomial Empty A)
        Empty.elim (fun v => Empty.elim v) k
      rwa [Finset.prod_empty,
        ← MvPolynomial.eval₂_one (Polynomial.C.comp MvPolynomial.C) Empty.elim]
  | cons f s hf ih =>
      intro k
      rw [Finset.prod_cons]
      let Q : Bool → Polynomial (MvPolynomial ι A) :=
        fun b => cond b (affineFactor (Φ f) (P f) t x) (∏ g ∈ s, affineFactor (Φ g) (P g) t x)
      have hmul := MvPolynomial.totalDegree_coeff_eval₂_le
        (MvPolynomial.X true * MvPolynomial.X false : MvPolynomial Bool A) Q
        (fun b m => by
          cases b
          · exact ih m
          · exact totalDegree_coeff_affineFactor_le _ _ _ _ m) k
      rwa [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X] at hmul

/-! ### Evaluation in formal variables and diagonal Taylor shift -/

/-- Evaluating the formal variables `X` of `affineInput` at any `y : ι → A` yields the scalar
polynomial with baseline at `x` and Taylor corrections weighted by `y`. -/
theorem map_eval_affineInput [Fintype ι]
    (row : ι → Polynomial A) (t : A) (x : ι → Bool) (y : ι → A) :
    (affineInput row t x).map (MvPolynomial.eval y) =
      Polynomial.C (∑ i : ι, (row i).eval t * bitVal A (x i)) +
        ∑ i : ι, Polynomial.C (y i) *
          (Polynomial.taylor t (row i) - Polynomial.C ((row i).eval t)) := by
  rw [affineInput, Polynomial.map_add, Polynomial.map_C, MvPolynomial.eval_C, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.eval_X, Polynomial.map_map]
  have hcomp : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id A := by
    ext a
    exact MvPolynomial.eval_C a
  rw [hcomp, Polynomial.map_id]

/-- Evaluating the formal variables `X` of `affineInput` diagonally at `x` cancels the baseline
subtraction and produces the Taylor shift of `∑ i, row i * C (bitVal A (x i))` at `t`. -/
theorem map_eval_self_affineInput [Fintype ι]
    (row : ι → Polynomial A) (t : A) (x : ι → Bool) :
    (affineInput row t x).map (MvPolynomial.eval fun i => bitVal A (x i)) =
      Polynomial.taylor t (∑ i : ι, row i * Polynomial.C (bitVal A (x i))) := by
  rw [map_eval_affineInput, map_sum (Polynomial.taylor t), map_sum Polynomial.C]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.taylor_mul, Polynomial.taylor_C, map_mul]
  ring

/-- Evaluating the formal variables `X` of `affineFactor` at `y : ι → A` pushes inside the factor
evaluation. -/
theorem map_eval_affineFactor [Fintype ι] {σ : Type*}
    (Φ : MvPolynomial σ A) (rows : σ → ι → Polynomial A)
    (t : A) (x : ι → Bool) (y : ι → A) :
    (affineFactor Φ rows t x).map (MvPolynomial.eval y) =
      MvPolynomial.aeval (fun v => (affineInput (rows v) t x).map (MvPolynomial.eval y)) Φ := by
  unfold affineFactor
  change Polynomial.mapRingHom (MvPolynomial.eval y) _ = _
  rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
  congr 1
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
    MvPolynomial.eval_C, Polynomial.algebraMap_eq]

/-- Evaluating the formal variables `X` of `factorProduct` at `y : ι → A` factors over `s`. -/
theorem map_eval_factorProduct [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) (y : ι → A) :
    (factorProduct s Φ P t x).map (MvPolynomial.eval y) =
      ∏ f ∈ s, (affineFactor (Φ f) (P f) t x).map (MvPolynomial.eval y) := by
  unfold factorProduct
  simpa only [Polynomial.coe_mapRingHom] using
    map_prod (Polynomial.mapRingHom (MvPolynomial.eval y)) (fun f => affineFactor (Φ f) (P f) t x) s

/-- Evaluating the `j`-th coefficient of `factorProduct` at `y : ι → A` agrees with taking the
`j`-th coefficient after substituting `X ↦ y` into each factor. -/
theorem eval_coeff_factorProduct [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) (y : ι → A) (j : ℕ) :
    MvPolynomial.eval y ((factorProduct s Φ P t x).coeff j) =
      (∏ f ∈ s, (affineFactor (Φ f) (P f) t x).map (MvPolynomial.eval y)).coeff j := by
  rw [← Polynomial.coeff_map, map_eval_factorProduct]

/-- Diagonal formal evaluation of `affineFactor` at `x` equals the Taylor shift of the scalar
factor polynomial at `t`. -/
theorem map_eval_self_affineFactor [Fintype ι] {σ : Type*}
    (Φ : MvPolynomial σ A) (rows : σ → ι → Polynomial A)
    (t : A) (x : ι → Bool) :
    (affineFactor Φ rows t x).map (MvPolynomial.eval fun i => bitVal A (x i)) =
      Polynomial.taylor t
        (MvPolynomial.aeval (fun v => ∑ i : ι, rows v i * Polynomial.C (bitVal A (x i))) Φ) := by
  rw [map_eval_affineFactor]
  have hcomp := MvPolynomial.comp_aeval_apply
    (fun v => ∑ i : ι, rows v i * Polynomial.C (bitVal A (x i)))
    (Polynomial.taylorAlgHom t) Φ
  simp only [Polynomial.taylorAlgHom_apply, ← map_eval_self_affineInput] at hcomp
  exact hcomp.symm

/-- Diagonal formal evaluation of `factorProduct` at `x` equals the Taylor shift of the scalar
product of factors at `t` (equation (3.8) of [OpenAI2026ETH]). -/
theorem map_eval_self_factorProduct [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (x : ι → Bool) :
    (factorProduct s Φ P t x).map (MvPolynomial.eval fun i => bitVal A (x i)) =
      Polynomial.taylor t (∏ f ∈ s,
        MvPolynomial.aeval (fun v => ∑ i : ι, P f v i * Polynomial.C (bitVal A (x i))) (Φ f)) := by
  rw [map_eval_factorProduct]
  change _ = (Polynomial.taylorAlgHom t) _
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [Polynomial.taylorAlgHom_apply, map_eval_self_affineFactor]

open Classical in
/-- Summing the diagonal formal evaluations of `factorProduct` over the Boolean cube yields the
Taylor shift `Polynomial.taylor t (replacedSum s Φ P)` (`∑_x G_x(x, z) = H(t + z)`, equation (3.8)
of [OpenAI2026ETH]). -/
theorem taylor_replacedSum_eq_sum_map_eval [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) :
    Polynomial.taylor t (replacedSum s Φ P) =
      ∑ x : ι → Bool,
        (factorProduct s Φ P t x).map (MvPolynomial.eval fun i => bitVal A (x i)) := by
  rw [replacedSum, map_sum (Polynomial.taylor t)]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (map_eval_self_factorProduct s Φ P t x).symm

open Classical in
/-- Scalar evaluation of `replacedSum` at any point `t : A`. -/
theorem eval_replacedSum [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) :
    (replacedSum s Φ P).eval t =
      ∑ x : ι → Bool, ∏ f ∈ s,
        MvPolynomial.eval (fun v => ∑ i : ι, (P f v i).eval t * bitVal A (x i)) (Φ f) := by
  rw [replacedSum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  change Polynomial.aeval t _ = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-! ### Restricted-subset Taylor jet identity -/

open Classical in
/-- The `j`-th Taylor coefficient of `replacedSum` at `t` is the Boolean-cube sum of the diagonal
evaluations of `(factorProduct s Φ P t x).coeff j`. -/
theorem coeff_taylor_replacedSum_eq_sum_eval [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (j : ℕ) :
    (Polynomial.taylor t (replacedSum s Φ P)).coeff j =
      ∑ x : ι → Bool,
        MvPolynomial.eval (fun i => bitVal A (x i)) ((factorProduct s Φ P t x).coeff j) := by
  rw [taylor_replacedSum_eq_sum_map_eval, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_map]

open Classical in
/-- **Restricted-subset Taylor jet identity** (equations (3.9)–(3.10), p. 24 of [OpenAI2026ETH]).
For every outer order `j ≤ q` and node `t : A`, the `j`-th Taylor coefficient of `replacedSum` at
`t` equals the signed Möbius sum over pairs `U ⊆ E` with `#E ≤ q` of restricted cube sums in which
`(factorProduct s Φ P t x).coeff j` remains indexed by the original assignment `x` while its formal
variables are evaluated at the indicator of `U`. -/
theorem coeff_taylor_replacedSum_eq_restricted_subsets [Fintype ι]
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) {j q : ℕ} (hj : j ≤ q) :
    (Polynomial.taylor t (replacedSum s Φ P)).coeff j =
      ∑ E ∈ (Finset.univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
          ∑ x ∈ (Finset.univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal A (decide (i ∈ U)))
              ((factorProduct s Φ P t x).coeff j) := by
  rw [coeff_taylor_replacedSum_eq_sum_eval]
  exact sum_eval_eq_restricted_subsets q (fun x => (factorProduct s Φ P t x).coeff j)
    (fun x => (totalDegree_coeff_factorProduct_le s Φ P t x j).trans hj)

end Substitutions

end Cslib.AffineTaylor
