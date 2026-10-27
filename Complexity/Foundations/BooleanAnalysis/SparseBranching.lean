/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseEquations
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi

/-!
# Univariate parity-product specialization and heavy-variable branch reduction

This module completes the algebraic and combinatorial infrastructure of Sections 5.3, 5.5, and 5.6
of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (pp. 37–39), building on
`Complexity.Foundations.BooleanAnalysis.SparseEquations`:

1. **Univariate $H(T)$ and coordinatewise $H_s(T) = [V^s] H(T)$ specialization (§5.3, eq. 5.5)**:
   When each variable $v \in \iota$ in equation $i \in I$ is replaced by a univariate polynomial
   $q_{x, i, v}(T) \in R[T]$ of degree at most $R_{\mathrm{deg}}$ that restores the Boolean input
   $\mathrm{bitVal}(x_v)$ at $T = 0$, the substituted equation polynomial
   `Cslib.BitString.univariateMonomialSumPoly` has `natDegree ≤ k * R_deg` and evaluates to
   `monomialSum R (P i) x` at $T = 0$. Summing the parity-factor product over $x \in \{0, 1\}^\iota$
   yields `Cslib.BitString.univariateParityProduct`, whose $V^s$-coordinate polynomials
   `Cslib.BitString.univariateParityCoord` ($s < \ell$) and truncated sum
   `Cslib.BitString.univariateParityTruncatedSum` have `natDegree` at most
   `(k * R_deg) * (#I + 2 * (ℓ - 1))` (`Cslib.BitString.natDegree_univariateParityCoord_le`,
   `Cslib.BitString.natDegree_univariateParityTruncatedSum_le`) and recover `commonZeroCount I P`
   modulo $2^\ell$ at $T = 0$
   (`Cslib.BitString.eval_zero_univariateParityTruncatedSum_modEq_commonZeroCount`,
   `Cslib.BitString.emod_eval_zero_univariateParityTruncatedSum_eq_commonZeroCount`).
2. **Free-variable branch relabeling (§5.5–5.6, Proof of Theorem 2.2)**:
   After branching on a subset $S \subseteq \iota$ of heavy variables, every restricted equation
   `restrictMonomials S b (P i)` is supported on `univ \ S`. Transporting along an equivalence
   `e : ↥(univ \ S) ≃ ι'` (such as `Fin n'` with $n' = n - |S|$) via
   `Cslib.BitString.relabelRestrictedMonomials` preserves degree bounds `#M ≤ k`, never increases
   monomial counts, bounds every free variable's equation incidence by `b₀` when $S$ is the
   heavy-variable set (`Cslib.BitString.varIncidence_relabelRestrictedMonomials_heavyVars_le`), and
   decomposes `commonZeroCount I P` additively as the sum of `commonZeroCount` on the relabeled
   free-variable cube `ι' → Bool`
   (`Cslib.BitString.commonZeroCount_eq_sum_relabelRestrictedMonomials`).
3. **Neutral variable-coverage scopes and Theorem 2.2 threshold bounds (§5.5–5.6)**:
   Adjoining a singleton neutral scope `{v}` for each declared variable $v \in \iota'$ via
   `Cslib.BitString.withNeutralFactors` and `Cslib.BitString.withNeutralScope` increments each
   variable's incidence by `1`, ensuring positive variable incidence (`1 ≤ varIncidence`),
   total incidence $M' \ge n'$ (`Cslib.BitString.card_le_totalIncidence_withNeutralFactors`), and
   light-variable incidence at most $b_0 + 1$. Finally, when $M \cdot s \le b_0 \cdot n$ (as for
   $b_0 = \lceil M s / n \rceil$ with $s = \lceil \sqrt{\lambda} \rceil$), the heavy-variable set
   has size at most $n / s$, at most $2^{n / s}$ branches, and leaves $n' \ge n - n / s \ge n / 2$
   free variables when $s \ge 2$.

## Main definitions

* `Cslib.BitString.univariateMonomialPoly`, `Cslib.BitString.univariateMonomialSumPoly`: univariate
  polynomial replacement in a monomial and a sparse polynomial equation.
* `Cslib.BitString.univariateParityProduct`, `Cslib.BitString.univariateParityCoord`,
  `Cslib.BitString.univariateParityTruncatedSum`: the cube-summed bivariate polynomial $H(T, V)$,
  its $V^s$-coordinate polynomials $[V^s] H(T)$, and its truncated sum $S_\ell(H(T))$.
* `Cslib.BitString.relabelMonomials`, `Cslib.BitString.relabelRestrictedMonomials`: relabeling
  monomial families and restricted branch equations onto a free-variable index type `ι'`.
* `Cslib.BitString.withNeutralFactors`, `Cslib.BitString.withNeutralScope`: adjoining neutral
  singleton scopes `{v}` for every variable $v \in \iota'$.
* `Cslib.BitString.heavyThreshold`: integer ceiling $\lceil M s / n \rceil$ for the heavy-variable
  incidence threshold $b_0$.

## Main results

* `Cslib.BitString.natDegree_univariateParityCoord_le` and
  `Cslib.BitString.natDegree_univariateParityTruncatedSum_le`: equation (5.5) degree bound
  $\deg_T \le (k R_{\mathrm{deg}})(m_{\mathrm{test}} + 2(\ell - 1))$.
* `Cslib.BitString.eval_zero_univariateParityTruncatedSum_modEq_commonZeroCount` and
  `Cslib.BitString.emod_eval_zero_univariateParityTruncatedSum_eq_commonZeroCount`: equation (5.5)
  congruence and exact recovery of `commonZeroCount` at $T = 0$.
* `Cslib.BitString.commonZeroCount_eq_sum_relabelRestrictedMonomials`: additive branch decomposition
  of `commonZeroCount` into `commonZeroCount` over the relabeled free-variable cube `ι' → Bool`.
* `Cslib.BitString.varIncidence_relabelRestrictedMonomials_heavyVars_le`: post-branching
  free-variable incidence bound $\le b_0$ on `ι'`.
* `Cslib.BitString.card_le_totalIncidence_withNeutralFactors`: neutral scopes guarantee $M' \ge n'$.
* `Cslib.BitString.card_heavyVars_le_card_div` and
  `Cslib.BitString.card_sdiff_heavyVars_ge_half`: $|S| \le n / s$ and $n' \ge n / 2$ for $s \ge 2$.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.3, 5.5, and 5.6)
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset

variable {ι ι' κ R : Type*}

/-! ### Section 1: Univariate replacement forms and degree / restoration lemmas (§5.3) -/

section UnivariateReplacement

/-- Replacing each variable `v ∈ M` by a univariate polynomial `q v : Polynomial R` in a monomial
`M`. -/
def univariateMonomialPoly (R : Type*) [CommSemiring R] (q : ι → Polynomial R)
    (M : Finset ι) : Polynomial R :=
  ∏ v ∈ M, q v

/-- Replacing each variable `v` by `q v : Polynomial R` in a sparse polynomial `𝓜`. -/
def univariateMonomialSumPoly (R : Type*) [CommSemiring R] (q : ι → Polynomial R)
    (𝓜 : Finset (Finset ι)) : Polynomial R :=
  ∑ M ∈ 𝓜, univariateMonomialPoly R q M

/-- `univariateMonomialPoly R q M` agrees with evaluating `monomialPoly R M` at `q`. -/
theorem univariateMonomialPoly_eq_eval₂ [CommSemiring R] (q : ι → Polynomial R) (M : Finset ι) :
    univariateMonomialPoly R q M = (monomialPoly R M).eval₂ Polynomial.C q := by
  rw [univariateMonomialPoly, monomialPoly, MvPolynomial.eval₂_prod]
  refine prod_congr rfl fun v _ => ?_
  rw [MvPolynomial.eval₂_X]

/-- `univariateMonomialSumPoly R q 𝓜` agrees with evaluating `monomialSumPoly R 𝓜` at `q`. -/
theorem univariateMonomialSumPoly_eq_eval₂ [CommSemiring R] (q : ι → Polynomial R)
    (𝓜 : Finset (Finset ι)) :
    univariateMonomialSumPoly R q 𝓜 = (monomialSumPoly R 𝓜).eval₂ Polynomial.C q := by
  rw [univariateMonomialSumPoly, monomialSumPoly, MvPolynomial.eval₂_sum]
  exact sum_congr rfl fun M _ => univariateMonomialPoly_eq_eval₂ q M

/-- Pointwise evaluation of `univariateMonomialPoly R q M` at `t : R`. -/
theorem eval_univariateMonomialPoly [CommSemiring R] (q : ι → Polynomial R) (M : Finset ι)
    (t : R) :
    (univariateMonomialPoly R q M).eval t = ∏ v ∈ M, (q v).eval t := by
  rw [univariateMonomialPoly, Polynomial.eval_prod]

private theorem eval_sum {α : Type*} [CommSemiring R] (S : Finset α) (f : α → Polynomial R)
    (t : R) :
    (∑ x ∈ S, f x).eval t = ∑ x ∈ S, (f x).eval t := by
  change Polynomial.evalRingHom t (∑ x ∈ S, f x) = _
  rw [map_sum]
  rfl

/-- Pointwise evaluation of `univariateMonomialSumPoly R q 𝓜` at `t : R`. -/
theorem eval_univariateMonomialSumPoly [CommSemiring R] (q : ι → Polynomial R)
    (𝓜 : Finset (Finset ι)) (t : R) :
    (univariateMonomialSumPoly R q 𝓜).eval t = ∑ M ∈ 𝓜, ∏ v ∈ M, (q v).eval t := by
  rw [univariateMonomialSumPoly, eval_sum]
  exact sum_congr rfl fun M _ => eval_univariateMonomialPoly q M t

/-- **Restoration at `T = 0`**: if every `q v` (`v ∈ M`) evaluates at `0` to `bitVal R (x v)`, then
`univariateMonomialSumPoly R q 𝓜` evaluates at `0` to `monomialSum R 𝓜 x`. -/
theorem eval_zero_univariateMonomialSumPoly [CommRing R] {q : ι → Polynomial R}
    {𝓜 : Finset (Finset ι)} {x : ι → Bool}
    (hq0 : ∀ M ∈ 𝓜, ∀ v ∈ M, (q v).eval 0 = bitVal R (x v)) :
    (univariateMonomialSumPoly R q 𝓜).eval 0 = monomialSum R 𝓜 x := by
  rw [eval_univariateMonomialSumPoly, monomialSum]
  refine sum_congr rfl fun M hM => ?_
  rw [monomial]
  exact prod_congr rfl fun v hv => hq0 M hM v hv

/-- If `#M ≤ k` and every `q v` (`v ∈ M`) has `natDegree ≤ d₀`, then
`univariateMonomialPoly R q M` has `natDegree ≤ k * d₀`. -/
theorem natDegree_univariateMonomialPoly_le [CommSemiring R] {q : ι → Polynomial R}
    {M : Finset ι} {k d₀ : ℕ} (hk : #M ≤ k) (hd : ∀ v ∈ M, (q v).natDegree ≤ d₀) :
    (univariateMonomialPoly R q M).natDegree ≤ k * d₀ := by
  calc
    (∏ v ∈ M, q v).natDegree
      ≤ ∑ v ∈ M, (q v).natDegree := Polynomial.natDegree_prod_le M q
    _ ≤ ∑ _v ∈ M, d₀ := sum_le_sum hd
    _ = #M * d₀ := by rw [sum_const, smul_eq_mul]
    _ ≤ k * d₀ := Nat.mul_le_mul_right d₀ hk

/-- If every monomial `M ∈ 𝓜` has `#M ≤ k` and every `q v` has `natDegree ≤ d₀`, then
`univariateMonomialSumPoly R q 𝓜` has `natDegree ≤ k * d₀`. -/
theorem natDegree_univariateMonomialSumPoly_le [CommSemiring R] {q : ι → Polynomial R}
    {𝓜 : Finset (Finset ι)} {k d₀ : ℕ} (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hd : ∀ M ∈ 𝓜, ∀ v ∈ M, (q v).natDegree ≤ d₀) :
    (univariateMonomialSumPoly R q 𝓜).natDegree ≤ k * d₀ := by
  refine (Polynomial.natDegree_sum_le 𝓜 (univariateMonomialPoly R q)).trans ?_
  rw [Finset.fold_max_le]
  exact ⟨Nat.zero_le _, fun M hM => natDegree_univariateMonomialPoly_le (hk M hM) (hd M hM)⟩

end UnivariateReplacement

/-! ### Section 2: Ring-homomorphism transport and `natDegree` bounds for `parityFactor` -/

section UnivariateParityFactor

/-- Any ring homomorphism `φ : A →+* B` commutes with `Polynomial.evalInt`. -/
theorem map_evalInt {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (y : A)
    (p : Polynomial ℤ) :
    φ (Polynomial.evalInt y p) = Polynomial.evalInt (φ y) p := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [Polynomial.evalInt, Polynomial.eval₂_add, map_add, ← Polynomial.evalInt,
      ← Polynomial.evalInt, ihp, ihq, Polynomial.evalInt, Polynomial.evalInt,
      ← Polynomial.eval₂_add]
    rfl
  | monomial n a =>
    rw [Polynomial.evalInt, Polynomial.evalInt, Polynomial.eval₂_monomial,
      Polynomial.eval₂_monomial, map_mul, map_pow]
    congr 1
    rw [eq_intCast, eq_intCast, map_intCast]

/-- Mapping `parityFactor ℓ y` coefficientwise by `φ : A →+* B` yields `parityFactor ℓ (φ y)`. -/
theorem map_parityFactor {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (ℓ : ℕ) (y : A) :
    (Polynomial.parityFactor ℓ y).map φ = Polynomial.parityFactor ℓ (φ y) := by
  ext s
  rw [Polynomial.coeff_map, Polynomial.coeff_parityFactor, Polynomial.coeff_parityFactor]
  split_ifs with hs
  · rw [map_mul, map_pow, map_evalInt, map_evalInt]
  · exact map_zero φ

/-- Any ring homomorphism `φ : A →+* B` commutes with `sumCoeffsBelow`. -/
theorem map_sumCoeffsBelow {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    (P : Polynomial A) (m : ℕ) :
    φ (P.sumCoeffsBelow m) = (P.map φ).sumCoeffsBelow m := by
  rw [Polynomial.sumCoeffsBelow, Polynomial.sumCoeffsBelow, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map]

/-- Evaluating the `s`-th coefficient of `∏ i ∈ I, parityFactor ℓ (L i)` at `t : R` agrees with
the `s`-th coefficient of `∏ i ∈ I, parityFactor ℓ ((L i).eval t)`. -/
theorem eval_coeff_prod_parityFactor [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → Polynomial R) (s : ℕ) (t : R) :
    ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff s).eval t =
      (∏ i ∈ I, Polynomial.parityFactor ℓ ((L i).eval t)).coeff s := by
  let φ : Polynomial R →+* R := Polynomial.evalRingHom t
  change φ ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff s) = _
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  refine congrArg (fun Q : Polynomial R => Q.coeff s) (prod_congr rfl fun i _ => ?_)
  exact map_parityFactor φ ℓ (L i)

/-- Evaluating `sumCoeffsBelow m` of `∏ i ∈ I, parityFactor ℓ (L i)` at `t : R` agrees with
`sumCoeffsBelow m` of `∏ i ∈ I, parityFactor ℓ ((L i).eval t)`. -/
theorem eval_sumCoeffsBelow_prod_parityFactor [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → Polynomial R) (m : ℕ) (t : R) :
    ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).sumCoeffsBelow m).eval t =
      (∏ i ∈ I, Polynomial.parityFactor ℓ ((L i).eval t)).sumCoeffsBelow m := by
  rw [Polynomial.sumCoeffsBelow, eval_sum, Polynomial.sumCoeffsBelow]
  exact sum_congr rfl fun s _ => eval_coeff_prod_parityFactor I ℓ L s t

/-- For `y : Polynomial R` and `p : Polynomial ℤ`,
`(evalInt y p).natDegree ≤ p.natDegree * y.natDegree`. -/
theorem natDegree_evalInt_le [CommRing R] (y : Polynomial R) (p : Polynomial ℤ) :
    (Polynomial.evalInt y p).natDegree ≤ p.natDegree * y.natDegree := by
  rw [Polynomial.evalInt, Polynomial.eval₂_eq_sum_range]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  rw [mem_range, Nat.lt_succ_iff] at hi
  dsimp only [Function.comp_apply]
  have hcast : (Int.castRingHom (Polynomial R) (p.coeff i)) = Polynomial.C (p.coeff i : R) := by
    rw [eq_intCast, ← Polynomial.C_eq_intCast]
  rw [hcast]
  calc
    (Polynomial.C (p.coeff i : R) * y ^ i).natDegree
      ≤ (Polynomial.C (p.coeff i : R)).natDegree + (y ^ i).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 0 + i * y.natDegree := by
        rw [Polynomial.natDegree_C]
        exact add_le_add le_rfl Polynomial.natDegree_pow_le
    _ ≤ p.natDegree * y.natDegree := by
        rw [zero_add]
        exact Nat.mul_le_mul_right _ hi

/-- `evalInt y (parityBaseDigit ℓ j)` has `natDegree ≤ y.natDegree`. -/
theorem natDegree_evalInt_parityBaseDigit_le [CommRing R] (ℓ j : ℕ) (y : Polynomial R) :
    (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j)).natDegree ≤ y.natDegree := by
  calc
    (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j)).natDegree
      ≤ (Polynomial.parityBaseDigit ℓ j).natDegree * y.natDegree :=
        natDegree_evalInt_le y _
    _ ≤ 1 * y.natDegree :=
        Nat.mul_le_mul_right _ (Polynomial.natDegree_parityBaseDigit_le ℓ j)
    _ = y.natDegree := one_mul _

/-- `evalInt y hPoly` has `natDegree ≤ 2 * y.natDegree`. -/
theorem natDegree_evalInt_hPoly_le [CommRing R] (y : Polynomial R) :
    (Polynomial.evalInt y Polynomial.hPoly).natDegree ≤ 2 * y.natDegree := by
  rw [Polynomial.evalInt_hPoly]
  calc
    (y ^ 2 - y).natDegree
      ≤ max (y ^ 2).natDegree y.natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ max (2 * y.natDegree) y.natDegree :=
        max_le_max Polynomial.natDegree_pow_le le_rfl
    _ = 2 * y.natDegree := max_eq_left (by omega)

/-- The `j`-th coefficient of `parityFactor ℓ y` has `natDegree ≤ (1 + 2 * j) * y.natDegree`. -/
theorem natDegree_coeff_parityFactor_le [CommRing R] (ℓ : ℕ) (y : Polynomial R) (j : ℕ) :
    ((Polynomial.parityFactor ℓ y).coeff j).natDegree ≤ (1 + 2 * j) * y.natDegree := by
  rw [Polynomial.coeff_parityFactor]
  split_ifs with hj
  · calc
      (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j) *
          Polynomial.evalInt y Polynomial.hPoly ^ j).natDegree
        ≤ (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j)).natDegree +
            (Polynomial.evalInt y Polynomial.hPoly ^ j).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ y.natDegree + j * (Polynomial.evalInt y Polynomial.hPoly).natDegree :=
          add_le_add (natDegree_evalInt_parityBaseDigit_le ℓ j y) Polynomial.natDegree_pow_le
      _ ≤ y.natDegree + j * (2 * y.natDegree) :=
          add_le_add le_rfl (Nat.mul_le_mul_left j (natDegree_evalInt_hPoly_le y))
      _ = (1 + 2 * j) * y.natDegree := by ring
  · simp only [Polynomial.natDegree_zero, zero_le]

/-- If every `L i` (`i ∈ I`) has `natDegree ≤ d`, then the `V ^ s`-coefficient of
`∏ i ∈ I, parityFactor ℓ (L i)` has `natDegree ≤ d * (#I + 2 * s)`. -/
theorem natDegree_coeff_prod_parityFactor_le [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → Polynomial R) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) :
    ∀ s : ℕ, ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff s).natDegree ≤ d * (#I + 2 * s) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro s
    simp only [prod_empty, card_empty, zero_add]
    rcases eq_or_ne s 0 with rfl | hs
    · simp only [Polynomial.coeff_one_zero, Polynomial.natDegree_one, zero_le]
    · rw [Polynomial.coeff_one, ite_eq_right hs, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  | insert a I ha ih =>
    intro s
    rw [prod_insert ha, card_insert_of_notMem ha, Polynomial.coeff_mul]
    have haL : (L a).natDegree ≤ d := hL a (mem_insert_self a I)
    have hIL : ∀ i ∈ I, (L i).natDegree ≤ d := fun i hi => hL i (mem_insert_of_mem hi)
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun p hp => ?_⟩
    rw [mem_antidiagonal] at hp
    calc
      (((Polynomial.parityFactor ℓ (L a)).coeff p.1) *
          ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff p.2)).natDegree
        ≤ ((Polynomial.parityFactor ℓ (L a)).coeff p.1).natDegree +
            ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff p.2).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ (1 + 2 * p.1) * (L a).natDegree + d * (#I + 2 * p.2) :=
          add_le_add (natDegree_coeff_parityFactor_le ℓ (L a) p.1) (ih hIL p.2)
      _ ≤ (1 + 2 * p.1) * d + d * (#I + 2 * p.2) :=
          add_le_add (Nat.mul_le_mul_left _ haL) le_rfl
      _ = d * (#I + 1 + 2 * (p.1 + p.2)) := by ring
      _ = d * (#I + 1 + 2 * s) := by rw [hp]

/-- For `s < ℓ`, the `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (L i)` has
`natDegree ≤ d * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_coeff_prod_parityFactor_le_of_lt [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → Polynomial R) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) {s : ℕ} (hs : s < ℓ) :
    ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).coeff s).natDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  refine (natDegree_coeff_prod_parityFactor_le I ℓ L hL s).trans ?_
  exact Nat.mul_le_mul_left d (by omega)

/-- The truncated sum `sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (L i))` has
`natDegree ≤ d * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_sumCoeffsBelow_prod_parityFactor_le [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → Polynomial R) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) :
    ((∏ i ∈ I, Polynomial.parityFactor ℓ (L i)).sumCoeffsBelow ℓ).natDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  rw [Polynomial.sumCoeffsBelow]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun s hs => ?_⟩
  exact natDegree_coeff_prod_parityFactor_le_of_lt I ℓ L hL (mem_range.mp hs)

end UnivariateParityFactor

/-! ### Section 3: Cube-summed univariate polynomial $H(T)$ and equation (5.5) -/

section CubeSummedUnivariate

/-- **§5.3 (`H(T)` in `R[T][V]`)**: the cube sum over `x : ι → Bool` of the product of parity
factors evaluated at the univariate replacement forms `q x i : ι → Polynomial R`. -/
def univariateParityProduct [Fintype ι] [DecidableEq ι] [CommRing R] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) : Polynomial (Polynomial R) :=
  ∑ x : ι → Bool,
    ∏ i ∈ I, Polynomial.parityFactor ℓ (univariateMonomialSumPoly R (q x i) (P i))

/-- **§5.3 (`[V ^ s] H(T)`)**: the `s`-th `V`-coefficient polynomial of `univariateParityProduct`
in `R[T]`. -/
def univariateParityCoord [Fintype ι] [DecidableEq ι] [CommRing R] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) (s : ℕ) : Polynomial R :=
  (univariateParityProduct I P ℓ q).coeff s

/-- **§5.3 (`S_ℓ(H(T))`)**: the sum of the first `ℓ` `V`-coefficient polynomials of
`univariateParityProduct` in `R[T]`. -/
def univariateParityTruncatedSum [Fintype ι] [DecidableEq ι] [CommRing R] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) : Polynomial R :=
  (univariateParityProduct I P ℓ q).sumCoeffsBelow ℓ

/-- `univariateParityTruncatedSum` is the sum of `univariateParityCoord I P ℓ q s` for
`s ∈ range ℓ`. -/
theorem univariateParityTruncatedSum_eq_sum_coord [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) :
    univariateParityTruncatedSum I P ℓ q =
      ∑ s ∈ range ℓ, univariateParityCoord I P ℓ q s :=
  rfl

/-- `univariateParityCoord` expands as the cube sum of the `V ^ s`-coefficients of each `x`-term. -/
theorem univariateParityCoord_eq_sum [Fintype ι] [DecidableEq ι] [CommRing R] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (ℓ : ℕ) (q : (ι → Bool) → κ → ι → Polynomial R) (s : ℕ) :
    univariateParityCoord I P ℓ q s =
      ∑ x : ι → Bool,
        (∏ i ∈ I,
          Polynomial.parityFactor ℓ (univariateMonomialSumPoly R (q x i) (P i))).coeff s := by
  rw [univariateParityCoord, univariateParityProduct, Polynomial.finsetSum_coeff]

/-- `univariateParityTruncatedSum` expands as the cube sum of `sumCoeffsBelow ℓ` of each
`x`-term. -/
theorem univariateParityTruncatedSum_eq_sum [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) :
    univariateParityTruncatedSum I P ℓ q =
      ∑ x : ι → Bool,
        (∏ i ∈ I,
          Polynomial.parityFactor ℓ
            (univariateMonomialSumPoly R (q x i) (P i))).sumCoeffsBelow ℓ := by
  rw [univariateParityTruncatedSum, univariateParityProduct, Polynomial.sumCoeffsBelow]
  simp only [Polynomial.finsetSum_coeff]
  rw [sum_comm]
  rfl

/-- **§5.3, eq. (5.5a) (coordinatewise degree bound $\deg_T [V^s] H(T) \le k R_{\mathrm{deg}}
(\#I + 2(\ell - 1))$)**: if every equation has degree at most `k` and every replacement polynomial
`q x i v` has `natDegree ≤ R_deg`, then for `s < ℓ`, `univariateParityCoord I P ℓ q s` has
`natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateParityCoord_le [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) {k R_deg : ℕ}
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hq : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q x i v).natDegree ≤ R_deg)
    {s : ℕ} (hs : s < ℓ) :
    (univariateParityCoord I P ℓ q s).natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1)) := by
  rw [univariateParityCoord_eq_sum]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun x _ => ?_⟩
  refine natDegree_coeff_prod_parityFactor_le_of_lt I ℓ
    (fun i => univariateMonomialSumPoly R (q x i) (P i)) (fun i hi => ?_) hs
  exact natDegree_univariateMonomialSumPoly_le (hk i hi) (hq x i hi)

/-- **§5.3, eq. (5.5a) ($\deg_T S_\ell(H(T)) \le k R_{\mathrm{deg}} (\#I + 2(\ell - 1))$)**: if
every equation has degree at most `k` and every replacement polynomial `q x i v` has
`natDegree ≤ R_deg`, then `univariateParityTruncatedSum I P ℓ q` has
`natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateParityTruncatedSum_le [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R) {k R_deg : ℕ}
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hq : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q x i v).natDegree ≤ R_deg) :
    (univariateParityTruncatedSum I P ℓ q).natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1)) := by
  rw [univariateParityTruncatedSum_eq_sum_coord]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun s hs => ?_⟩
  exact natDegree_univariateParityCoord_le I P ℓ q hk hq (mem_range.mp hs)

/-- **§5.3, eq. (5.5b) (evaluation restoration at `T = 0`)**: when every replacement polynomial
`q x i v` restores `bitVal R (x v)` at `T = 0`, evaluating `univariateParityTruncatedSum` at `0`
yields the cube sum of truncated parity-factor products at `monomialSum R (P i) x`. -/
theorem eval_zero_univariateParityTruncatedSum [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (ℓ : ℕ)
    (q : (ι → Bool) → κ → ι → Polynomial R)
    (hq0 : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q x i v).eval 0 = bitVal R (x v)) :
    (univariateParityTruncatedSum I P ℓ q).eval 0 =
      ∑ x : ι → Bool,
        (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum R (P i) x)).sumCoeffsBelow ℓ := by
  rw [univariateParityTruncatedSum_eq_sum, eval_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_sumCoeffsBelow_prod_parityFactor]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [eval_zero_univariateMonomialSumPoly (hq0 x i hi)]

/-- **§5.3, eq. (5.5b) ($S_\ell(H(0)) \equiv N(\mathcal{P}) \pmod{2^\ell}$)**: when every integer
replacement polynomial `q x i v` restores `bitVal ℤ (x v)` at `T = 0`,
`(univariateParityTruncatedSum I P ℓ q).eval 0 ≡ commonZeroCount I P [ZMOD 2 ^ ℓ]`. -/
theorem eval_zero_univariateParityTruncatedSum_modEq_commonZeroCount [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (q : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hq0 : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q x i v).eval 0 = bitVal ℤ (x v)) :
    (univariateParityTruncatedSum I P ℓ q).eval 0 ≡
      (commonZeroCount I P : ℤ) [ZMOD (2 : ℤ) ^ ℓ] := by
  rw [eval_zero_univariateParityTruncatedSum I P ℓ q hq0]
  exact sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount I P hℓ

/-- **§5.3, eq. (5.5b) (exact recovery of $N(\mathcal{P})$ from $S_\ell(H(0)) \bmod 2^\ell$)**:
when `Fintype.card ι < ℓ` and every replacement polynomial `q x i v` restores `bitVal ℤ (x v)` at
`T = 0`, the least nonnegative residue of `(univariateParityTruncatedSum I P ℓ q).eval 0` modulo
`2 ^ ℓ` equals `commonZeroCount I P`. -/
theorem emod_eval_zero_univariateParityTruncatedSum_eq_commonZeroCount [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) {ℓ : ℕ} (hℓ : Fintype.card ι < ℓ)
    (q : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hq0 : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q x i v).eval 0 = bitVal ℤ (x v)) :
    ((univariateParityTruncatedSum I P ℓ q).eval 0) % ((2 : ℤ) ^ ℓ) =
      (commonZeroCount I P : ℤ) := by
  rw [eval_zero_univariateParityTruncatedSum I P ℓ q hq0]
  exact emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount I P hℓ

end CubeSummedUnivariate

/-! ### Section 4: Free-variable branch relabeling (§5.5–5.6, Proof of Theorem 2.2) -/

section BranchRelabeling

/-- Relabeling every monomial `M ∈ 𝓜` along a map `f : ι → ι'`. -/
def relabelMonomials [DecidableEq ι'] (f : ι → ι') (𝓜 : Finset (Finset ι)) :
    Finset (Finset ι') :=
  𝓜.image fun M => M.image f

/-- Relabeling a restricted branch equation `restrictMonomials S b 𝓜` (whose monomials are subsets
of `univ \ S`) across an equivalence `e : ↥(univ \ S) ≃ ι'` onto a free-variable index type `ι'`. -/
def relabelRestrictedMonomials [Fintype ι] [DecidableEq ι] [DecidableEq ι']
    (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool) (𝓜 : Finset (Finset ι)) :
    Finset (Finset ι') :=
  (restrictMonomials S b 𝓜).image fun M => (M.subtype (· ∈ univ \ S)).image e

/-- Extending a free-variable assignment `y : ι' → Bool` by `false` on `S` to obtain a canonical
representative in `subproblemAssignments S`. -/
def extendFreeAssignment [Fintype ι] [DecidableEq ι] (S : Finset ι) (e : ↥(univ \ S) ≃ ι')
    (y : ι' → Bool) (v : ι) : Bool :=
  if hv : v ∈ univ \ S then y (e ⟨v, hv⟩) else false

/-- Restricting an assignment `z : ι → Bool` to `ι'` along `e : ↥(univ \ S) ≃ ι'`. -/
def restrictToFreeVars [Fintype ι] [DecidableEq ι] (S : Finset ι) (e : ↥(univ \ S) ≃ ι')
    (z : ι → Bool) (w : ι') : Bool :=
  z (e.symm w).1

@[simp]
theorem restrictToFreeVars_extendFreeAssignment [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (e : ↥(univ \ S) ≃ ι') (y : ι' → Bool) :
    restrictToFreeVars S e (extendFreeAssignment S e y) = y := by
  ext w
  simp only [restrictToFreeVars, extendFreeAssignment, (e.symm w).2, ↓reduceDIte, Subtype.coe_eta,
    Equiv.apply_symm_apply]

theorem extendFreeAssignment_mem_subproblemAssignments [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (y : ι' → Bool) :
    extendFreeAssignment S e y ∈ subproblemAssignments S := by
  rw [subproblemAssignments, mem_filter]
  refine ⟨mem_univ _, fun v hv => ?_⟩
  have hnot : v ∉ univ \ S := fun h => (mem_sdiff.mp h).2 hv
  simp only [extendFreeAssignment, hnot, ↓reduceDIte]

theorem extendFreeAssignment_restrictToFreeVars [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (e : ↥(univ \ S) ≃ ι') {z : ι → Bool} (hz : z ∈ subproblemAssignments S) :
    extendFreeAssignment S e (restrictToFreeVars S e z) = z := by
  rw [subproblemAssignments, mem_filter] at hz
  ext v
  by_cases hv : v ∈ univ \ S
  · simp only [extendFreeAssignment, hv, ↓reduceDIte, restrictToFreeVars,
      Equiv.symm_apply_apply]
  · have hvS : v ∈ S := by
      by_contra hnotS
      exact hv (mem_sdiff.mpr ⟨mem_univ v, hnotS⟩)
    simp only [extendFreeAssignment, hv, ↓reduceDIte, hz.2 v hvS]

/-- Every monomial in `relabelRestrictedMonomials S e b 𝓜` has degree at most `k` when every
monomial in `𝓜` has degree at most `k`. -/
theorem card_mem_relabelRestrictedMonomials_le [Fintype ι] [DecidableEq ι] [DecidableEq ι']
    {S : Finset ι} {e : ↥(univ \ S) ≃ ι'} {b : ι → Bool} {𝓜 : Finset (Finset ι)} {k : ℕ}
    (hk : ∀ M ∈ 𝓜, #M ≤ k) :
    ∀ M' ∈ relabelRestrictedMonomials S e b 𝓜, #M' ≤ k := by
  intro M' hM'
  rw [relabelRestrictedMonomials, mem_image] at hM'
  rcases hM' with ⟨M, hM, rfl⟩
  calc
    #((M.subtype (· ∈ univ \ S)).image e)
      ≤ #(M.subtype (· ∈ univ \ S)) := card_image_le
    _ = #(M.filter (· ∈ univ \ S)) := card_subtype _ _
    _ ≤ #M := card_filter_le _ _
    _ ≤ k := card_le_of_mem_restrictMonomials hk hM

/-- `relabelRestrictedMonomials` never increases the number of monomials. -/
theorem card_relabelRestrictedMonomials_le [Fintype ι] [DecidableEq ι] [DecidableEq ι']
    (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool) (𝓜 : Finset (Finset ι)) :
    #(relabelRestrictedMonomials S e b 𝓜) ≤ #𝓜 :=
  card_image_le.trans (card_restrictMonomials_le S b 𝓜)

/-- On any monomial `M ⊆ univ \ S`, the subtype-image map `M ↦ (M.subtype (· ∈ univ \ S)).image e`
is injective. -/
private theorem subtype_image_injOn_restrictMonomials [Fintype ι] [DecidableEq ι] [DecidableEq ι']
    (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool) (𝓜 : Finset (Finset ι)) :
    Set.InjOn (fun M : Finset ι => (M.subtype (· ∈ univ \ S)).image e)
      (restrictMonomials S b 𝓜) := by
  intro M₁ hM₁ M₂ hM₂ hEq
  dsimp only at hEq
  have hsub₁ : M₁ ⊆ univ \ S := fun v hv =>
    mem_sdiff.mpr ⟨mem_univ v, disjoint_left.mp (disjoint_of_mem_restrictMonomials hM₁) hv⟩
  have hsub₂ : M₂ ⊆ univ \ S := fun v hv =>
    mem_sdiff.mpr ⟨mem_univ v, disjoint_left.mp (disjoint_of_mem_restrictMonomials hM₂) hv⟩
  ext v
  constructor
  · intro hv₁
    have hvU : v ∈ univ \ S := hsub₁ hv₁
    have hin : e ⟨v, hvU⟩ ∈ (M₁.subtype (· ∈ univ \ S)).image e :=
      mem_image.mpr ⟨⟨v, hvU⟩, mem_subtype.mpr hv₁, rfl⟩
    rw [hEq, mem_image] at hin
    rcases hin with ⟨u, hu, hue⟩
    have huv := e.injective hue
    subst huv
    exact mem_subtype.mp hu
  · intro hv₂
    have hvU : v ∈ univ \ S := hsub₂ hv₂
    have hin : e ⟨v, hvU⟩ ∈ (M₂.subtype (· ∈ univ \ S)).image e :=
      mem_image.mpr ⟨⟨v, hvU⟩, mem_subtype.mpr hv₂, rfl⟩
    rw [← hEq, mem_image] at hin
    rcases hin with ⟨u, hu, hue⟩
    have huv := e.injective hue
    subst huv
    exact mem_subtype.mp hu

/-- Evaluating `relabelRestrictedMonomials S e b 𝓜` at `y : ι' → Bool` in any commutative ring `R`
agrees with evaluating `restrictMonomials S b 𝓜` at `extendFreeAssignment S e y`. -/
theorem monomialSum_relabelRestrictedMonomials [Fintype ι] [DecidableEq ι] [DecidableEq ι']
    (R : Type*) [CommRing R] (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool)
    (𝓜 : Finset (Finset ι)) (y : ι' → Bool) :
    monomialSum R (relabelRestrictedMonomials S e b 𝓜) y =
      monomialSum R (restrictMonomials S b 𝓜) (extendFreeAssignment S e y) := by
  rw [monomialSum, monomialSum, relabelRestrictedMonomials,
    sum_image (subtype_image_injOn_restrictMonomials S e b 𝓜)]
  refine sum_congr rfl fun M hM => ?_
  have hsub : M ⊆ univ \ S := fun v hv =>
    mem_sdiff.mpr ⟨mem_univ v, disjoint_left.mp (disjoint_of_mem_restrictMonomials hM) hv⟩
  rw [monomial, monomial, prod_image (fun u _ v _ huv => e.injective huv)]
  refine prod_nbij Subtype.val (fun x hx => mem_coe.mpr (mem_subtype.mp hx))
    Subtype.val_injective.injOn
    (fun v hv => ⟨⟨v, hsub hv⟩, mem_coe.mpr (mem_subtype.mpr hv), rfl⟩)
    (fun x _ => ?_)
  simp only [extendFreeAssignment, x.2, ↓reduceDIte]

/-- Over `ZMod 2`, evaluating `relabelRestrictedMonomials S e b 𝓜` at `y : ι' → Bool` equals
evaluating the original equation `𝓜` at `patchAssignment S b (extendFreeAssignment S e y)`. -/
theorem monomialSum_zmod_two_relabelRestrictedMonomials [Fintype ι] [DecidableEq ι]
    [DecidableEq ι'] (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool)
    (𝓜 : Finset (Finset ι)) (y : ι' → Bool) :
    monomialSum (ZMod 2) (relabelRestrictedMonomials S e b 𝓜) y =
      monomialSum (ZMod 2) 𝓜 (patchAssignment S b (extendFreeAssignment S e y)) := by
  rw [monomialSum_relabelRestrictedMonomials, monomialSum_zmod_two_restrictMonomials]

/-- **§5.5–5.6 (Theorem 2.2 additive branch decomposition on the relabeled free-variable cube
`ι' → Bool`)**: for any branch variable set `S` and equivalence `e : ↥(univ \ S) ≃ ι'`, the
common-zero count `commonZeroCount I P` equals the sum over `b ∈ branchAssignments S` of
`commonZeroCount` of the relabeled restricted equations on `ι' → Bool`. -/
theorem commonZeroCount_eq_sum_relabelRestrictedMonomials [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (I : Finset κ)
    (P : κ → Finset (Finset ι)) :
    commonZeroCount I P =
      ∑ b ∈ branchAssignments S,
        commonZeroCount I (fun i => relabelRestrictedMonomials S e b (P i)) := by
  rw [commonZeroCount_eq_sum_branches S I P]
  refine sum_congr rfl fun b _ => ?_
  rw [commonZeroCount]
  refine card_bij (fun z _ => restrictToFreeVars S e z)
    (fun z hz => ?_) (fun z₁ hz₁ z₂ hz₂ hEq => ?_) (fun y hy => ?_)
  · rw [mem_filter] at hz ⊢
    refine ⟨mem_univ _, fun i hi => ?_⟩
    rw [monomialSum_relabelRestrictedMonomials,
      extendFreeAssignment_restrictToFreeVars S e hz.1]
    exact hz.2 i hi
  · rw [mem_filter] at hz₁ hz₂
    rw [← extendFreeAssignment_restrictToFreeVars S e hz₁.1,
      ← extendFreeAssignment_restrictToFreeVars S e hz₂.1, hEq]
  · rw [mem_filter] at hy
    refine ⟨extendFreeAssignment S e y, mem_filter.mpr
      ⟨extendFreeAssignment_mem_subproblemAssignments S e y, fun i hi => ?_⟩,
      restrictToFreeVars_extendFreeAssignment S e y⟩
    rw [← monomialSum_relabelRestrictedMonomials]
    exact hy.2 i hi

/-- The variable scope of `relabelRestrictedMonomials S e b 𝓜` is contained in the image under `e`
of `(equationScope 𝓜 \ S).subtype (· ∈ univ \ S)`. -/
theorem equationScope_relabelRestrictedMonomials_subset [Fintype ι] [DecidableEq ι]
    [DecidableEq ι'] (S : Finset ι) (e : ↥(univ \ S) ≃ ι') (b : ι → Bool)
    (𝓜 : Finset (Finset ι)) :
    equationScope (relabelRestrictedMonomials S e b 𝓜) ⊆
      ((equationScope 𝓜 \ S).subtype (· ∈ univ \ S)).image e := by
  intro w hw
  rw [equationScope, mem_biUnion] at hw
  rcases hw with ⟨M', hM', hwM'⟩
  rw [relabelRestrictedMonomials, mem_image] at hM'
  rcases hM' with ⟨M, hM, rfl⟩
  rw [id_eq, mem_image] at hwM'
  rcases hwM' with ⟨v, hv, rfl⟩
  rw [mem_subtype] at hv
  have hvScope : v.1 ∈ equationScope 𝓜 \ S :=
    equationScope_restrictMonomials_subset_sdiff S b 𝓜
      (mem_biUnion.mpr ⟨M, hM, hv⟩)
  exact mem_image.mpr ⟨v, mem_subtype.mpr hvScope, rfl⟩

/-- **§5.5–5.6 (free-variable incidence bound on `ι'` after branching on `heavyVars`)**: for
`S = heavyVars univ F (fun i => equationScope (P i)) b₀` and `I ⊆ F`, every variable `w : ι'` has
incidence at most `b₀` in the relabeled restricted system. -/
theorem varIncidence_relabelRestrictedMonomials_heavyVars_le [Fintype ι] [DecidableEq ι]
    [DecidableEq ι'] (F I : Finset κ) (P : κ → Finset (Finset ι)) (b₀ : ℕ)
    (hIF : I ⊆ F) (e : ↥(univ \ heavyVars univ F (fun i => equationScope (P i)) b₀) ≃ ι')
    (b : ι → Bool) (w : ι') :
    varIncidence I
      (fun i => equationScope
        (relabelRestrictedMonomials
          (heavyVars univ F (fun i => equationScope (P i)) b₀) e b (P i))) w ≤ b₀ := by
  let S := heavyVars univ F (fun i => equationScope (P i)) b₀
  have hsub :
      {i ∈ I | w ∈ equationScope (relabelRestrictedMonomials S e b (P i))} ⊆
        {i ∈ F | (e.symm w).1 ∈ equationScope (restrictMonomials S b (P i))} := by
    intro i hi
    rw [mem_filter] at hi ⊢
    refine ⟨hIF hi.1, ?_⟩
    rcases hi with ⟨_, hw⟩
    rw [equationScope, mem_biUnion] at hw ⊢
    rcases hw with ⟨M', hM', hwM'⟩
    rw [relabelRestrictedMonomials, mem_image] at hM'
    rcases hM' with ⟨M, hM, rfl⟩
    rw [id_eq, mem_image] at hwM'
    rcases hwM' with ⟨v, hv, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨M, hM, mem_subtype.mp hv⟩
  calc
    varIncidence I
        (fun i => equationScope (relabelRestrictedMonomials S e b (P i))) w
      ≤ varIncidence F
          (fun i => equationScope (restrictMonomials S b (P i))) (e.symm w).1 :=
        card_le_card hsub
    _ ≤ b₀ :=
        varIncidence_equationScope_restrictMonomials_heavyVars_le univ F P b₀
          (fun _ _ => subset_univ _) b (e.symm w).1

end BranchRelabeling

/-! ### Section 5: Neutral variable-coverage scopes and Theorem 2.2 threshold bounds (§5.5–5.6) -/

section NeutralScopesAndThresholds

/-- **§5.5 (neutral variable-coverage factor index set)**: adjoins one neutral factor `Sum.inr v`
for each declared variable `v : ι'` to the equation index set `I`. -/
def withNeutralFactors [Fintype ι'] (I : Finset κ) : Finset (κ ⊕ ι') :=
  I.disjSum univ

/-- **§5.5 (neutral variable-coverage scopes)**: retains `scope i` for `Sum.inl i` and assigns the
singleton scope `{v}` to each neutral factor `Sum.inr v`. -/
def withNeutralScope (scope : κ → Finset ι') : κ ⊕ ι' → Finset ι'
  | Sum.inl i => scope i
  | Sum.inr v => {v}

/-- Adjoining neutral singleton scopes increments the incidence of every variable `v : ι'` by
exactly `1`. -/
theorem varIncidence_withNeutralFactors [Fintype ι'] [DecidableEq ι'] (I : Finset κ)
    (scope : κ → Finset ι') (v : ι') :
    varIncidence (withNeutralFactors I) (withNeutralScope scope) v =
      varIncidence I scope v + 1 := by
  classical
  unfold varIncidence withNeutralFactors
  rw [card_filter, sum_disjSum, ← card_filter, ← card_filter]
  congr 1
  have hfilter :
      ({w : ι' | v ∈ ({w} : Finset ι')} : Finset ι') = {v} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton, eq_comm]
  change #({w ∈ (univ : Finset ι') | v ∈ ({w} : Finset ι')}) = 1
  rw [hfilter, card_singleton]

/-- Every declared variable `v : ι'` has incidence at least `1` after adjoining neutral scopes. -/
theorem one_le_varIncidence_withNeutralFactors [Fintype ι'] [DecidableEq ι'] (I : Finset κ)
    (scope : κ → Finset ι') (v : ι') :
    1 ≤ varIncidence (withNeutralFactors I) (withNeutralScope scope) v := by
  rw [varIncidence_withNeutralFactors]
  omega

/-- If `varIncidence I scope v ≤ b₀`, then after adjoining neutral scopes the variable incidence is
at most `b₀ + 1`. -/
theorem varIncidence_withNeutralFactors_le [Fintype ι'] [DecidableEq ι'] {I : Finset κ}
    {scope : κ → Finset ι'} {v : ι'} {b₀ : ℕ} (hv : varIncidence I scope v ≤ b₀) :
    varIncidence (withNeutralFactors I) (withNeutralScope scope) v ≤ b₀ + 1 := by
  rw [varIncidence_withNeutralFactors]
  exact Nat.add_le_add_right hv 1

/-- Adjoining neutral singleton scopes adds `Fintype.card ι'` to `totalIncidence`. -/
theorem totalIncidence_withNeutralFactors [Fintype ι'] (I : Finset κ) (scope : κ → Finset ι') :
    totalIncidence (withNeutralFactors I) (withNeutralScope scope) =
      totalIncidence I scope + Fintype.card ι' := by
  rw [totalIncidence, withNeutralFactors, sum_disjSum, totalIncidence]
  congr 1
  simp only [withNeutralScope, card_singleton, sum_const, card_univ, smul_eq_mul, mul_one]

/-- **§5.5 ($M' \ge n'$)**: after adjoining neutral singleton scopes, the total incidence is at
least `Fintype.card ι'`. -/
theorem card_le_totalIncidence_withNeutralFactors [Fintype ι'] (I : Finset κ)
    (scope : κ → Finset ι') :
    Fintype.card ι' ≤ totalIncidence (withNeutralFactors I) (withNeutralScope scope) := by
  rw [totalIncidence_withNeutralFactors]
  exact Nat.le_add_left _ _

/-- **§5.5 (heavy-variable threshold $b_0 = \lceil M s / n \rceil$)**: integer ceiling of
`M * s / n`. -/
def heavyThreshold (M n s : ℕ) : ℕ :=
  (M * s + n - 1) / n

/-- When `1 ≤ n`, `M * s ≤ heavyThreshold M n s * n`. -/
theorem mul_le_heavyThreshold_mul {M n s : ℕ} (hn : 1 ≤ n) :
    M * s ≤ heavyThreshold M n s * n := by
  unfold heavyThreshold
  have hmod := Nat.div_add_mod (M * s + n - 1) n
  have hlt : (M * s + n - 1) % n < n := Nat.mod_lt _ hn
  rw [Nat.mul_comm ((M * s + n - 1) / n) n]
  omega

/-- **§5.5 ($|S| \le n / s$)**: whenever `totalIncidence F scope * s ≤ b₀ * #V`, `1 ≤ b₀`,
`1 ≤ s`, and `∀ i ∈ F, scope i ⊆ V`, the heavy-variable set `heavyVars V F scope b₀` has
cardinality at most `#V / s`. -/
theorem card_heavyVars_le_card_div [DecidableEq ι] (V : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) {b₀ s : ℕ} (hb₀ : 1 ≤ b₀) (hs : 1 ≤ s)
    (hV : ∀ i ∈ F, scope i ⊆ V) (hM : totalIncidence F scope * s ≤ b₀ * #V) :
    #(heavyVars V F scope b₀) ≤ #V / s := by
  refine (Nat.le_div_iff_mul_le hs).mpr ?_
  have hcard := card_heavyVars_mul_le_totalIncidence V F scope b₀ hV
  have hmul : (#(heavyVars V F scope b₀) * s) * b₀ ≤ #V * b₀ := by
    calc
      (#(heavyVars V F scope b₀) * s) * b₀
        = (#(heavyVars V F scope b₀) * b₀) * s := by ring
      _ ≤ totalIncidence F scope * s := Nat.mul_le_mul_right s hcard
      _ ≤ b₀ * #V := hM
      _ = #V * b₀ := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmul hb₀

/-- **§5.5 ($2^{|S|} \le 2^{n / s}$)**: under `totalIncidence F scope * s ≤ b₀ * Fintype.card ι`,
`1 ≤ b₀`, and `1 ≤ s`, there are at most `2 ^ (Fintype.card ι / s)` heavy-variable branches. -/
theorem card_branchAssignments_heavyVars_le_two_pow_div [Fintype ι] [DecidableEq ι]
    (F : Finset κ) (scope : κ → Finset ι) {b₀ s : ℕ} (hb₀ : 1 ≤ b₀) (hs : 1 ≤ s)
    (hM : totalIncidence F scope * s ≤ b₀ * Fintype.card ι) :
    #(branchAssignments (heavyVars univ F scope b₀)) ≤ 2 ^ (Fintype.card ι / s) := by
  rw [card_branchAssignments]
  have hle := card_heavyVars_le_card_div univ F scope hb₀ hs (fun _ _ => subset_univ _)
    (by simpa [card_univ] using hM)
  rw [card_univ] at hle
  exact Nat.pow_le_pow_right (by decide) hle

/-- **§5.5 ($n' = n - |S| \ge n - n / s$)**: under `totalIncidence F scope * s ≤ b₀ * #V`,
`1 ≤ b₀`, `1 ≤ s`, and `∀ i ∈ F, scope i ⊆ V`, the set `V \ heavyVars V F scope b₀` of free
variables has cardinality at least `#V - #V / s`. -/
theorem card_sdiff_heavyVars_ge [DecidableEq ι] (V : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) {b₀ s : ℕ} (hb₀ : 1 ≤ b₀) (hs : 1 ≤ s)
    (hV : ∀ i ∈ F, scope i ⊆ V) (hM : totalIncidence F scope * s ≤ b₀ * #V) :
    #V - #V / s ≤ #(V \ heavyVars V F scope b₀) := by
  have hsub : heavyVars V F scope b₀ ⊆ V := filter_subset _ V
  rw [card_sdiff, inter_eq_left.mpr hsub]
  have hle := card_heavyVars_le_card_div V F scope hb₀ hs hV hM
  omega

/-- **§5.5 ($n' \ge n / 2$ for $s \ge 2$)**: when `2 ≤ s`, `1 ≤ b₀`, `∀ i ∈ F, scope i ⊆ V`, and
`totalIncidence F scope * s ≤ b₀ * #V`, at least half of the variables in `V` remain free after
removing `heavyVars V F scope b₀`: `#V ≤ 2 * #(V \ heavyVars V F scope b₀)` and
`#V / 2 ≤ #(V \ heavyVars V F scope b₀)`. -/
theorem card_sdiff_heavyVars_ge_half [DecidableEq ι] (V : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) {b₀ s : ℕ} (hb₀ : 1 ≤ b₀) (hs : 2 ≤ s)
    (hV : ∀ i ∈ F, scope i ⊆ V) (hM : totalIncidence F scope * s ≤ b₀ * #V) :
    #V ≤ 2 * #(V \ heavyVars V F scope b₀) ∧
      #V / 2 ≤ #(V \ heavyVars V F scope b₀) := by
  have hdiv : #V / s ≤ #V / 2 := Nat.div_le_div_left hs (by decide)
  have hge := card_sdiff_heavyVars_ge V F scope hb₀ (by omega) hV hM
  constructor <;> omega

end NeutralScopesAndThresholds

end Cslib.BitString
