/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Foundations.Data.Polynomial.ParityAmplifier
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sparse polynomial equations over `𝔽₂`, common-zero counting, and heavy-variable branching

A sparse degree-`k` polynomial over `𝔽₂` on the Boolean cube `ι → Bool` is represented by a finite
family `𝓜 : Finset (Finset ι)` of monomials `M ⊆ ι` of size at most `k`, evaluated in any
commutative ring `R` via `Cslib.BitString.monomialSum R 𝓜 x = ∑ M ∈ 𝓜, monomial R M x` and lifted
to `MvPolynomial ι R` via `Cslib.BitString.monomialSumPoly R 𝓜`.

Over `ZMod 2`, `monomialSum (ZMod 2) 𝓜 x = 0` holds if and only if the integer evaluation
`monomialSum ℤ 𝓜 x` is even (`Cslib.BitString.monomialSum_zmod_two_eq_zero_iff_even`). Consequently,
the number of common zeros `Cslib.BitString.commonZeroCount I P` of a system `{P i}_{i ∈ I}` of
polynomial equations over `𝔽₂` equals the sum over the Boolean cube of the product of evenness
indicators of their integer evaluations
(`Cslib.BitString.sum_prod_even_monomialSum_eq_commonZeroCount`).

Combining this identity with the Beigel–Tarui parity-amplifying polynomials and shared-`V`
truncation from `Complexity.Foundations.Data.Polynomial.ParityAmplifier` [Toda][Toda1991],
[Arora and Barak, Section 17.4][AroraBarak09]:
* Substituting any family of polynomials `q : ι → MvPolynomial σ R` of total degree at most `d₀`
  into `monomialSumPoly R (P i)` of degree at most `k` produces a lifted polynomial of total degree
  at most `k * d₀` (`Cslib.BitString.totalDegree_eval₂_monomialSumPoly_le`), so the truncated
  shared-`V` product `S_ℓ(∏ i ∈ I, B_i(V))` has total degree at most `(k * d₀) * (#I + 2 * (ℓ - 1))`
  (`Cslib.BitString.totalDegree_sumCoeffsBelow_prod_parityFactor_eval₂_le`).
* Summing the truncated product over `x : ι → Bool` recovers `commonZeroCount I P` modulo `2 ^ ℓ`
  (`Cslib.BitString.sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount`), and recovers
  `commonZeroCount I P` on the nose via `(· % 2 ^ ℓ)` whenever `Fintype.card ι < ℓ`
  (`Cslib.BitString.emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount`).

Finally, for any system of equations with variable scopes `scope : κ → Finset ι` contained in a
candidate variable set `V` (`∀ i ∈ F, scope i ⊆ V`) and positive incidence threshold `1 ≤ b₀`,
the set `Cslib.BitString.heavyVars V F scope b₀` of variables in `V` appearing in more than `b₀`
scopes has cardinality at most `totalIncidence F scope / b₀`
(`Cslib.BitString.card_heavyVars_le_div`), while every
remaining variable in `V \ heavyVars V F scope b₀` (and in any post-branching restricted equation
scope when `∀ i ∈ I, equationScope (P i) ⊆ V`) has incidence at most `b₀`. Branching on all
`2 ^ #S` assignments to a variable subset `S` and simplifying each equation via
`Cslib.BitString.restrictMonomials` preserves degree bounds, never increases the number of
monomials per equation, and decomposes `commonZeroCount` additively across the branches
(`Cslib.BitString.commonZeroCount_eq_sum_branches`).

## Main definitions

* `Cslib.BitString.monomialSum`: evaluation `∑ M ∈ 𝓜, monomial R M x` of a family of monomials.
* `Cslib.BitString.monomialPoly`, `Cslib.BitString.monomialSumPoly`: formal multilinear polynomial
  lifts in `MvPolynomial ι R`.
* `Cslib.BitString.IsCommonZero`, `Cslib.BitString.commonZeroCount`: common zeros of a system of
  `𝔽₂` polynomial equations on `ι → Bool` and their count.
* `Cslib.BitString.varIncidence`, `Cslib.BitString.totalIncidence`, `Cslib.BitString.heavyVars`:
  variable-equation incidence counts and heavy-variable set above threshold `b₀`.
* `Cslib.BitString.patchAssignment`, `Cslib.BitString.restrictMonomials`: patching a branch
  assignment on `S` and reducing a monomial family modulo `2` after specializing `S`.
* `Cslib.BitString.parityBaseDigitCleared`, `Cslib.BitString.hPolyCleared`,
  `Cslib.BitString.parityFactorCleared`, `Cslib.BitString.clearedMonomialPoly`,
  `Cslib.BitString.clearedMonomialSumPoly`: cleared-denominator parity factors and degree-`k`
  homogenized monomial sums from §5.4 and Appendix B.2.

## Main results

* `Cslib.BitString.monomialSum_zmod_two_eq_zero_iff_even`: `𝔽₂` vanishing iff even `ℤ` evaluation.
* `Cslib.BitString.sum_prod_even_monomialSum_eq_commonZeroCount`: equation (5.1) expressing
  `commonZeroCount` as the cube sum of products of evenness indicators.
* `Cslib.BitString.totalDegree_sumCoeffsBelow_prod_parityFactor_eval₂_le`: total-degree bound
  `(k * d₀) * (#I + 2 * (ℓ - 1))` for the truncated product under degree-`d₀` replacements.
* `Cslib.BitString.emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount`: exact recovery of
  `commonZeroCount` modulo `2 ^ ℓ` when `Fintype.card ι < ℓ`.
* `Cslib.BitString.card_heavyVars_le_div` and `Cslib.BitString.varIncidence_sdiff_heavyVars_le`:
  heavy-variable cardinality bound and light-variable incidence bound.
* `Cslib.BitString.monomialSum_zmod_two_restrictMonomials` and
  `Cslib.BitString.commonZeroCount_eq_sum_branches`: exact `𝔽₂` specialization and additive branch
  decomposition of `commonZeroCount`.
* `Cslib.BitString.prod_parityFactorCleared_mul`,
  `Cslib.BitString.coeffNorm1_clearedMonomialSumPoly_le`, and
  `Cslib.BitString.coeffNorm1_coeff_parityFactorCleared_le`: cleared-denominator homogenization
  ($\Delta = d_{\text{den}}^k$, $\Gamma = \Delta^{2\ell-1}$, $\Omega = \Gamma^{\#I}$) and numerator
  `ℓ₁`-norm bounds from §5.4 and Appendix B.2.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.1, 5.3, 5.4, 5.5, and Appendix B.2)
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset MvPolynomial

variable {ι κ σ R : Type*}

/-! ### 1. Monomial sums, integer lifts, and `commonZeroCount` -/

/-- The sum of the monomials in `𝓜 : Finset (Finset ι)` evaluated at `x : ι → Bool` in `R`. -/
def monomialSum (R : Type*) [CommRing R] (𝓜 : Finset (Finset ι)) (x : ι → Bool) : R :=
  ∑ M ∈ 𝓜, monomial R M x

/-- The empty family of monomials evaluates to `0`. -/
@[simp]
theorem monomialSum_empty (R : Type*) [CommRing R] (x : ι → Bool) :
    monomialSum R (∅ : Finset (Finset ι)) x = 0 := by
  simp only [monomialSum, sum_empty]

/-- A singleton family `{M}` evaluates to `monomial R M x`. -/
@[simp]
theorem monomialSum_singleton (R : Type*) [CommRing R] (M : Finset ι) (x : ι → Bool) :
    monomialSum R {M} x = monomial R M x := by
  simp only [monomialSum, sum_singleton]

/-- `monomialSum R 𝓜 x` equals the cast to `R` of the number of monomials `M ∈ 𝓜` satisfied by
`x`. -/
theorem monomialSum_eq_card_filter (R : Type*) [CommRing R] (𝓜 : Finset (Finset ι))
    (x : ι → Bool) :
    monomialSum R 𝓜 x = (#{M ∈ 𝓜 | ∀ v ∈ M, x v = true} : R) := by
  unfold monomialSum
  simp only [monomial_apply, sum_boole]

/-- A monomial sum vanishes in `ZMod 2` at `x` if and only if its integer lift `monomialSum ℤ 𝓜 x`
is even. -/
theorem monomialSum_zmod_two_eq_zero_iff_even (𝓜 : Finset (Finset ι)) (x : ι → Bool) :
    monomialSum (ZMod 2) 𝓜 x = 0 ↔ Even (monomialSum ℤ 𝓜 x) := by
  rw [monomialSum_eq_card_filter (ZMod 2), monomialSum_eq_card_filter ℤ,
    ZMod.natCast_eq_zero_iff_even, Int.even_natCast]

/-- An assignment `x : ι → Bool` is a common zero of the family `{P i}_{i ∈ I}` over `𝔽₂` if every
equation `P i` (`i ∈ I`) evaluates to `0` in `ZMod 2` at `x`. -/
def IsCommonZero (I : Finset κ) (P : κ → Finset (Finset ι)) (x : ι → Bool) : Prop :=
  ∀ i ∈ I, monomialSum (ZMod 2) (P i) x = 0

instance instDecidableIsCommonZero (I : Finset κ) (P : κ → Finset (Finset ι))
    (x : ι → Bool) : Decidable (IsCommonZero I P x) := by
  unfold IsCommonZero
  infer_instance

/-- `x` is a common zero over `𝔽₂` if and only if all integer evaluations `monomialSum ℤ (P i) x`
(`i ∈ I`) are even. -/
theorem isCommonZero_iff_forall_even (I : Finset κ) (P : κ → Finset (Finset ι)) (x : ι → Bool) :
    IsCommonZero I P x ↔ ∀ i ∈ I, Even (monomialSum ℤ (P i) x) := by
  unfold IsCommonZero
  exact forall₂_congr fun i _ => monomialSum_zmod_two_eq_zero_iff_even (P i) x

/-- The number of common zeros `x : ι → Bool` of the polynomial system `{P i}_{i ∈ I}` over `𝔽₂`. -/
def commonZeroCount [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) : ℕ :=
  #{x : ι → Bool | IsCommonZero I P x}

/-- At any assignment `x`, the product of the evenness indicators of `monomialSum ℤ (P i) x` over
`i ∈ I` is `1` if `IsCommonZero I P x` and `0` otherwise. -/
theorem prod_even_monomialSum_eq_ite (I : Finset κ) (P : κ → Finset (Finset ι)) (x : ι → Bool) :
    (∏ i ∈ I, if Even (monomialSum ℤ (P i) x) then (1 : ℤ) else 0) =
      if IsCommonZero I P x then 1 else 0 := by
  simp only [prod_boole, isCommonZero_iff_forall_even]

/-- **Equation (5.1)**: the common-zero count of `{P i}_{i ∈ I}` over `𝔽₂` equals the sum over the
Boolean cube of the product of evenness indicators of the integer lifts `monomialSum ℤ (P i) x`. -/
theorem sum_prod_even_monomialSum_eq_commonZeroCount [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) :
    (∑ x : ι → Bool, ∏ i ∈ I, if Even (monomialSum ℤ (P i) x) then (1 : ℤ) else 0) =
      commonZeroCount I P := by
  calc
    (∑ x : ι → Bool, ∏ i ∈ I, if Even (monomialSum ℤ (P i) x) then (1 : ℤ) else 0)
      = ∑ x : ι → Bool, if IsCommonZero I P x then (1 : ℤ) else 0 := by
        refine sum_congr rfl fun x _ => ?_
        exact prod_even_monomialSum_eq_ite I P x
    _ = commonZeroCount I P := by
        rw [commonZeroCount, sum_boole]

/-- An empty system of equations has `2 ^ Fintype.card ι` common zeros. -/
@[simp]
theorem commonZeroCount_empty [Fintype ι] [DecidableEq ι] (P : κ → Finset (Finset ι)) :
    commonZeroCount (∅ : Finset κ) P = 2 ^ Fintype.card ι := by
  have htrue : ∀ x ∈ (univ : Finset (ι → Bool)), IsCommonZero (∅ : Finset κ) P x := by
    intro x _ i hi
    exact False.elim (notMem_empty i hi)
  rw [commonZeroCount, filter_true_of_mem htrue, card_univ, Fintype.card_fun, Fintype.card_bool]

/-- If some equation `i ∈ I` is the constant polynomial `1` (`P i = {∅}`), there are no common
zeros. -/
theorem commonZeroCount_eq_zero_of_singleton_empty [Fintype ι] [DecidableEq ι] {I : Finset κ}
    {P : κ → Finset (Finset ι)} {i : κ} (hi : i ∈ I) (hP : P i = {∅}) :
    commonZeroCount I P = 0 := by
  rw [commonZeroCount, card_eq_zero, filter_eq_empty_iff]
  intro x _ hcz
  have h1 := hcz i hi
  rw [hP, monomialSum_singleton, monomial_empty, Pi.one_apply] at h1
  exact one_ne_zero h1

/-- `commonZeroCount I P` is at most `2 ^ Fintype.card ι`. -/
theorem commonZeroCount_le_two_pow [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) :
    commonZeroCount I P ≤ 2 ^ Fintype.card ι := by
  rw [commonZeroCount]
  calc
    #{x : ι → Bool | IsCommonZero I P x} ≤ #(univ : Finset (ι → Bool)) := card_filter_le _ _
    _ = 2 ^ Fintype.card ι := by
      rw [card_univ, Fintype.card_fun, Fintype.card_bool]

/-! ### 2. Formal multilinear lifts and replacement total-degree bounds -/

/-- The formal multilinear monomial `∏ v ∈ M, X v` in `MvPolynomial ι R`. -/
def monomialPoly (R : Type*) [CommSemiring R] (M : Finset ι) : MvPolynomial ι R :=
  ∏ v ∈ M, X v

/-- The formal multilinear polynomial `∑ M ∈ 𝓜, ∏ v ∈ M, X v` in `MvPolynomial ι R`. -/
def monomialSumPoly (R : Type*) [CommSemiring R] (𝓜 : Finset (Finset ι)) : MvPolynomial ι R :=
  ∑ M ∈ 𝓜, monomialPoly R M

/-- Evaluating `monomialPoly R M` at `v ↦ bitVal R (x v)` gives `monomial R M x`. -/
@[simp]
theorem aeval_bitVal_monomialPoly (R : Type*) [CommRing R] (M : Finset ι) (x : ι → Bool) :
    aeval (fun v => bitVal R (x v)) (monomialPoly R M) = monomial R M x := by
  simp only [monomialPoly, monomial, map_prod, aeval_X]

/-- Evaluating `monomialSumPoly R 𝓜` at `v ↦ bitVal R (x v)` gives `monomialSum R 𝓜 x`. -/
@[simp]
theorem aeval_bitVal_monomialSumPoly (R : Type*) [CommRing R] (𝓜 : Finset (Finset ι))
    (x : ι → Bool) :
    aeval (fun v => bitVal R (x v)) (monomialSumPoly R 𝓜) = monomialSum R 𝓜 x := by
  simp only [monomialSumPoly, monomialSum, map_sum, aeval_bitVal_monomialPoly]

/-- Evaluating `monomialPoly R M` via `eval₂ f q` gives `∏ v ∈ M, q v`. -/
theorem eval₂_monomialPoly {S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (q : ι → S) (M : Finset ι) :
    (monomialPoly R M).eval₂ f q = ∏ v ∈ M, q v := by
  unfold monomialPoly
  rw [← coe_eval₂Hom, map_prod]
  refine prod_congr rfl fun v _ => ?_
  simp only [coe_eval₂Hom, eval₂_X]

/-- Substituting polynomials `q v` of total degree at most `d₀` into `monomialPoly R M` produces a
polynomial of total degree at most `#M * d₀`. -/
theorem totalDegree_eval₂_monomialPoly_le [CommSemiring R] (f : R →+* MvPolynomial σ R)
    (q : ι → MvPolynomial σ R) {M : Finset ι} {d₀ : ℕ}
    (hq : ∀ v ∈ M, (q v).totalDegree ≤ d₀) :
    ((monomialPoly R M).eval₂ f q).totalDegree ≤ #M * d₀ := by
  rw [eval₂_monomialPoly]
  refine (totalDegree_finsetProd M q).trans ?_
  exact (sum_le_card_nsmul M (fun v => (q v).totalDegree) d₀ hq).trans
    (by simp only [smul_eq_mul, le_rfl])

/-- Substituting polynomials `q v` of total degree at most `d₀` into `monomialSumPoly R 𝓜` of
degree at most `k` produces a polynomial of total degree at most `k * d₀`. -/
theorem totalDegree_eval₂_monomialSumPoly_le [CommSemiring R] (f : R →+* MvPolynomial σ R)
    (q : ι → MvPolynomial σ R) {𝓜 : Finset (Finset ι)} {k d₀ : ℕ}
    (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hq : ∀ M ∈ 𝓜, ∀ v ∈ M, (q v).totalDegree ≤ d₀) :
    ((monomialSumPoly R 𝓜).eval₂ f q).totalDegree ≤ k * d₀ := by
  unfold monomialSumPoly
  rw [← coe_eval₂Hom, map_sum]
  refine (totalDegree_finsetSum 𝓜 _).trans (Finset.sup_le fun M hM => ?_)
  rw [coe_eval₂Hom]
  exact (totalDegree_eval₂_monomialPoly_le f q (hq M hM)).trans
    (Nat.mul_le_mul_right d₀ (hk M hM))

/-! ### 3. Truncated parity-factor degree bound (eq. 5.5) and count recovery (eq. 5.4) -/

/-- **Equation (5.5) (truncated product degree bound under variable replacement)**: under the same
hypotheses, the truncated sum `S_ℓ(∏ i ∈ I, B_i(V))` has total degree at most
`(k * d₀) * (#I + 2 * (ℓ - 1))`. -/
theorem totalDegree_sumCoeffsBelow_prod_parityFactor_eval₂_le [CommRing R] (I : Finset κ)
    {P : κ → Finset (Finset ι)} (ℓ : ℕ) {k d₀ : ℕ}
    (f : R →+* MvPolynomial σ R) (q : κ → ι → MvPolynomial σ R)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hq : ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (q i v).totalDegree ≤ d₀) :
    (Polynomial.sumCoeffsBelow ℓ
      (∏ i ∈ I, Polynomial.parityFactor ℓ ((monomialSumPoly R (P i)).eval₂ f (q i)))).totalDegree ≤
      (k * d₀) * (#I + 2 * (ℓ - 1)) :=
  Polynomial.totalDegree_sumCoeffsBelow_prod_parityFactor_le I ℓ fun i hi =>
    totalDegree_eval₂_monomialSumPoly_le f (q i) (hk i hi) (hq i hi)

/-- `Polynomial.sumCoeffsBelow ℓ` commutes with finite sums. -/
theorem sumCoeffsBelow_sum {α A : Type*} [Semiring A] (s : Finset α) (ℓ : ℕ)
    (F : α → Polynomial A) :
    Polynomial.sumCoeffsBelow ℓ (∑ a ∈ s, F a) =
      ∑ a ∈ s, Polynomial.sumCoeffsBelow ℓ (F a) := by
  unfold Polynomial.sumCoeffsBelow
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Polynomial.finsetSum_coeff]

/-- **Equation (5.4) (congruence modulo `2 ^ ℓ`)**: for `ℓ ≥ 1`, summing the truncated product of
parity factors of `monomialSum ℤ (P i) x` over `x : ι → Bool` recovers `commonZeroCount I P`
modulo `2 ^ ℓ`. -/
theorem sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∑ x : ι → Bool,
      Polynomial.sumCoeffsBelow ℓ (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x))) ≡
      (commonZeroCount I P : ℤ) [ZMOD (2 : ℤ) ^ ℓ] := by
  rw [← sum_prod_even_monomialSum_eq_commonZeroCount I P]
  exact Int.ModEq.sum fun x _ =>
    Polynomial.sumCoeffsBelow_prod_parityFactor_modEq I hℓ (fun i => monomialSum ℤ (P i) x)

/-- **Equation (5.4) (exact recovery via `% 2 ^ ℓ`)**: when `Fintype.card ι < ℓ` (in particular for
`ℓ = Fintype.card ι + 1`), reducing the cube sum of truncated parity-factor products modulo
`2 ^ ℓ` recovers `commonZeroCount I P` on the nose. -/
theorem emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) {ℓ : ℕ} (hℓ : Fintype.card ι < ℓ) :
    (∑ x : ι → Bool,
      Polynomial.sumCoeffsBelow ℓ (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x))) %
      ((2 : ℤ) ^ ℓ) = commonZeroCount I P := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hmod :
      (∑ x : ι → Bool,
        Polynomial.sumCoeffsBelow ℓ (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x))) %
        ((2 : ℤ) ^ ℓ) = (commonZeroCount I P : ℤ) % ((2 : ℤ) ^ ℓ) :=
    sum_sumCoeffsBelow_prod_parityFactor_modEq_commonZeroCount I P hℓ1
  rw [hmod, Int.emod_eq_of_lt (Nat.cast_nonneg _)]
  have hle : (commonZeroCount I P : ℤ) ≤ (2 : ℤ) ^ Fintype.card ι := by
    exact_mod_cast commonZeroCount_le_two_pow I P
  have hlt : (2 : ℤ) ^ Fintype.card ι < (2 : ℤ) ^ ℓ := by
    exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < 2) hℓ
  exact lt_of_le_of_lt hle hlt

/-! ### 4. Heavy-variable incidence bounds (§5.5) -/

/-- The number of constraints `i ∈ F` whose scope `scope i` contains variable `v`. -/
def varIncidence [DecidableEq ι] (F : Finset κ) (scope : κ → Finset ι) (v : ι) : ℕ :=
  #{i ∈ F | v ∈ scope i}

/-- The total variable-constraint incidence `∑ i ∈ F, #(scope i)`. -/
def totalIncidence (F : Finset κ) (scope : κ → Finset ι) : ℕ :=
  ∑ i ∈ F, #(scope i)

/-- Double-counting variable-constraint incidences over a universe `U` containing all scopes. -/
theorem sum_varIncidence_eq_totalIncidence [DecidableEq ι] (U : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) (hU : ∀ i ∈ F, scope i ⊆ U) :
    ∑ v ∈ U, varIncidence F scope v = totalIncidence F scope := by
  unfold varIncidence totalIncidence
  simp only [card_eq_sum_ones]
  have h1 : (∑ v ∈ U, ∑ x ∈ {i ∈ F | v ∈ scope i}, 1) =
      ∑ v ∈ U, ∑ i ∈ F, if v ∈ scope i then 1 else 0 := by
    refine sum_congr rfl fun v _ => ?_
    rw [sum_filter]
  rw [h1, sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (hU i hi)]

/-- If every constraint in `F` has scope size at most `k`, then `totalIncidence F scope` is at
most `k * #F`. -/
theorem totalIncidence_le_mul_card (F : Finset κ) (scope : κ → Finset ι) {k : ℕ}
    (hk : ∀ i ∈ F, #(scope i) ≤ k) :
    totalIncidence F scope ≤ k * #F := by
  unfold totalIncidence
  refine (sum_le_card_nsmul F (fun i => #(scope i)) k hk).trans ?_
  rw [smul_eq_mul, mul_comm]

/-- The set of heavy variables in `U` whose incidence in `F` strictly exceeds `b₀`. -/
def heavyVars [DecidableEq ι] (U : Finset ι) (F : Finset κ) (scope : κ → Finset ι)
    (b₀ : ℕ) : Finset ι :=
  {v ∈ U | b₀ < varIncidence F scope v}

/-- Markov / counting bound: `#(heavyVars U F scope b₀) * (b₀ + 1) ≤ totalIncidence F scope`. -/
theorem card_heavyVars_mul_succ_le_totalIncidence [DecidableEq ι] (U : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) (b₀ : ℕ) (hU : ∀ i ∈ F, scope i ⊆ U) :
    #(heavyVars U F scope b₀) * (b₀ + 1) ≤ totalIncidence F scope := by
  rw [← sum_varIncidence_eq_totalIncidence U F scope hU]
  calc
    #(heavyVars U F scope b₀) * (b₀ + 1)
      = ∑ _v ∈ heavyVars U F scope b₀, (b₀ + 1) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ heavyVars U F scope b₀, varIncidence F scope v := by
        refine sum_le_sum fun v hv => ?_
        rw [heavyVars, mem_filter] at hv
        exact hv.2
    _ ≤ ∑ v ∈ U, varIncidence F scope v :=
        sum_le_sum_of_subset (filter_subset _ U)

/-- `#(heavyVars U F scope b₀) * b₀ ≤ totalIncidence F scope`. -/
theorem card_heavyVars_mul_le_totalIncidence [DecidableEq ι] (U : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) (b₀ : ℕ) (hU : ∀ i ∈ F, scope i ⊆ U) :
    #(heavyVars U F scope b₀) * b₀ ≤ totalIncidence F scope := by
  refine (Nat.mul_le_mul_left _ (Nat.le_succ b₀)).trans ?_
  exact card_heavyVars_mul_succ_le_totalIncidence U F scope b₀ hU

/-- **§5.5 (heavy-variable cardinality bound)**: for `b₀ > 0`, the number of heavy variables is at
most `totalIncidence F scope / b₀`. -/
theorem card_heavyVars_le_div [DecidableEq ι] (U : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) {b₀ : ℕ} (hb₀ : 0 < b₀) (hU : ∀ i ∈ F, scope i ⊆ U) :
    #(heavyVars U F scope b₀) ≤ totalIncidence F scope / b₀ :=
  (Nat.le_div_iff_mul_le hb₀).mpr (card_heavyVars_mul_le_totalIncidence U F scope b₀ hU)

/-- Every variable in `U \ heavyVars U F scope b₀` has incidence at most `b₀`. -/
theorem varIncidence_le_of_mem_sdiff_heavyVars [DecidableEq ι] {U : Finset ι} {F : Finset κ}
    {scope : κ → Finset ι} {b₀ : ℕ} {v : ι} (hv : v ∈ U \ heavyVars U F scope b₀) :
    varIncidence F scope v ≤ b₀ := by
  rw [mem_sdiff, heavyVars, mem_filter, not_and] at hv
  exact Nat.le_of_not_lt (hv.2 hv.1)

/-- Removing `heavyVars U F scope b₀` from every scope reduces the incidence of **every** variable
`v : ι` to at most `b₀`. -/
theorem varIncidence_sdiff_heavyVars_le [DecidableEq ι] (U : Finset ι) (F : Finset κ)
    (scope : κ → Finset ι) (b₀ : ℕ) (hU : ∀ i ∈ F, scope i ⊆ U) (v : ι) :
    varIncidence F (fun i => scope i \ heavyVars U F scope b₀) v ≤ b₀ := by
  by_cases hv : v ∈ U \ heavyVars U F scope b₀
  · have hsub : {i ∈ F | v ∈ scope i \ heavyVars U F scope b₀} ⊆ {i ∈ F | v ∈ scope i} := by
      intro i hi
      rw [mem_filter] at hi ⊢
      exact ⟨hi.1, (mem_sdiff.mp hi.2).1⟩
    exact (card_le_card hsub).trans (varIncidence_le_of_mem_sdiff_heavyVars hv)
  · have hzero : varIncidence F (fun i => scope i \ heavyVars U F scope b₀) v = 0 := by
      rw [varIncidence, card_eq_zero, filter_eq_empty_iff]
      intro i hi hvi
      rw [mem_sdiff] at hvi
      apply hv
      exact mem_sdiff.mpr ⟨hU i hi hvi.1, hvi.2⟩
    rw [hzero]
    exact Nat.zero_le _

/-! ### 5. Exact branching on a variable subset `S` (§5.5) -/

/-- The assignment that takes values from `b` on `S` and from `y` outside `S`. -/
def patchAssignment [DecidableEq ι] (S : Finset ι) (b y : ι → Bool) (v : ι) : Bool :=
  if v ∈ S then b v else y v

/-- On `S`, `patchAssignment S b y` agrees with `b`. -/
@[simp]
theorem patchAssignment_of_mem [DecidableEq ι] {S : Finset ι} {b y : ι → Bool} {v : ι}
    (hv : v ∈ S) :
    patchAssignment S b y v = b v :=
  ite_eq_left hv

/-- Outside `S`, `patchAssignment S b y` agrees with `y`. -/
@[simp]
theorem patchAssignment_of_notMem [DecidableEq ι] {S : Finset ι} {b y : ι → Bool} {v : ι}
    (hv : v ∉ S) :
    patchAssignment S b y v = y v :=
  ite_eq_right hv

/-- A monomial `M` evaluated on `patchAssignment S b y` factors into the indicator that `b` is all
`true` on `M ∩ S` times `monomial R (M \ S) y`. -/
theorem monomial_patchAssignment (R : Type*) [CommRing R] [DecidableEq ι] (S : Finset ι)
    (b y : ι → Bool) (M : Finset ι) :
    monomial R M (patchAssignment S b y) =
      (if ∀ v ∈ M ∩ S, b v = true then 1 else 0) * monomial R (M \ S) y := by
  rw [monomial_apply, monomial_apply]
  have hiff : (∀ v ∈ M, patchAssignment S b y v = true) ↔
      (∀ v ∈ M ∩ S, b v = true) ∧ (∀ v ∈ M \ S, y v = true) := by
    constructor
    · intro h
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [mem_inter] at hv
        simpa only [patchAssignment, hv.2, ↓reduceIte] using h v hv.1
      · rw [mem_sdiff] at hv
        simpa only [patchAssignment, hv.2, ↓reduceIte] using h v hv.1
    · rintro ⟨h1, h2⟩ v hv
      by_cases hvs : v ∈ S
      · simp only [patchAssignment, hvs, ↓reduceIte]
        exact h1 v (mem_inter.mpr ⟨hv, hvs⟩)
      · simp only [patchAssignment, hvs, ↓reduceIte]
        exact h2 v (mem_sdiff.mpr ⟨hv, hvs⟩)
  by_cases h1 : ∀ v ∈ M ∩ S, b v = true
  · by_cases h2 : ∀ v ∈ M \ S, y v = true
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, mul_one]
    · rw [ite_eq_right (fun hc => h2 (hiff.mp hc).2), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun hc => h1 (hiff.mp hc).1), ite_eq_right h1, zero_mul]

/-- The reduced family of monomials in the remaining variables after specializing `S` to `b` and
combining duplicate restricted monomials `M \ S` modulo `2`. -/
def restrictMonomials [DecidableEq ι] (S : Finset ι) (b : ι → Bool)
    (𝓜 : Finset (Finset ι)) : Finset (Finset ι) :=
  {M' ∈ 𝓜.image (· \ S) | Odd #{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true}}

/-- Every monomial in `restrictMonomials S b 𝓜` is disjoint from `S`. -/
theorem disjoint_of_mem_restrictMonomials [DecidableEq ι] {S : Finset ι} {b : ι → Bool}
    {𝓜 : Finset (Finset ι)} {M' : Finset ι} (hM' : M' ∈ restrictMonomials S b 𝓜) :
    Disjoint M' S := by
  rw [restrictMonomials, mem_filter, mem_image] at hM'
  rcases hM'.1 with ⟨M, _, rfl⟩
  exact sdiff_disjoint

/-- Specializing `S` never increases the degree of any monomial: if `∀ M ∈ 𝓜, #M ≤ k`, then
`∀ M' ∈ restrictMonomials S b 𝓜, #M' ≤ k`. -/
theorem card_le_of_mem_restrictMonomials [DecidableEq ι] {S : Finset ι} {b : ι → Bool}
    {𝓜 : Finset (Finset ι)} {k : ℕ} (hk : ∀ M ∈ 𝓜, #M ≤ k)
    {M' : Finset ι} (hM' : M' ∈ restrictMonomials S b 𝓜) :
    #M' ≤ k := by
  rw [restrictMonomials, mem_filter, mem_image] at hM'
  rcases hM'.1 with ⟨M, hM, rfl⟩
  exact (card_le_card sdiff_subset).trans (hk M hM)

/-- Specializing `S` and reducing modulo `2` never increases the number of monomials:
`#(restrictMonomials S b 𝓜) ≤ #𝓜`. -/
theorem card_restrictMonomials_le [DecidableEq ι] (S : Finset ι) (b : ι → Bool)
    (𝓜 : Finset (Finset ι)) :
    #(restrictMonomials S b 𝓜) ≤ #𝓜 :=
  (card_filter_le _ _).trans card_image_le

/-- Over any commutative ring `R`, `monomialSum R 𝓜 (patchAssignment S b y)` groups by restricted
monomials `M' ∈ 𝓜.image (· \ S)`. -/
theorem monomialSum_patchAssignment_eq_sum_image (R : Type*) [CommRing R] [DecidableEq ι]
    (S : Finset ι) (b y : ι → Bool) (𝓜 : Finset (Finset ι)) :
    monomialSum R 𝓜 (patchAssignment S b y) =
      ∑ M' ∈ 𝓜.image (· \ S),
        (#{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true} : R) * monomial R M' y := by
  unfold monomialSum
  rw [← sum_fiberwise_of_maps_to (fun M hM => mem_image_of_mem (· \ S) hM)]
  refine sum_congr rfl fun M' _ => ?_
  have hcongr :
      (∑ M ∈ {M ∈ 𝓜 | M \ S = M'}, monomial R M (patchAssignment S b y)) =
        ∑ M ∈ {M ∈ 𝓜 | M \ S = M'},
          (if ∀ v ∈ M ∩ S, b v = true then (1 : R) else 0) * monomial R M' y := by
    refine sum_congr rfl fun M hM => ?_
    rw [mem_filter] at hM
    rw [monomial_patchAssignment, hM.2]
  rw [hcongr, ← sum_mul, sum_boole, filter_filter]

/-- **§5.5 (exact `𝔽₂` specialization)**: over `ZMod 2`, evaluating `restrictMonomials S b 𝓜` at
`y` equals evaluating the original family `𝓜` at `patchAssignment S b y`. -/
theorem monomialSum_zmod_two_restrictMonomials [DecidableEq ι] (S : Finset ι) (b y : ι → Bool)
    (𝓜 : Finset (Finset ι)) :
    monomialSum (ZMod 2) (restrictMonomials S b 𝓜) y =
      monomialSum (ZMod 2) 𝓜 (patchAssignment S b y) := by
  rw [monomialSum_patchAssignment_eq_sum_image, monomialSum, restrictMonomials, sum_filter]
  refine sum_congr rfl fun M' _ => ?_
  by_cases hodd : Odd #{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true}
  · have hcast : (#{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true} : ZMod 2) = 1 := by
      rcases hodd with ⟨m, hm⟩
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, h2, zero_mul, zero_add]
    simp only [hodd, ↓reduceIte, hcast, one_mul]
  · have heven : Even #{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true} :=
      Nat.not_odd_iff_even.mp hodd
    have hcast : (#{M ∈ 𝓜 | M \ S = M' ∧ ∀ v ∈ M ∩ S, b v = true} : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff_even.mpr heven)
    simp only [hodd, ↓reduceIte, hcast, zero_mul]

/-- `patchAssignment S b y` is a common zero of `P` if and only if `y` is a common zero of the
specialized system `fun i => restrictMonomials S b (P i)`. -/
theorem isCommonZero_patchAssignment_iff [DecidableEq ι] (S : Finset ι) (b y : ι → Bool)
    (I : Finset κ) (P : κ → Finset (Finset ι)) :
    IsCommonZero I P (patchAssignment S b y) ↔
      IsCommonZero I (fun i => restrictMonomials S b (P i)) y := by
  unfold IsCommonZero
  refine forall₂_congr fun i _ => ?_
  rw [monomialSum_zmod_two_restrictMonomials]

/-- Canonical branch assignments supported on `S` (`false` outside `S`). -/
def branchAssignments [Fintype ι] [DecidableEq ι] (S : Finset ι) : Finset (ι → Bool) :=
  {b : ι → Bool | ∀ v ∉ S, b v = false}

/-- Canonical subproblem assignments supported outside `S` (`false` on `S`). -/
def subproblemAssignments [Fintype ι] [DecidableEq ι] (S : Finset ι) : Finset (ι → Bool) :=
  {y : ι → Bool | ∀ v ∈ S, y v = false}

/-- There are `2 ^ #S` canonical branch assignments in `branchAssignments S`. -/
theorem card_branchAssignments [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    #(branchAssignments S) = 2 ^ #S := by
  have hbij :
      #(branchAssignments S) = #(univ : Finset (S → Bool)) := by
    refine card_nbij' (fun b (v : S) => b v.1)
      (fun g v => if hv : v ∈ S then g ⟨v, hv⟩ else false) ?_ ?_ ?_ ?_
    · intro b _
      exact mem_coe.mpr (mem_univ _)
    · intro g _
      rw [mem_coe, branchAssignments, mem_filter]
      refine ⟨mem_univ _, fun v hv => dite_eq_right hv⟩
    · intro b hb
      rw [mem_coe, branchAssignments, mem_filter] at hb
      funext v
      by_cases hv : v ∈ S
      · exact dite_eq_left hv
      · exact (dite_eq_right hv).trans (hb.2 v hv).symm
    · intro g _
      funext ⟨v, hv⟩
      exact dite_eq_left hv
  rw [hbij, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- The variable scope `⋃ M ∈ 𝓜, M` of a family `𝓜` of monomials. -/
def equationScope [DecidableEq ι] (𝓜 : Finset (Finset ι)) : Finset ι :=
  𝓜.biUnion id

/-- If every monomial in `𝓜` has size at most `k`, then `#(equationScope 𝓜) ≤ k * #𝓜`. -/
theorem card_equationScope_le [DecidableEq ι] {𝓜 : Finset (Finset ι)} {k : ℕ}
    (hk : ∀ M ∈ 𝓜, #M ≤ k) :
    #(equationScope 𝓜) ≤ k * #𝓜 := by
  unfold equationScope
  refine card_biUnion_le.trans ?_
  refine (sum_le_card_nsmul 𝓜 (fun M => #M) k hk).trans ?_
  rw [smul_eq_mul, mul_comm]

/-- After specializing `S`, the variable scope of `restrictMonomials S b 𝓜` is contained in
`equationScope 𝓜 \ S`. -/
theorem equationScope_restrictMonomials_subset_sdiff [DecidableEq ι] (S : Finset ι)
    (b : ι → Bool) (𝓜 : Finset (Finset ι)) :
    equationScope (restrictMonomials S b 𝓜) ⊆ equationScope 𝓜 \ S := by
  intro v hv
  rw [equationScope, mem_biUnion] at hv
  rcases hv with ⟨M', hM', hvM'⟩
  rw [restrictMonomials, mem_filter, mem_image] at hM'
  rcases hM'.1 with ⟨M, hM, rfl⟩
  rw [id_eq, mem_sdiff] at hvM'
  rw [mem_sdiff, equationScope, mem_biUnion]
  exact ⟨⟨M, hM, hvM'.1⟩, hvM'.2⟩

/-- **§5.5 (post-branching incidence bound)**: after branching on the heavy variables
`S = heavyVars U F (fun i => equationScope (P i)) b₀`, every variable `v : ι` appears in at most
`b₀` reduced scopes `equationScope (restrictMonomials S b (P i))` (`i ∈ F`). -/
theorem varIncidence_equationScope_restrictMonomials_heavyVars_le [DecidableEq ι]
    (U : Finset ι) (F : Finset κ) (P : κ → Finset (Finset ι)) (b₀ : ℕ)
    (hU : ∀ i ∈ F, equationScope (P i) ⊆ U) (b : ι → Bool) (v : ι) :
    varIncidence F
      (fun i => equationScope
        (restrictMonomials (heavyVars U F (fun i => equationScope (P i)) b₀) b (P i))) v ≤
      b₀ := by
  let S := heavyVars U F (fun i => equationScope (P i)) b₀
  have hsub :
      {i ∈ F | v ∈ equationScope (restrictMonomials S b (P i))} ⊆
        {i ∈ F | v ∈ equationScope (P i) \ S} := by
    intro i hi
    rw [mem_filter] at hi ⊢
    exact ⟨hi.1, equationScope_restrictMonomials_subset_sdiff S b (P i) hi.2⟩
  exact (card_le_card hsub).trans
    (varIncidence_sdiff_heavyVars_le U F (fun i => equationScope (P i)) b₀ hU v)

/-- **§5.5 (heavy-variable branch count bound)**: for `b₀ > 0`, the number of canonical branches on
`heavyVars U F scope b₀` is at most `2 ^ (totalIncidence F scope / b₀)`. -/
theorem card_branchAssignments_heavyVars_le [Fintype ι] [DecidableEq ι] (U : Finset ι)
    (F : Finset κ) (scope : κ → Finset ι) {b₀ : ℕ} (hb₀ : 0 < b₀)
    (hU : ∀ i ∈ F, scope i ⊆ U) :
    #(branchAssignments (heavyVars U F scope b₀)) ≤ 2 ^ (totalIncidence F scope / b₀) := by
  rw [card_branchAssignments]
  exact Nat.pow_le_pow_right (by omega) (card_heavyVars_le_div U F scope hb₀ hU)

/-- **§5.5 (additive branch decomposition of `commonZeroCount`)**: branching over all canonical
assignments `b ∈ branchAssignments S` to `S` partitions `commonZeroCount I P` into the sum of
common-zero counts on `subproblemAssignments S` of the reduced systems
`fun i => restrictMonomials S b (P i)`. -/
theorem commonZeroCount_eq_sum_branches [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (I : Finset κ) (P : κ → Finset (Finset ι)) :
    commonZeroCount I P =
      ∑ b ∈ branchAssignments S,
        #{y ∈ subproblemAssignments S |
          IsCommonZero I (fun i => restrictMonomials S b (P i)) y} := by
  classical
  have hbij :
      #{x : ι → Bool | IsCommonZero I P x} =
        ∑ p ∈ branchAssignments S ×ˢ subproblemAssignments S,
          if IsCommonZero I P (patchAssignment S p.1 p.2) then 1 else 0 := by
    rw [card_filter]
    refine sum_nbij' (fun x => (fun v => if v ∈ S then x v else false,
        fun v => if v ∈ S then false else x v))
      (fun p => patchAssignment S p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro x _
      rw [mem_product, branchAssignments, subproblemAssignments, mem_filter, mem_filter]
      refine ⟨⟨mem_univ _, fun v hv => ite_eq_right hv⟩, ⟨mem_univ _, fun v hv => ite_eq_left hv⟩⟩
    · intro p _
      exact mem_univ _
    · intro x _
      funext v
      by_cases hv : v ∈ S <;> simp only [patchAssignment, hv, ↓reduceIte]
    · intro p hp
      rw [mem_product, branchAssignments, subproblemAssignments, mem_filter, mem_filter] at hp
      ext v
      · by_cases hv : v ∈ S
        · simp only [patchAssignment, hv, ↓reduceIte]
        · simp only [hv, ↓reduceIte, (hp.1.2 v hv).symm]
      · by_cases hv : v ∈ S
        · simp only [hv, ↓reduceIte, (hp.2.2 v hv).symm]
        · simp only [patchAssignment, hv, ↓reduceIte]
    · intro x _
      have hx :
          patchAssignment S (fun v => if v ∈ S then x v else false)
            (fun v => if v ∈ S then false else x v) = x := by
        funext v
        by_cases hv : v ∈ S <;> simp only [patchAssignment, hv, ↓reduceIte]
      rw [hx]
  rw [commonZeroCount, hbij, sum_product]
  refine sum_congr rfl fun b _ => ?_
  rw [card_filter]
  refine sum_congr rfl fun y _ => ?_
  simp only [isCommonZero_patchAssignment_iff]

/-! ### 6. Cleared-denominator homogenization and `ℓ₁`-norm bounds (§5.4 & Appendix B.2) -/

/-- Cleared-denominator evaluation `a_j * Δ + b_j * A_i` of `parityBaseDigit ℓ j = a_j + b_j X` at
`L_i = A_i / Δ`. -/
def parityBaseDigitCleared {A : Type*} [CommRing A] (ℓ j : ℕ) (Δ A_i : A) : A :=
  ((Polynomial.parityBaseDigit ℓ j).coeff 0 : A) * Δ +
    ((Polynomial.parityBaseDigit ℓ j).coeff 1 : A) * A_i

/-- Homogenization of `parityBaseDigit ℓ j`: `parityBaseDigitCleared ℓ j Δ (Δ * y) =
Δ * evalInt y (parityBaseDigit ℓ j)`. -/
theorem parityBaseDigitCleared_mul {A : Type*} [CommRing A] (ℓ j : ℕ) (Δ y : A) :
    parityBaseDigitCleared ℓ j Δ (Δ * y) =
      Δ * Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j) := by
  conv_rhs =>
    rw [Polynomial.evalInt, Polynomial.parityBaseDigit_eq_C_add_C_mul_X ℓ j, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C]
  rw [parityBaseDigitCleared]
  simp only [eq_intCast]
  ring

/-- Cleared-denominator evaluation `A_i * (A_i - Δ)` of `hPoly = X ^ 2 - X` at `L_i = A_i / Δ`. -/
def hPolyCleared {A : Type*} [CommRing A] (Δ A_i : A) : A :=
  A_i * (A_i - Δ)

/-- Homogenization of `hPoly`: `hPolyCleared Δ (Δ * y) = Δ ^ 2 * evalInt y hPoly`. -/
theorem hPolyCleared_mul {A : Type*} [CommRing A] (Δ y : A) :
    hPolyCleared Δ (Δ * y) = Δ ^ 2 * Polynomial.evalInt y Polynomial.hPoly := by
  rw [hPolyCleared, Polynomial.evalInt_hPoly]
  ring

/-- The cleared-denominator parity factor `Γ B_i(V)` with uniform factor denominator
`Γ = Δ ^ (2 * ℓ - 1)`:
`∑ j ∈ range ℓ, C (Δ ^ (2 * (ℓ - 1 - j)) * parityBaseDigitCleared ℓ j Δ A_i *
  hPolyCleared Δ A_i ^ j) * X ^ j`. -/
def parityFactorCleared {A : Type*} [CommRing A] (ℓ : ℕ) (Δ A_i : A) : Polynomial A :=
  ∑ j ∈ range ℓ,
    Polynomial.C
      (Δ ^ (2 * (ℓ - 1 - j)) * parityBaseDigitCleared ℓ j Δ A_i * hPolyCleared Δ A_i ^ j) *
      Polynomial.X ^ j

/-- The `s`-th coefficient of `parityFactorCleared ℓ Δ A_i`. -/
theorem coeff_parityFactorCleared {A : Type*} [CommRing A] (ℓ : ℕ) (Δ A_i : A) (s : ℕ) :
    (parityFactorCleared ℓ Δ A_i).coeff s =
      if s < ℓ then
        Δ ^ (2 * (ℓ - 1 - s)) * parityBaseDigitCleared ℓ s Δ A_i * hPolyCleared Δ A_i ^ s
      else 0 := by
  rw [parityFactorCleared, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hs : s < ℓ
  · rw [ite_eq_left hs, sum_eq_single s]
    · simp only [↓reduceIte]
    · intro j _ hjs
      exact ite_eq_right (Ne.symm hjs)
    · intro hns
      exact absurd (mem_range.mpr hs) hns
  · rw [ite_eq_right hs]
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    exact ite_eq_right (by omega)

/-- **§5.4 & Appendix B.2 (single-factor denominator clearing, $\Gamma = \Delta^{2\ell-1}$)**: for
`ℓ ≥ 1`, `parityFactorCleared ℓ Δ (Δ * y) = C (Δ ^ (2 * ℓ - 1)) * parityFactor ℓ y`. -/
theorem parityFactorCleared_mul {A : Type*} [CommRing A] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (Δ y : A) :
    parityFactorCleared ℓ Δ (Δ * y) =
      Polynomial.C (Δ ^ (2 * ℓ - 1)) * Polynomial.parityFactor ℓ y := by
  rw [parityFactorCleared, Polynomial.parityFactor, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [parityBaseDigitCleared_mul, hPolyCleared_mul, mul_pow, ← pow_mul,
    ← mul_assoc (Polynomial.C (Δ ^ (2 * ℓ - 1))), ← Polynomial.C_mul]
  congr 2
  have hexp : 2 * (ℓ - 1 - j) + 1 + 2 * j = 2 * ℓ - 1 := by omega
  calc
    Δ ^ (2 * (ℓ - 1 - j)) * (Δ * Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j)) *
        (Δ ^ (2 * j) * Polynomial.evalInt y Polynomial.hPoly ^ j)
      = (Δ ^ (2 * (ℓ - 1 - j)) * Δ ^ 1 * Δ ^ (2 * j)) *
          (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j) *
            Polynomial.evalInt y Polynomial.hPoly ^ j) := by ring
    _ = Δ ^ (2 * ℓ - 1) *
          (Polynomial.evalInt y (Polynomial.parityBaseDigit ℓ j) *
            Polynomial.evalInt y Polynomial.hPoly ^ j) := by
      rw [← pow_add, ← pow_add, hexp]

/-- **§5.4 & Appendix B.2 (product denominator clearing, $\Omega = \Gamma^{\#I}$)**: for `ℓ ≥ 1`,
the product of cleared factors over `i ∈ I` equals `C ((Δ ^ (2 * ℓ - 1)) ^ #I)` times the product
of `parityFactor ℓ (y i)`. -/
theorem prod_parityFactorCleared_mul {A : Type*} [CommRing A] (I : Finset κ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (Δ : A) (y : κ → A) :
    (∏ i ∈ I, parityFactorCleared ℓ Δ (Δ * y i)) =
      Polynomial.C ((Δ ^ (2 * ℓ - 1)) ^ #I) * ∏ i ∈ I, Polynomial.parityFactor ℓ (y i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [prod_empty, card_empty, pow_zero, map_one, one_mul]
  | insert a I ha ih =>
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha, pow_succ',
      parityFactorCleared_mul hℓ Δ (y a), ih, map_mul]
    ring

/-- Scaling a polynomial by `C c` scales `sumCoeffsBelow m` by `c`. -/
theorem sumCoeffsBelow_C_mul {A : Type*} [CommRing A] (c : A) (p : Polynomial A) (m : ℕ) :
    (Polynomial.C c * p).sumCoeffsBelow m = c * p.sumCoeffsBelow m := by
  rw [Polynomial.sumCoeffsBelow, Polynomial.sumCoeffsBelow, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  exact Polynomial.coeff_C_mul p

/-- **§5.4 (truncated cleared-denominator product)**: for `ℓ ≥ 1`, the sum of the first `m`
coefficients of `∏ i ∈ I, parityFactorCleared ℓ Δ (Δ * y i)` equals `(Δ ^ (2 * ℓ - 1)) ^ #I`
times the sum of the first `m` coefficients of `∏ i ∈ I, parityFactor ℓ (y i)`. -/
theorem sumCoeffsBelow_prod_parityFactorCleared_mul {A : Type*} [CommRing A] (I : Finset κ)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (Δ : A) (y : κ → A) (m : ℕ) :
    (∏ i ∈ I, parityFactorCleared ℓ Δ (Δ * y i)).sumCoeffsBelow m =
      (Δ ^ (2 * ℓ - 1)) ^ #I * (∏ i ∈ I, Polynomial.parityFactor ℓ (y i)).sumCoeffsBelow m := by
  rw [prod_parityFactorCleared_mul I hℓ Δ y, sumCoeffsBelow_C_mul]

/-- The cleared-denominator monomial `C (d_den ^ (k - #M)) * ∏ v ∈ M, θ v` in `ℤ[X]` for a monomial
`M` of degree at most `k` when each input has denominator `d_den`. -/
def clearedMonomialPoly (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ) (M : Finset ι) : Polynomial ℤ :=
  Polynomial.C (d_den ^ (k - #M)) * ∏ v ∈ M, θ v

/-- The cleared-denominator monomial sum `A_i = ∑ M ∈ 𝓜, clearedMonomialPoly d_den k θ M` in
`ℤ[X]`. -/
def clearedMonomialSumPoly (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ)
    (𝓜 : Finset (Finset ι)) : Polynomial ℤ :=
  ∑ M ∈ 𝓜, clearedMonomialPoly d_den k θ M

/-- **Appendix B.2 (monomial numerator norm bound)**: if `d_den.natAbs ≤ B₀`, `#M ≤ k`, and every
`θ v` (`v ∈ M`) has `coeffNorm1 (θ v) ≤ B₀`, then
`coeffNorm1 (clearedMonomialPoly d_den k θ M) ≤ B₀ ^ k`. -/
theorem coeffNorm1_clearedMonomialPoly_le {d_den : ℤ} {k B₀ : ℕ} {θ : ι → Polynomial ℤ}
    {M : Finset ι} (hd : d_den.natAbs ≤ B₀) (hM : #M ≤ k)
    (hθ : ∀ v ∈ M, Polynomial.coeffNorm1 (θ v) ≤ B₀) :
    Polynomial.coeffNorm1 (clearedMonomialPoly d_den k θ M) ≤ B₀ ^ k := by
  unfold clearedMonomialPoly
  calc
    Polynomial.coeffNorm1 (Polynomial.C (d_den ^ (k - #M)) * ∏ v ∈ M, θ v)
      ≤ (d_den ^ (k - #M)).natAbs * Polynomial.coeffNorm1 (∏ v ∈ M, θ v) :=
        Polynomial.coeffNorm1_C_mul_le _ _
    _ ≤ B₀ ^ (k - #M) * ∏ v ∈ M, Polynomial.coeffNorm1 (θ v) := by
        rw [Int.natAbs_pow]
        exact Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Polynomial.coeffNorm1_prod_le M θ)
    _ ≤ B₀ ^ (k - #M) * ∏ _v ∈ M, B₀ :=
        Nat.mul_le_mul_left _ (prod_le_prod hθ)
    _ = B₀ ^ k := by
        rw [prod_const, ← pow_add, Nat.sub_add_cancel hM]

/-- **Appendix B.2 (equation numerator norm bound `∥Δ L_i∥₁ ≤ #𝓜 * B₀ ^ k`)**: under the same
hypotheses for all `M ∈ 𝓜`, `coeffNorm1 (clearedMonomialSumPoly d_den k θ 𝓜) ≤ #𝓜 * B₀ ^ k`. -/
theorem coeffNorm1_clearedMonomialSumPoly_le {d_den : ℤ} {k B₀ : ℕ} {θ : ι → Polynomial ℤ}
    {𝓜 : Finset (Finset ι)} (hd : d_den.natAbs ≤ B₀) (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hθ : ∀ M ∈ 𝓜, ∀ v ∈ M, Polynomial.coeffNorm1 (θ v) ≤ B₀) :
    Polynomial.coeffNorm1 (clearedMonomialSumPoly d_den k θ 𝓜) ≤ #𝓜 * B₀ ^ k := by
  unfold clearedMonomialSumPoly
  calc
    Polynomial.coeffNorm1 (∑ M ∈ 𝓜, clearedMonomialPoly d_den k θ M)
      ≤ ∑ M ∈ 𝓜, Polynomial.coeffNorm1 (clearedMonomialPoly d_den k θ M) :=
        Polynomial.coeffNorm1_sum_le 𝓜 _
    _ ≤ ∑ _M ∈ 𝓜, B₀ ^ k :=
        sum_le_sum fun M hM => coeffNorm1_clearedMonomialPoly_le hd (hk M hM) (hθ M hM)
    _ = #𝓜 * B₀ ^ k := by
        rw [sum_const, smul_eq_mul]

/-- **Appendix B.2 (`∥Δ e_j(L_i)∥₁` bound)**: if `coeffNorm1 A_i ≤ B`, then
`coeffNorm1 (parityBaseDigitCleared ℓ j (C Δ) A_i) ≤ coeffNorm1 (parityBaseDigit ℓ j) *
(B + Δ.natAbs)`. -/
theorem coeffNorm1_parityBaseDigitCleared_le (ℓ j : ℕ) (Δ : ℤ) {A_i : Polynomial ℤ} {B : ℕ}
    (hA : Polynomial.coeffNorm1 A_i ≤ B) :
    Polynomial.coeffNorm1 (parityBaseDigitCleared ℓ j (Polynomial.C Δ) A_i) ≤
      Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) * (B + Δ.natAbs) := by
  rw [parityBaseDigitCleared]
  have hcast : ∀ c : ℤ, (c : Polynomial ℤ) = Polynomial.C c := fun c =>
    (eq_intCast Polynomial.C c).symm
  rw [hcast, hcast]
  let a₀ := ((Polynomial.parityBaseDigit ℓ j).coeff 0).natAbs
  let a₁ := ((Polynomial.parityBaseDigit ℓ j).coeff 1).natAbs
  have h0 : Polynomial.coeffNorm1
      (Polynomial.C ((Polynomial.parityBaseDigit ℓ j).coeff 0) * Polynomial.C Δ) ≤
      a₀ * Δ.natAbs := by
    refine (Polynomial.coeffNorm1_C_mul_le _ _).trans ?_
    rw [Polynomial.coeffNorm1_C]
  have h1 : Polynomial.coeffNorm1
      (Polynomial.C ((Polynomial.parityBaseDigit ℓ j).coeff 1) * A_i) ≤ a₁ * B :=
    (Polynomial.coeffNorm1_C_mul_le _ _).trans (Nat.mul_le_mul_left a₁ hA)
  have ha0 : a₀ ≤ Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) :=
    Polynomial.natAbs_coeff_le_coeffNorm1 _ 0
  have ha1 : a₁ ≤ Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) :=
    Polynomial.natAbs_coeff_le_coeffNorm1 _ 1
  calc
    Polynomial.coeffNorm1
        (Polynomial.C ((Polynomial.parityBaseDigit ℓ j).coeff 0) * Polynomial.C Δ +
          Polynomial.C ((Polynomial.parityBaseDigit ℓ j).coeff 1) * A_i)
      ≤ a₀ * Δ.natAbs + a₁ * B := (Polynomial.coeffNorm1_add_le _ _).trans (add_le_add h0 h1)
    _ ≤ Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) * Δ.natAbs +
          Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) * B :=
        add_le_add (Nat.mul_le_mul_right _ ha0) (Nat.mul_le_mul_right _ ha1)
    _ = Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ j) * (B + Δ.natAbs) := by ring

/-- **Appendix B.2 (`∥A_i (A_i - Δ)∥₁` bound)**: if `coeffNorm1 A_i ≤ B`, then
`coeffNorm1 (hPolyCleared (C Δ) A_i) ≤ B * (B + Δ.natAbs)`. -/
theorem coeffNorm1_hPolyCleared_le (Δ : ℤ) {A_i : Polynomial ℤ} {B : ℕ}
    (hA : Polynomial.coeffNorm1 A_i ≤ B) :
    Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i) ≤ B * (B + Δ.natAbs) := by
  unfold hPolyCleared
  calc
    Polynomial.coeffNorm1 (A_i * (A_i - Polynomial.C Δ))
      ≤ Polynomial.coeffNorm1 A_i * Polynomial.coeffNorm1 (A_i - Polynomial.C Δ) :=
        Polynomial.coeffNorm1_mul_le _ _
    _ ≤ B * (Polynomial.coeffNorm1 A_i + Polynomial.coeffNorm1 (Polynomial.C Δ)) :=
        Nat.mul_le_mul hA (Polynomial.coeffNorm1_sub_le A_i (Polynomial.C Δ))
    _ ≤ B * (B + Δ.natAbs) := by
        rw [Polynomial.coeffNorm1_C]
        exact Nat.mul_le_mul_left B (add_le_add hA le_rfl)

/-- **Appendix B.2 (`∥[V ^ s] (Γ B_i)∥₁` bound)**: if `coeffNorm1 A_i ≤ B`, then every `V ^ s`-
coefficient of `parityFactorCleared ℓ (C Δ) A_i` has `coeffNorm1` at most
`coeffNorm1 (parityBaseDigit ℓ s) * (B + Δ.natAbs) ^ (2 * ℓ - 1)`. -/
theorem coeffNorm1_coeff_parityFactorCleared_le (ℓ : ℕ) (Δ : ℤ) {A_i : Polynomial ℤ} {B : ℕ}
    (hA : Polynomial.coeffNorm1 A_i ≤ B) (s : ℕ) :
    Polynomial.coeffNorm1 ((parityFactorCleared ℓ (Polynomial.C Δ) A_i).coeff s) ≤
      Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ s) * (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
  rw [coeff_parityFactorCleared]
  split_ifs with hs
  · have hpowΔ :
        Polynomial.coeffNorm1 ((Polynomial.C Δ) ^ (2 * (ℓ - 1 - s))) ≤
          (B + Δ.natAbs) ^ (2 * (ℓ - 1 - s)) := by
      refine (Polynomial.coeffNorm1_pow_le (Polynomial.C Δ) _).trans ?_
      rw [Polynomial.coeffNorm1_C]
      exact Nat.pow_le_pow_left (Nat.le_add_left Δ.natAbs B) _
    have he :
        Polynomial.coeffNorm1 (parityBaseDigitCleared ℓ s (Polynomial.C Δ) A_i) ≤
          Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ s) * (B + Δ.natAbs) :=
      coeffNorm1_parityBaseDigitCleared_le ℓ s Δ hA
    have hh :
        Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i ^ s) ≤
          (B + Δ.natAbs) ^ (2 * s) := by
      calc
        Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i ^ s)
          ≤ Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i) ^ s :=
            Polynomial.coeffNorm1_pow_le _ s
        _ ≤ (B * (B + Δ.natAbs)) ^ s :=
            Nat.pow_le_pow_left (coeffNorm1_hPolyCleared_le Δ hA) s
        _ ≤ ((B + Δ.natAbs) * (B + Δ.natAbs)) ^ s :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.le_add_right B Δ.natAbs)) s
        _ = (B + Δ.natAbs) ^ (2 * s) := by
            rw [← sq, ← pow_mul]
    have hexp : 2 * (ℓ - 1 - s) + 1 + 2 * s = 2 * ℓ - 1 := by omega
    calc
      Polynomial.coeffNorm1
          ((Polynomial.C Δ) ^ (2 * (ℓ - 1 - s)) *
            parityBaseDigitCleared ℓ s (Polynomial.C Δ) A_i *
            hPolyCleared (Polynomial.C Δ) A_i ^ s)
        ≤ Polynomial.coeffNorm1
            ((Polynomial.C Δ) ^ (2 * (ℓ - 1 - s)) *
              parityBaseDigitCleared ℓ s (Polynomial.C Δ) A_i) *
            Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i ^ s) :=
          Polynomial.coeffNorm1_mul_le _ _
      _ ≤ (Polynomial.coeffNorm1 ((Polynomial.C Δ) ^ (2 * (ℓ - 1 - s))) *
            Polynomial.coeffNorm1 (parityBaseDigitCleared ℓ s (Polynomial.C Δ) A_i)) *
            Polynomial.coeffNorm1 (hPolyCleared (Polynomial.C Δ) A_i ^ s) :=
          Nat.mul_le_mul_right _ (Polynomial.coeffNorm1_mul_le _ _)
      _ ≤ ((B + Δ.natAbs) ^ (2 * (ℓ - 1 - s)) *
            (Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ s) * (B + Δ.natAbs))) *
            (B + Δ.natAbs) ^ (2 * s) :=
          Nat.mul_le_mul (Nat.mul_le_mul hpowΔ he) hh
      _ = Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ s) *
            ((B + Δ.natAbs) ^ (2 * (ℓ - 1 - s)) * (B + Δ.natAbs) ^ 1 *
              (B + Δ.natAbs) ^ (2 * s)) := by ring
      _ = Polynomial.coeffNorm1 (Polynomial.parityBaseDigit ℓ s) *
            (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
          rw [← pow_add, ← pow_add, hexp]
  · simp only [Polynomial.coeffNorm1_zero, zero_le]

/-- **Appendix B.2 (explicit `∥[V ^ s] (Γ B_i)∥₁` bound)**: combining
`coeffNorm1_coeff_parityFactorCleared_le` with `coeffNorm1_parityBaseDigit_le` yields the explicit
exponential bound `2 * ((2 * ℓ) ^ s * 2 ^ (3 * ℓ)) * (B + Δ.natAbs) ^ (2 * ℓ - 1)` for every
`V ^ s`-coefficient of `parityFactorCleared ℓ (C Δ) A_i`. -/
theorem coeffNorm1_coeff_parityFactorCleared_le_explicit (ℓ : ℕ) (Δ : ℤ)
    {A_i : Polynomial ℤ} {B : ℕ} (hA : Polynomial.coeffNorm1 A_i ≤ B) (s : ℕ) :
    Polynomial.coeffNorm1 ((parityFactorCleared ℓ (Polynomial.C Δ) A_i).coeff s) ≤
      2 * ((2 * ℓ) ^ s * 2 ^ (3 * ℓ)) * (B + Δ.natAbs) ^ (2 * ℓ - 1) :=
  (coeffNorm1_coeff_parityFactorCleared_le ℓ Δ hA s).trans
    (Nat.mul_le_mul_right _ (Polynomial.coeffNorm1_parityBaseDigit_le ℓ s))

end Cslib.BitString
