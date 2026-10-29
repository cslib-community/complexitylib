/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseBranching
public import Complexity.Foundations.Data.Polynomial.BivariateCoeffNorm1
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi

/-!
# Rational-to-cleared-denominator specialization and exact division recovery

This module bridges the rational replacement polynomials of Section 5.3–5.4 and the
cleared-denominator integer interpolation pipeline of Section 5.4 and Appendix B.2–B.3 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (pp. 37–39, 48–50):

1. **Cleared-denominator evaluation at $T = 0$, ring homogenization, and `natDegree` bounds
   (§5.3–5.4 & Appendix B.2)**:
   When every monomial $M \in \mathcal{P}_i$ has size $\#M \le k$ and each variable $v \in M$ in
   equation $i \in I$ has an integer numerator polynomial $\theta_{x, i, v}(T) \in \mathbb{Z}[T]$
   over a common denominator $d_{\mathrm{den}} \in \mathbb{Z}$ satisfying
   $\theta_{x, i, v}(0) = d_{\mathrm{den}} \cdot \mathrm{bitVal}_{\mathbb{Z}}(x_v)$ and
   $\deg_T \theta_{x, i, v} \le R_{\mathrm{deg}}$, the cleared-denominator equation polynomial
   `Cslib.BitString.clearedMonomialSumPoly` has `natDegree ≤ k * R_deg`, evaluates at $T = 0$ to
   $d_{\mathrm{den}}^k \cdot \mathrm{monomialSum}_{\mathbb{Z}}(\mathcal{P}_i, x)$, and maps into any
   commutative ring $R$ as `C ((d_den : R) ^ k)` times `Cslib.BitString.univariateMonomialSumPoly`
   whenever `(θ x i v).map (Int.castRingHom R) = C (d_den : R) * q x i v` for all $M \in
   \mathcal{P}_i$ and $v \in M$.
2. **Cube-summed cleared-denominator polynomials $\tilde{H}_s(T) = \Omega [V^s] H(T)$ and exact
   integer division recovery (§5.4 & Appendix B.3, eq. B.1)**:
   Summing the cleared parity-factor products over $x \in \{0, 1\}^\iota$ yields
   `Cslib.BitString.univariateClearedParityProduct`, its $V^s$-coordinates
   `Cslib.BitString.univariateClearedParityCoord` ($\tilde{H}_s(T) \in \mathbb{Z}[T]$), and its
   truncated sum `Cslib.BitString.univariateClearedParityTruncatedSum`. Over any field $K$ with
   $(d_{\mathrm{den}} : K) \neq 0$, $1 \le \ell$, and $\forall i \in I, \forall M \in \mathcal{P}_i,
   \#M \le k$, $\tilde{H}_s(T)$ maps into $K[T]$ as the common product denominator
   $\Omega = (d_{\mathrm{den}}^k)^{(2\ell - 1)\#I}$ (`Cslib.BitString.clearedProductDenom`) times
   the rational coordinate polynomial `[V^s] H(T)` associated to the rational replacement family
   `Cslib.BitString.divDenomReplacement` ($r_{x, i, v}(T) = d_{\mathrm{den}}^{-1}
   \theta_{x, i, v}(T)$). At $T = 0$, when $1 \le \ell$, $\#M \le k$, and
   $\theta_{x, i, v}(0) = d_{\mathrm{den}} \cdot \mathrm{bitVal}_{\mathbb{Z}}(x_v)$,
   $\tilde{H}_s(0)$ is an exact integer multiple of $\Omega$; when $d_{\mathrm{den}} \neq 0$ and
   `Fintype.card ι < ℓ` (and $D_H \neq 0$ for Cramer determinant recovery), dividing each
   $\tilde{H}_s(0)$ (or Cramer's rule determinant numerator $N_{H, s} = D_H \tilde{H}_s(0)$ in
   eq. B.1) by $\Omega$ (or $\Omega D_H$), summing over $0 \le s < \ell$, and reducing modulo
   $2^\ell$ recovers `commonZeroCount I P` on the nose, both on a single problem and summed across
   all heavy-variable branches at shared precision $\ell = n + 1$.

## Main definitions

* `Cslib.BitString.clearedProductDenom`: the product denominator
  $\Omega = ((d_{\mathrm{den}}^k)^{2\ell - 1})^{m_{\mathrm{test}}}$.
* `Cslib.BitString.univariateClearedParityProduct`,
  `Cslib.BitString.univariateClearedParityCoord`,
  `Cslib.BitString.univariateClearedParityTruncatedSum`: the cube-summed cleared-denominator
  bivariate polynomial $\tilde{H}(T, V) \in \mathbb{Z}[T][V]$, its $V^s$-coordinate polynomials
  $\tilde{H}_s(T) \in \mathbb{Z}[T]$, and its truncated sum
  $S_\ell(\tilde{H}(T)) \in \mathbb{Z}[T]$.
* `Cslib.BitString.divDenomReplacement`: the rational replacement family
  $r_{x, i, v}(T) = d_{\mathrm{den}}^{-1} \theta_{x, i, v}(T) \in K[T]$.

## Main results

* `Cslib.BitString.eval_zero_clearedMonomialSumPoly`,
  `Cslib.BitString.map_clearedMonomialSumPoly`,
  `Cslib.BitString.natDegree_clearedMonomialSumPoly_le`: $T = 0$ evaluation, ring homogenization,
  and `natDegree` bound for cleared-denominator equation polynomials.
* `Cslib.BitString.natDegree_univariateClearedParityCoord_le`,
  `Cslib.BitString.natDegree_univariateClearedParityTruncatedSum_le`: equation (5.5a) `natDegree`
  bounds for $\tilde{H}_s(T)$ and $S_\ell(\tilde{H}(T))$.
* `Cslib.BitString.map_univariateClearedParityCoord_divDenomReplacement`,
  `Cslib.BitString.map_univariateClearedParityTruncatedSum_divDenomReplacement`: over any field $K$
  with $(d_{\mathrm{den}} : K) \neq 0$, $1 \le \ell$, and monomial degree at most $k$,
  $\tilde{H}_s(T) = \Omega [V^s] H(T)$ and $S_\ell(\tilde{H}(T)) = \Omega S_\ell(H(T))$.
* `Cslib.BitString.bivariateCoeffNorm1_parityFactorCleared_le`,
  `Cslib.BitString.bivariateCoeffNorm1_prod_parityFactorCleared_le`,
  `Cslib.BitString.coeffNorm1_univariateClearedParityCoord_le`: Appendix B.2 bivariate and
  coordinate `ℓ₁`-norm bounds for cleared parity factors and $\tilde{H}_s(T)$.
* `Cslib.BitString.eval_zero_univariateClearedParityCoord`,
  `Cslib.BitString.ediv_eval_zero_univariateClearedParityCoord`,
  `Cslib.BitString.emod_sum_ediv_eval_zero_univariateClearedParityCoord_eq_commonZeroCount`,
  `Cslib.BitString.emod_ediv_eval_zero_univariateClearedParityTruncatedSum_eq_commonZeroCount`:
  exact integer divisibility by $\Omega$ at $T = 0$ and exact modular recovery of `commonZeroCount`.
* `Cslib.BitString.emod_sum_cramer_ediv_eq_commonZeroCount`: Appendix B.3 (eq. B.1) exact integer
  division recovery from Cramer's rule determinant numerators $N_{H, s} = D_H \tilde{H}_s(0)$ when
  $d_{\mathrm{den}} \neq 0$, $D_H \neq 0$, and `Fintype.card ι < ℓ`.
* `Cslib.BitString.commonZeroCount_eq_sum_branch_emod_ediv_cleared`: §5.5 branch-summed exact
  recovery from cleared-denominator branch polynomials at shared precision $\ell = n + 1$.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 5.3–5.5 and
  Appendix B.2–B.3)
-/

@[expose] public noncomputable section

namespace Cslib.BitString

open Finset

variable {ι κ R : Type*}

/-! ### 1. Ring-homomorphism transport and `natDegree` bounds for cleared parity factors -/

/-- Any ring homomorphism `φ : A →+* B` commutes with `parityBaseDigitCleared`. -/
theorem map_parityBaseDigitCleared {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (ℓ j : ℕ) (Δ A_i : A) :
    φ (parityBaseDigitCleared ℓ j Δ A_i) =
      parityBaseDigitCleared ℓ j (φ Δ) (φ A_i) := by
  simp only [parityBaseDigitCleared, map_add, map_mul, map_intCast]

/-- Any ring homomorphism `φ : A →+* B` commutes with `hPolyCleared`. -/
theorem map_hPolyCleared {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (Δ A_i : A) :
    φ (hPolyCleared Δ A_i) = hPolyCleared (φ Δ) (φ A_i) := by
  simp only [hPolyCleared, map_mul, map_sub]

/-- Mapping `parityFactorCleared ℓ Δ A_i` coefficientwise by `φ : A →+* B` yields
`parityFactorCleared ℓ (φ Δ) (φ A_i)`. -/
theorem map_parityFactorCleared {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (ℓ : ℕ) (Δ A_i : A) :
    (parityFactorCleared ℓ Δ A_i).map φ = parityFactorCleared ℓ (φ Δ) (φ A_i) := by
  ext s
  rw [Polynomial.coeff_map, coeff_parityFactorCleared, coeff_parityFactorCleared]
  split_ifs with hs
  · rw [map_mul, map_mul, map_pow, map_pow, map_parityBaseDigitCleared, map_hPolyCleared]
  · exact map_zero φ

/-- Evaluating the `s`-th coefficient of `∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)` at `t : R`
agrees with the `s`-th coefficient of
`∏ i ∈ I, parityFactorCleared ℓ (Δ.eval t) ((A_i i).eval t)`. -/
theorem eval_coeff_prod_parityFactorCleared [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (Δ : Polynomial R) (A_i : κ → Polynomial R) (s : ℕ) (t : R) :
    ((∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)).coeff s).eval t =
      (∏ i ∈ I, parityFactorCleared ℓ (Δ.eval t) ((A_i i).eval t)).coeff s := by
  let φ : Polynomial R →+* R := Polynomial.evalRingHom t
  change φ ((∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)).coeff s) = _
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  refine congrArg (fun Q : Polynomial R => Q.coeff s) (prod_congr rfl fun i _ => ?_)
  exact map_parityFactorCleared φ ℓ Δ (A_i i)

/-- When `Δ` has `natDegree = 0` and `A_i` has `natDegree ≤ d`, `parityBaseDigitCleared ℓ j Δ A_i`
has `natDegree ≤ d`. -/
theorem natDegree_parityBaseDigitCleared_le [CommRing R] (ℓ j : ℕ) (Δ A_i : Polynomial R)
    {d : ℕ} (hΔ : Δ.natDegree = 0) (hA : A_i.natDegree ≤ d) :
    (parityBaseDigitCleared ℓ j Δ A_i).natDegree ≤ d := by
  rw [parityBaseDigitCleared]
  have hcast : ∀ c : ℤ, (c : Polynomial R) = Polynomial.C (c : R) := fun c => by
    rw [← Polynomial.C_eq_intCast]
  rw [hcast, hcast]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hA

/-- When `Δ` has `natDegree = 0` and `A_i` has `natDegree ≤ d`, `hPolyCleared Δ A_i` has
`natDegree ≤ 2 * d`. -/
theorem natDegree_hPolyCleared_le [CommRing R] (Δ A_i : Polynomial R) {d : ℕ}
    (hΔ : Δ.natDegree = 0) (hA : A_i.natDegree ≤ d) :
    (hPolyCleared Δ A_i).natDegree ≤ 2 * d := by
  rw [hPolyCleared]
  have hsub : (A_i - Δ).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hA (by omega))
  calc
    (A_i * (A_i - Δ)).natDegree
      ≤ A_i.natDegree + (A_i - Δ).natDegree := Polynomial.natDegree_mul_le
    _ ≤ d + d := add_le_add hA hsub
    _ = 2 * d := by ring

/-- When `Δ` has `natDegree = 0` and `A_i` has `natDegree ≤ d`, the `s`-th coefficient of
`parityFactorCleared ℓ Δ A_i` has `natDegree ≤ d * (1 + 2 * s)`. -/
theorem natDegree_coeff_parityFactorCleared_le [CommRing R] (ℓ : ℕ) (Δ A_i : Polynomial R)
    {d : ℕ} (hΔ : Δ.natDegree = 0) (hA : A_i.natDegree ≤ d) (s : ℕ) :
    ((parityFactorCleared ℓ Δ A_i).coeff s).natDegree ≤ d * (1 + 2 * s) := by
  rw [coeff_parityFactorCleared]
  split_ifs with hs
  · have hΔpow : (Δ ^ (2 * (ℓ - 1 - s))).natDegree = 0 := by
      refine Nat.eq_zero_of_le_zero ((Polynomial.natDegree_pow_le).trans ?_)
      simp only [hΔ, mul_zero, le_rfl]
    have he : (parityBaseDigitCleared ℓ s Δ A_i).natDegree ≤ d :=
      natDegree_parityBaseDigitCleared_le ℓ s Δ A_i hΔ hA
    have hh : (hPolyCleared Δ A_i ^ s).natDegree ≤ s * (2 * d) :=
      (Polynomial.natDegree_pow_le).trans
        (Nat.mul_le_mul_left s (natDegree_hPolyCleared_le Δ A_i hΔ hA))
    calc
      (Δ ^ (2 * (ℓ - 1 - s)) * parityBaseDigitCleared ℓ s Δ A_i *
          hPolyCleared Δ A_i ^ s).natDegree
        ≤ (Δ ^ (2 * (ℓ - 1 - s)) * parityBaseDigitCleared ℓ s Δ A_i).natDegree +
            (hPolyCleared Δ A_i ^ s).natDegree := Polynomial.natDegree_mul_le
      _ ≤ ((Δ ^ (2 * (ℓ - 1 - s))).natDegree +
            (parityBaseDigitCleared ℓ s Δ A_i).natDegree) +
            (hPolyCleared Δ A_i ^ s).natDegree :=
          add_le_add Polynomial.natDegree_mul_le le_rfl
      _ ≤ (0 + d) + s * (2 * d) := add_le_add (add_le_add (le_of_eq hΔpow) he) hh
      _ = d * (1 + 2 * s) := by ring
  · simp only [Polynomial.natDegree_zero, zero_le]

/-- **Lemma 5.2 (cleared-denominator univariate `natDegree` bound)**: if `Δ.natDegree = 0` and
every `A_i i` (`i ∈ I`) has `natDegree ≤ d`, then the `s`-th coefficient of
`∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)` has `natDegree ≤ d * (#I + 2 * s)`. -/
theorem natDegree_coeff_prod_parityFactorCleared_le [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (Δ : Polynomial R) (A_i : κ → Polynomial R) {d : ℕ} (hΔ : Δ.natDegree = 0)
    (hA : ∀ i ∈ I, (A_i i).natDegree ≤ d) :
    ∀ s : ℕ,
      ((∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)).coeff s).natDegree ≤ d * (#I + 2 * s) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro s
    rcases s with _ | s
    · simp only [prod_empty, Polynomial.coeff_one_zero, Polynomial.natDegree_one, zero_le]
    · simp only [prod_empty, Polynomial.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
        Polynomial.natDegree_zero, zero_le]
  | insert a I ha ih =>
    intro s
    have ha_le : (A_i a).natDegree ≤ d := hA a (mem_insert_self a I)
    have hI_le : ∀ i ∈ I, (A_i i).natDegree ≤ d := fun i hi => hA i (mem_insert_of_mem hi)
    rw [prod_insert ha, card_insert_of_notMem ha, Polynomial.coeff_mul]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun p hp => ?_⟩
    rw [Finset.mem_antidiagonal] at hp
    dsimp only [Function.comp_apply]
    have h1 := natDegree_coeff_parityFactorCleared_le ℓ Δ (A_i a) hΔ ha_le p.1
    have h2 := ih hI_le p.2
    calc
      ((parityFactorCleared ℓ Δ (A_i a)).coeff p.1 *
          (∏ x ∈ I, parityFactorCleared ℓ Δ (A_i x)).coeff p.2).natDegree
        ≤ ((parityFactorCleared ℓ Δ (A_i a)).coeff p.1).natDegree +
            ((∏ x ∈ I, parityFactorCleared ℓ Δ (A_i x)).coeff p.2).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ d * (1 + 2 * p.1) + d * (#I + 2 * p.2) := add_le_add h1 h2
      _ = d * (#I + 1 + 2 * (p.1 + p.2)) := by ring
      _ = d * (#I + 1 + 2 * s) := by rw [hp]

/-- For `s < ℓ`, the `s`-th coefficient of `∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)` has
`natDegree ≤ d * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_coeff_prod_parityFactorCleared_le_of_lt [CommRing R] (I : Finset κ)
    {ℓ s d : ℕ} (Δ : Polynomial R) (A_i : κ → Polynomial R) (hΔ : Δ.natDegree = 0)
    (hA : ∀ i ∈ I, (A_i i).natDegree ≤ d) (hs : s < ℓ) :
    ((∏ i ∈ I, parityFactorCleared ℓ Δ (A_i i)).coeff s).natDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  refine (natDegree_coeff_prod_parityFactorCleared_le I ℓ Δ A_i hΔ hA s).trans ?_
  exact Nat.mul_le_mul_left d (by omega)

/-! ### 2. Cleared-denominator monomials and equations: $T = 0$ evaluation, ring homogenization,
and `natDegree` bounds (§5.3–5.4 & Appendix B.2) -/

/-- Evaluating `clearedMonomialPoly d_den k θ M` at `t : ℤ` yields
`d_den ^ (k - #M) * ∏ v ∈ M, (θ v).eval t`. -/
theorem eval_clearedMonomialPoly (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ) (M : Finset ι)
    (t : ℤ) :
    (clearedMonomialPoly d_den k θ M).eval t =
      d_den ^ (k - #M) * ∏ v ∈ M, (θ v).eval t := by
  rw [clearedMonomialPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]

/-- At `T = 0`, if `#M ≤ k` and every `θ v` (`v ∈ M`) evaluates to `d_den * bitVal ℤ (x v)`, then
`clearedMonomialPoly d_den k θ M` evaluates to `d_den ^ k * monomial ℤ M x`. -/
theorem eval_zero_clearedMonomialPoly (d_den : ℤ) {k : ℕ} (θ : ι → Polynomial ℤ)
    {M : Finset ι} (x : ι → Bool) (hM : #M ≤ k)
    (hθ : ∀ v ∈ M, (θ v).eval 0 = d_den * bitVal ℤ (x v)) :
    (clearedMonomialPoly d_den k θ M).eval 0 = d_den ^ k * monomial ℤ M x := by
  rw [eval_clearedMonomialPoly, monomial]
  have hprod : (∏ v ∈ M, (θ v).eval 0) = d_den ^ #M * ∏ v ∈ M, bitVal ℤ (x v) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun v hv => hθ v hv
  rw [hprod, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]

/-- **§5.3–5.4 ($T = 0$ evaluation of cleared equation polynomial)**: at `T = 0`, if every
`M ∈ 𝓜` has `#M ≤ k` and every `θ v` (`v ∈ M`) evaluates to `d_den * bitVal ℤ (x v)`, then
`clearedMonomialSumPoly d_den k θ 𝓜` evaluates to `d_den ^ k * monomialSum ℤ 𝓜 x`. -/
theorem eval_zero_clearedMonomialSumPoly (d_den : ℤ) {k : ℕ} (θ : ι → Polynomial ℤ)
    {𝓜 : Finset (Finset ι)} (x : ι → Bool) (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hθ : ∀ M ∈ 𝓜, ∀ v ∈ M, (θ v).eval 0 = d_den * bitVal ℤ (x v)) :
    (clearedMonomialSumPoly d_den k θ 𝓜).eval 0 = d_den ^ k * monomialSum ℤ 𝓜 x := by
  rw [clearedMonomialSumPoly, Polynomial.eval_finsetSum, monomialSum, mul_sum]
  exact sum_congr rfl fun M hM => eval_zero_clearedMonomialPoly d_den θ x (hk M hM) (hθ M hM)

/-- Mapping `clearedMonomialPoly d_den k θ M` into `R[X]` when `#M ≤ k` and
`(θ v).map (Int.castRingHom R) = C (d_den : R) * q v` yields
`C ((d_den : R) ^ k) * univariateMonomialPoly R q M`. -/
theorem map_clearedMonomialPoly [CommRing R] (d_den : ℤ) {k : ℕ} (θ : ι → Polynomial ℤ)
    (q : ι → Polynomial R) {M : Finset ι} (hM : #M ≤ k)
    (hq : ∀ v ∈ M, (θ v).map (Int.castRingHom R) = Polynomial.C (d_den : R) * q v) :
    (clearedMonomialPoly d_den k θ M).map (Int.castRingHom R) =
      Polynomial.C ((d_den : R) ^ k) * univariateMonomialPoly R q M := by
  rw [clearedMonomialPoly, Polynomial.map_mul, Polynomial.map_C, eq_intCast, Int.cast_pow,
    Polynomial.map_prod]
  have hprod :
      (∏ v ∈ M, (θ v).map (Int.castRingHom R)) =
        Polynomial.C ((d_den : R) ^ #M) * univariateMonomialPoly R q M := by
    rw [univariateMonomialPoly, Polynomial.C_pow, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun v hv => hq v hv
  rw [hprod, ← mul_assoc, ← Polynomial.C_mul, ← pow_add, Nat.sub_add_cancel hM]

/-- **§5.4 (ring homogenization of cleared equation polynomial)**: mapping
`clearedMonomialSumPoly d_den k θ 𝓜` into `R[X]` when `∀ M ∈ 𝓜, #M ≤ k` and
`(θ v).map (Int.castRingHom R) = C (d_den : R) * q v` yields
`C ((d_den : R) ^ k) * univariateMonomialSumPoly R q 𝓜`. -/
theorem map_clearedMonomialSumPoly [CommRing R] (d_den : ℤ) {k : ℕ} (θ : ι → Polynomial ℤ)
    (q : ι → Polynomial R) {𝓜 : Finset (Finset ι)} (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hq : ∀ M ∈ 𝓜, ∀ v ∈ M, (θ v).map (Int.castRingHom R) = Polynomial.C (d_den : R) * q v) :
    (clearedMonomialSumPoly d_den k θ 𝓜).map (Int.castRingHom R) =
      Polynomial.C ((d_den : R) ^ k) * univariateMonomialSumPoly R q 𝓜 := by
  rw [clearedMonomialSumPoly, Polynomial.map_sum, univariateMonomialSumPoly, mul_sum]
  exact sum_congr rfl fun M hM => map_clearedMonomialPoly d_den θ q (hk M hM) (hq M hM)

/-- If every `θ v` (`v ∈ M`) has `natDegree ≤ R_deg`, then `clearedMonomialPoly d_den k θ M` has
`natDegree ≤ #M * R_deg`. -/
theorem natDegree_clearedMonomialPoly_le (d_den : ℤ) (k : ℕ) (θ : ι → Polynomial ℤ)
    {M : Finset ι} {R_deg : ℕ} (hθ : ∀ v ∈ M, (θ v).natDegree ≤ R_deg) :
    (clearedMonomialPoly d_den k θ M).natDegree ≤ #M * R_deg := by
  rw [clearedMonomialPoly]
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (natDegree_univariateMonomialPoly_le le_rfl hθ)

/-- If every `M ∈ 𝓜` has `#M ≤ k` and every `θ v` (`v ∈ M`) has `natDegree ≤ R_deg`, then
`clearedMonomialSumPoly d_den k θ 𝓜` has `natDegree ≤ k * R_deg`. -/
theorem natDegree_clearedMonomialSumPoly_le (d_den : ℤ) {k R_deg : ℕ} (θ : ι → Polynomial ℤ)
    {𝓜 : Finset (Finset ι)} (hk : ∀ M ∈ 𝓜, #M ≤ k)
    (hθ : ∀ M ∈ 𝓜, ∀ v ∈ M, (θ v).natDegree ≤ R_deg) :
    (clearedMonomialSumPoly d_den k θ 𝓜).natDegree ≤ k * R_deg := by
  rw [clearedMonomialSumPoly]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun M hM => ?_⟩
  exact (natDegree_clearedMonomialPoly_le d_den k θ (hθ M hM)).trans
    (Nat.mul_le_mul_right R_deg (hk M hM))

/-! ### 3. Cube-summed cleared-denominator polynomials $\tilde{H}_s(T) = \Omega [V^s] H(T)$ and
exact integer division recovery (§5.4 & Appendix B.2–B.3) -/

/-- The common product denominator $\Omega = \Gamma^{m_{\mathrm{test}}} =
((d_{\mathrm{den}}^k)^{2\ell - 1})^{m_{\mathrm{test}}}$ of the product of $m_{\mathrm{test}}$
cleared parity factors (§5.4 and Appendix B.2). -/
def clearedProductDenom (d_den : ℤ) (k ℓ m_test : ℕ) : ℤ :=
  ((d_den ^ k) ^ (2 * ℓ - 1)) ^ m_test

/-- When `d_den ≠ 0`, `clearedProductDenom d_den k ℓ m_test ≠ 0`. -/
theorem clearedProductDenom_ne_zero {d_den : ℤ} (hd : d_den ≠ 0) (k ℓ m_test : ℕ) :
    clearedProductDenom d_den k ℓ m_test ≠ 0 :=
  pow_ne_zero m_test (pow_ne_zero (2 * ℓ - 1) (pow_ne_zero k hd))

/-- The cube-summed cleared-denominator bivariate polynomial
$\tilde{H}(T, V) = \sum_{x \in \{0, 1\}^\iota} \prod_{i \in I} (\Gamma B_i)(T, V)$ in
`Polynomial (Polynomial ℤ)` (`ℤ[T][V]`). -/
def univariateClearedParityProduct [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) : Polynomial (Polynomial ℤ) :=
  ∑ x : ι → Bool,
    ∏ i ∈ I,
      parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
        (clearedMonomialSumPoly d_den k (θ x i) (P i))

/-- The $V^s$-coordinate polynomial $\tilde{H}_s(T) = [V^s] \tilde{H}(T) \in \mathbb{Z}[T]$. -/
def univariateClearedParityCoord [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (s : ℕ) : Polynomial ℤ :=
  (univariateClearedParityProduct I P d_den k ℓ θ).coeff s

/-- Explicit cube-sum expansion of `univariateClearedParityCoord`. -/
theorem univariateClearedParityCoord_eq_sum [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (s : ℕ) :
    univariateClearedParityCoord I P d_den k ℓ θ s =
      ∑ x : ι → Bool,
        (∏ i ∈ I,
          parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
            (clearedMonomialSumPoly d_den k (θ x i) (P i))).coeff s := by
  rw [univariateClearedParityCoord, univariateClearedParityProduct, Polynomial.finsetSum_coeff]

/-- The truncated coefficient sum $S_\ell(\tilde{H}(T)) = \sum_{s < \ell} \tilde{H}_s(T) \in
\mathbb{Z}[T]$. -/
def univariateClearedParityTruncatedSum [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) : Polynomial ℤ :=
  (univariateClearedParityProduct I P d_den k ℓ θ).sumCoeffsBelow ℓ

/-- `univariateClearedParityTruncatedSum` is the sum of `univariateClearedParityCoord` over
`s ∈ range ℓ`. -/
theorem univariateClearedParityTruncatedSum_eq_sum_coord [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) :
    univariateClearedParityTruncatedSum I P d_den k ℓ θ =
      ∑ s ∈ range ℓ, univariateClearedParityCoord I P d_den k ℓ θ s :=
  rfl

/-- **Equation (5.5a) (cleared-denominator coordinate `natDegree` bound)**: for `s < ℓ`, if every
equation `P i` (`i ∈ I`) has degree at most `k` and every numerator `θ x i v` has
`natDegree ≤ R_deg`, then `univariateClearedParityCoord I P d_den k ℓ θ s` has
`natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateClearedParityCoord_le [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ) {R_deg s : ℕ}
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg)
    (hs : s < ℓ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).natDegree ≤
      (k * R_deg) * (#I + 2 * (ℓ - 1)) := by
  rw [univariateClearedParityCoord_eq_sum]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun x _ => ?_⟩
  exact natDegree_coeff_prod_parityFactorCleared_le_of_lt I (Polynomial.C (d_den ^ k))
    (fun i => clearedMonomialSumPoly d_den k (θ x i) (P i))
    (Polynomial.natDegree_C (d_den ^ k))
    (fun i hi => natDegree_clearedMonomialSumPoly_le d_den (θ x i) (hk i hi) (hθ x i hi)) hs

/-- **Equation (5.5a) (cleared-denominator truncated-sum `natDegree` bound)**: under the same
hypotheses, `univariateClearedParityTruncatedSum I P d_den k ℓ θ` has
`natDegree ≤ (k * R_deg) * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_univariateClearedParityTruncatedSum_le [Fintype ι] [DecidableEq ι]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ) {R_deg : ℕ}
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M, (θ x i v).natDegree ≤ R_deg) :
    (univariateClearedParityTruncatedSum I P d_den k ℓ θ).natDegree ≤
      (k * R_deg) * (#I + 2 * (ℓ - 1)) := by
  rw [univariateClearedParityTruncatedSum_eq_sum_coord]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun s hs => ?_⟩
  rw [mem_range] at hs
  exact natDegree_univariateClearedParityCoord_le I P d_den k ℓ θ hk hθ hs

/-- **§5.4 & Appendix B.2–B.3 (homogenization of $\tilde{H}_s(T) = \Omega [V^s] H(T)$)**:
for `1 ≤ ℓ`, if `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k` and every numerator `θ x i v` maps into `R[X]` as
`C (d_den : R) * q x i v`, then mapping `univariateClearedParityCoord I P d_den k ℓ θ s` into
`R[X]` gives `C (clearedProductDenom d_den k ℓ #I : R) * univariateParityCoord I P ℓ q s`. -/
theorem map_univariateClearedParityCoord [Fintype ι] [DecidableEq ι] [CommRing R] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (q : (ι → Bool) → κ → ι → Polynomial R)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hq : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).map (Int.castRingHom R) = Polynomial.C (d_den : R) * q x i v) (s : ℕ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).map (Int.castRingHom R) =
      Polynomial.C (clearedProductDenom d_den k ℓ #I : R) * univariateParityCoord I P ℓ q s := by
  let φ : Polynomial ℤ →+* Polynomial R := Polynomial.mapRingHom (Int.castRingHom R)
  change φ (univariateClearedParityCoord I P d_den k ℓ θ s) = _
  rw [univariateClearedParityCoord_eq_sum, univariateParityCoord_eq_sum, map_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  have hprod :
      (∏ i ∈ I,
        (parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
          (clearedMonomialSumPoly d_den k (θ x i) (P i))).map φ) =
        ∏ i ∈ I,
          parityFactorCleared ℓ (Polynomial.C ((d_den : R) ^ k))
            (Polynomial.C ((d_den : R) ^ k) * univariateMonomialSumPoly R (q x i) (P i)) := by
    refine prod_congr rfl fun i hi => ?_
    rw [map_parityFactorCleared]
    congr 1
    · change (Polynomial.C (d_den ^ k)).map (Int.castRingHom R) = _
      rw [Polynomial.map_C, eq_intCast, Int.cast_pow]
    · exact map_clearedMonomialSumPoly d_den (θ x i) (q x i) (hk i hi) (hq x i hi)
  rw [hprod, prod_parityFactorCleared_mul I hℓ (Polynomial.C ((d_den : R) ^ k))
    (fun i => univariateMonomialSumPoly R (q x i) (P i)), Polynomial.coeff_C_mul]
  congr 1
  simp only [clearedProductDenom, Int.cast_pow, Polynomial.C_pow]

/-- **§5.4 & Appendix B.2–B.3 (homogenization of $S_\ell(\tilde{H}(T)) = \Omega S_\ell(H(T))$
over `R[X]`)**: under the same hypotheses, mapping
`univariateClearedParityTruncatedSum I P d_den k ℓ θ` into `R[X]` gives
`C (clearedProductDenom d_den k ℓ #I : R) * univariateParityTruncatedSum I P ℓ q`. -/
theorem map_univariateClearedParityTruncatedSum [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Finset κ) (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (q : (ι → Bool) → κ → ι → Polynomial R)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hq : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).map (Int.castRingHom R) = Polynomial.C (d_den : R) * q x i v) :
    (univariateClearedParityTruncatedSum I P d_den k ℓ θ).map (Int.castRingHom R) =
      Polynomial.C (clearedProductDenom d_den k ℓ #I : R) *
        univariateParityTruncatedSum I P ℓ q := by
  rw [univariateClearedParityTruncatedSum_eq_sum_coord, Polynomial.map_sum,
    univariateParityTruncatedSum_eq_sum_coord, mul_sum]
  exact sum_congr rfl fun s _ => map_univariateClearedParityCoord I P d_den hℓ θ q hk hq s

/-- The rational replacement family $r_{x, i, v}(T) = d_{\mathrm{den}}^{-1} \theta_{x, i, v}(T) \in
K[T]$ over a field $K$ associated to an integer numerator family $\theta$ with common denominator
$d_{\mathrm{den}}$. -/
def divDenomReplacement (K : Type*) [Field K] (d_den : ℤ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (x : ι → Bool) (i : κ) (v : ι) : Polynomial K :=
  Polynomial.C ((d_den : K)⁻¹) * (θ x i v).map (Int.castRingHom K)

/-- Multiplying `divDenomReplacement K d_den θ x i v` by `C (d_den : K)` when `(d_den : K) ≠ 0`
recovers `(θ x i v).map (Int.castRingHom K)`. -/
theorem C_mul_divDenomReplacement {K : Type*} [Field K] {d_den : ℤ} (hd : (d_den : K) ≠ 0)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (x : ι → Bool) (i : κ) (v : ι) :
    (θ x i v).map (Int.castRingHom K) =
      Polynomial.C (d_den : K) * divDenomReplacement K d_den θ x i v := by
  rw [divDenomReplacement, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hd, Polynomial.C_1,
    one_mul]

/-- **§5.4 & Appendix B.3 ($\tilde{H}_s(T) = \Omega [V^s] H(T)$ over a field $K$)**: when
`(d_den : K) ≠ 0`, `1 ≤ ℓ`, and `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k`, mapping
`univariateClearedParityCoord I P d_den k ℓ θ s` into `K[T]` equals
`C (clearedProductDenom d_den k ℓ #I : K)` times `univariateParityCoord` for
`divDenomReplacement K d_den θ`. -/
theorem map_univariateClearedParityCoord_divDenomReplacement [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : (d_den : K) ≠ 0) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) (s : ℕ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).map (Int.castRingHom K) =
      Polynomial.C (clearedProductDenom d_den k ℓ #I : K) *
        univariateParityCoord I P ℓ (divDenomReplacement K d_den θ) s :=
  map_univariateClearedParityCoord I P d_den hℓ θ (divDenomReplacement K d_den θ) hk
    (fun x i _ _ _ v _ => C_mul_divDenomReplacement hd θ x i v) s

/-- **§5.4 & Appendix B.3 ($S_\ell(\tilde{H}(T)) = \Omega S_\ell(H(T))$ over a field $K$)**: under
the same hypotheses, mapping `univariateClearedParityTruncatedSum I P d_den k ℓ θ` into `K[T]`
equals `C (clearedProductDenom d_den k ℓ #I : K)` times `univariateParityTruncatedSum` for
`divDenomReplacement K d_den θ`. -/
theorem map_univariateClearedParityTruncatedSum_divDenomReplacement [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : (d_den : K) ≠ 0) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k) :
    (univariateClearedParityTruncatedSum I P d_den k ℓ θ).map (Int.castRingHom K) =
      Polynomial.C (clearedProductDenom d_den k ℓ #I : K) *
        univariateParityTruncatedSum I P ℓ (divDenomReplacement K d_den θ) :=
  map_univariateClearedParityTruncatedSum I P d_den hℓ θ (divDenomReplacement K d_den θ) hk
    (fun x i _ _ _ v _ => C_mul_divDenomReplacement hd θ x i v)

/-- **§5.4 & Appendix B.3 (exact integer factorization of $\tilde{H}_s(0)$ at $T = 0$)**:
for `1 ≤ ℓ`, if `∀ i ∈ I, ∀ M ∈ P i, #M ≤ k` and every `θ x i v` evaluates at `0` to
`d_den * bitVal ℤ (x v)`, then `(univariateClearedParityCoord I P d_den k ℓ θ s).eval 0` equals
`clearedProductDenom d_den k ℓ #I` times the integer value of `[V^s] H(0)`. -/
theorem eval_zero_univariateClearedParityCoord [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) (s : ℕ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 =
      clearedProductDenom d_den k ℓ #I *
        ∑ x : ι → Bool,
          (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s := by
  rw [univariateClearedParityCoord_eq_sum, Polynomial.eval_finsetSum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_coeff_prod_parityFactorCleared, Polynomial.eval_C]
  have hprod :
      (∏ i ∈ I,
        parityFactorCleared ℓ (d_den ^ k)
          ((clearedMonomialSumPoly d_den k (θ x i) (P i)).eval 0)) =
        ∏ i ∈ I,
          parityFactorCleared ℓ (d_den ^ k) (d_den ^ k * monomialSum ℤ (P i) x) := by
    refine prod_congr rfl fun i hi => ?_
    rw [eval_zero_clearedMonomialSumPoly d_den (θ x i) x (hk i hi) (hθ x i hi)]
  rw [hprod, prod_parityFactorCleared_mul I hℓ (d_den ^ k) (fun i => monomialSum ℤ (P i) x),
    Polynomial.coeff_C_mul, clearedProductDenom]

/-- **§5.4 & Appendix B.3 (exact integer factorization of $S_\ell(\tilde{H})(0)$ at $T = 0$)**:
under the same hypotheses, `(univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0` equals
`clearedProductDenom d_den k ℓ #I` times the integer value of $S_\ell(H(0))$. -/
theorem eval_zero_univariateClearedParityTruncatedSum [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) :
    (univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0 =
      clearedProductDenom d_den k ℓ #I *
        ∑ x : ι → Bool,
          (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).sumCoeffsBelow ℓ := by
  rw [univariateClearedParityTruncatedSum_eq_sum_coord, Polynomial.eval_finsetSum]
  have hsum :
      (∑ s ∈ range ℓ, (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0) =
        ∑ s ∈ range ℓ,
          clearedProductDenom d_den k ℓ #I *
            ∑ x : ι → Bool,
              (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s :=
    sum_congr rfl fun s _ => eval_zero_univariateClearedParityCoord I P d_den hℓ θ hk hθ s
  rw [hsum, ← mul_sum, sum_comm]
  rfl

/-- **Appendix B.3 (exact divisibility of $\tilde{H}_s(0)$ by $\Omega$)**: under the hypotheses of
`eval_zero_univariateClearedParityCoord`, `clearedProductDenom d_den k ℓ #I` divides
`(univariateClearedParityCoord I P d_den k ℓ θ s).eval 0` in `ℤ`. -/
theorem dvd_eval_zero_univariateClearedParityCoord [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) (s : ℕ) :
    clearedProductDenom d_den k ℓ #I ∣
      (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 :=
  ⟨_, eval_zero_univariateClearedParityCoord I P d_den hℓ θ hk hθ s⟩

/-- **Appendix B.3 (exact integer quotient $\tilde{H}_s(0) / \Omega = H_s(0)$)**: when in addition
`d_den ≠ 0`, exact integer division of `(univariateClearedParityCoord I P d_den k ℓ θ s).eval 0`
by `clearedProductDenom d_den k ℓ #I` recovers the integer coefficient sum
`∑ x : ι → Bool, (∏ i ∈ I, parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s`. -/
theorem ediv_eval_zero_univariateClearedParityCoord [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) {d_den : ℤ} (hd : d_den ≠ 0) {k ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) (s : ℕ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 /
        clearedProductDenom d_den k ℓ #I =
      ∑ x : ι → Bool,
        (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s := by
  rw [eval_zero_univariateClearedParityCoord I P d_den hℓ θ hk hθ s,
    Int.mul_ediv_cancel_left _ (clearedProductDenom_ne_zero hd k ℓ #I)]

/-- **§5.4 & Appendix B.3 (exact modular recovery of `commonZeroCount` from coordinate quotients
$\tilde{H}_s(0) / \Omega$)**: when `Fintype.card ι < ℓ` and `d_den ≠ 0`, summing the exact integer
quotients `(univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 / Ω` over `s ∈ range ℓ` and
reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_sum_ediv_eval_zero_univariateClearedParityCoord_eq_commonZeroCount
    [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : d_den ≠ 0) {k ℓ : ℕ} (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) :
    (∑ s ∈ range ℓ,
      (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 /
        clearedProductDenom d_den k ℓ #I) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hsum :
      (∑ s ∈ range ℓ,
        (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 /
          clearedProductDenom d_den k ℓ #I) =
        ∑ x : ι → Bool,
          (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).sumCoeffsBelow ℓ := by
    calc
      (∑ s ∈ range ℓ,
        (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 /
          clearedProductDenom d_den k ℓ #I)
        = ∑ s ∈ range ℓ,
            ∑ x : ι → Bool,
              (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s :=
          sum_congr rfl fun s _ =>
            ediv_eval_zero_univariateClearedParityCoord I P hd hℓ1 θ hk hθ s
      _ = ∑ x : ι → Bool,
            (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).sumCoeffsBelow ℓ := by
          rw [sum_comm]
          rfl
  rw [hsum]
  exact emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount I P hℓ

/-- **§5.4 & Appendix B.3 (exact modular recovery of `commonZeroCount` from
$S_\ell(\tilde{H})(0) / \Omega$)**: under the same hypotheses, dividing
`(univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0` by `clearedProductDenom d_den k ℓ #I`
and reducing modulo `2 ^ ℓ` recovers `commonZeroCount I P`. -/
theorem emod_ediv_eval_zero_univariateClearedParityTruncatedSum_eq_commonZeroCount
    [Fintype ι] [DecidableEq ι] (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ}
    (hd : d_den ≠ 0) {k ℓ : ℕ} (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v)) :
    ((univariateClearedParityTruncatedSum I P d_den k ℓ θ).eval 0 /
      clearedProductDenom d_den k ℓ #I) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  have hℓ1 : 1 ≤ ℓ := by omega
  rw [eval_zero_univariateClearedParityTruncatedSum I P d_den hℓ1 θ hk hθ,
    Int.mul_ediv_cancel_left _ (clearedProductDenom_ne_zero hd k ℓ #I)]
  exact emod_sum_sumCoeffsBelow_prod_parityFactor_eq_commonZeroCount I P hℓ

/-- **Appendix B.3 (eq. B.1, Cramer's rule determinant exact division recovery)**: if
`N_H : ℕ → ℤ` and `D_H : ℤ` (`D_H ≠ 0`) satisfy
`N_H s = D_H * (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0` for all `s ∈ range ℓ`
(as in $N_H = \det V^{(0)} = (\det V) \cdot \Omega H_s(0)$), then for `d_den ≠ 0` and
`Fintype.card ι < ℓ`, summing the exact integer quotients
`N_H s / (clearedProductDenom d_den k ℓ #I * D_H)` over `s ∈ range ℓ` and reducing modulo `2 ^ ℓ`
recovers `commonZeroCount I P`. -/
theorem emod_sum_cramer_ediv_eq_commonZeroCount [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) {d_den D_H : ℤ} (hd : d_den ≠ 0) (hDH : D_H ≠ 0)
    {k ℓ : ℕ} (hℓ : Fintype.card ι < ℓ)
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ) (N_H : ℕ → ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ x : ι → Bool, ∀ i ∈ I, ∀ M ∈ P i, ∀ v ∈ M,
      (θ x i v).eval 0 = d_den * bitVal ℤ (x v))
    (hcramer : ∀ s ∈ range ℓ,
      N_H s = D_H * (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0) :
    (∑ s ∈ range ℓ, N_H s / (clearedProductDenom d_den k ℓ #I * D_H)) % ((2 : ℤ) ^ ℓ) =
      commonZeroCount I P := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hcongr :
      (∑ s ∈ range ℓ, N_H s / (clearedProductDenom d_den k ℓ #I * D_H)) =
        ∑ s ∈ range ℓ,
          (univariateClearedParityCoord I P d_den k ℓ θ s).eval 0 /
            clearedProductDenom d_den k ℓ #I := by
    refine sum_congr rfl fun s hs => ?_
    rw [hcramer s hs, eval_zero_univariateClearedParityCoord I P d_den hℓ1 θ hk hθ s]
    have hmul :
        D_H * (clearedProductDenom d_den k ℓ #I *
            ∑ x : ι → Bool,
              (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s) =
          (clearedProductDenom d_den k ℓ #I * D_H) *
            ∑ x : ι → Bool,
              (∏ i ∈ I, Polynomial.parityFactor ℓ (monomialSum ℤ (P i) x)).coeff s := by
      ring
    rw [hmul,
      Int.mul_ediv_cancel_left _ (mul_ne_zero (clearedProductDenom_ne_zero hd k ℓ #I) hDH),
      Int.mul_ediv_cancel_left _ (clearedProductDenom_ne_zero hd k ℓ #I)]
  rw [hcongr]
  exact emod_sum_ediv_eval_zero_univariateClearedParityCoord_eq_commonZeroCount I P hd hℓ θ hk hθ

/-- **§5.5 & Appendix B.3 (branch-summed exact integer division recovery at shared precision
$\ell = n + 1$)**: summing the branch modular residues of
`((univariateClearedParityTruncatedSum ...).eval 0 / clearedProductDenom ...)` at precision
`branchPrecision (Fintype.card ι)` across all `b ∈ branchAssignments S` recovers
`commonZeroCount I P`. -/
theorem commonZeroCount_eq_sum_branch_emod_ediv_cleared {ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (S : Finset ι) (e : ↥(univ \ S) ≃ ι')
    (I : Finset κ) (P : κ → Finset (Finset ι)) {d_den : ℤ} (hd : d_den ≠ 0) {k : ℕ}
    (θ : (ι → Bool) → (ι' → Bool) → κ → ι' → Polynomial ℤ)
    (hk : ∀ i ∈ I, ∀ M ∈ P i, #M ≤ k)
    (hθ : ∀ b ∈ branchAssignments S, ∀ x : ι' → Bool, ∀ i ∈ I,
      ∀ M ∈ relabelRestrictedMonomials S e b (P i), ∀ v ∈ M,
      (θ b x i v).eval 0 = d_den * bitVal ℤ (x v)) :
    (commonZeroCount I P : ℤ) =
      ∑ b ∈ branchAssignments S,
        ((univariateClearedParityTruncatedSum I
          (fun i => relabelRestrictedMonomials S e b (P i))
          d_den k (branchPrecision (Fintype.card ι)) (θ b)).eval 0 /
            clearedProductDenom d_den k (branchPrecision (Fintype.card ι)) #I) %
              ((2 : ℤ) ^ branchPrecision (Fintype.card ι)) := by
  rw [commonZeroCount_eq_sum_relabelRestrictedMonomials S e I P, Nat.cast_sum]
  refine sum_congr rfl fun b hb => ?_
  have hlt : Fintype.card ι' < branchPrecision (Fintype.card ι) := by
    have hle : Fintype.card ι' ≤ Fintype.card ι := by
      rw [← Fintype.card_congr e, Fintype.card_coe]
      exact card_le_univ _
    rw [branchPrecision]
    omega
  have hk_branch : ∀ i ∈ I, ∀ M ∈ relabelRestrictedMonomials S e b (P i), #M ≤ k :=
    fun i hi M hM => card_mem_relabelRestrictedMonomials_le (hk i hi) M hM
  exact (emod_ediv_eval_zero_univariateClearedParityTruncatedSum_eq_commonZeroCount I
    (fun i => relabelRestrictedMonomials S e b (P i)) hd hlt (θ b) hk_branch (hθ b hb)).symm

/-! ### 4. Bivariate `ℓ₁`-norm bounds for cleared parity products and coordinates
(Appendix B.2) -/

/-- **Appendix B.2 (`∥Γ B_i∥₁ ≤ B₁ = ℓ E_ℓ (B + |Δ|)^{2ℓ - 1}`)**: if `A_i.coeffNorm1 ≤ B` and
`∀ s < ℓ, (parityBaseDigit ℓ s).coeffNorm1 ≤ E_ℓ`, then
`(parityFactorCleared ℓ (C Δ) A_i).bivariateCoeffNorm1 ≤ ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)`. -/
theorem bivariateCoeffNorm1_parityFactorCleared_le (ℓ : ℕ) (Δ : ℤ)
    {A_i : Polynomial ℤ} {B E_ℓ : ℕ} (hA : A_i.coeffNorm1 ≤ B)
    (hE : ∀ s < ℓ, (Polynomial.parityBaseDigit ℓ s).coeffNorm1 ≤ E_ℓ) :
    (parityFactorCleared ℓ (Polynomial.C Δ) A_i).bivariateCoeffNorm1 ≤
      ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
  have hsub : (parityFactorCleared ℓ (Polynomial.C Δ) A_i).support ⊆ range ℓ := by
    intro s hs
    rw [Polynomial.mem_support_iff, coeff_parityFactorCleared] at hs
    by_contra hns
    rw [mem_range] at hns
    exact hs (ite_eq_right hns)
  rw [Polynomial.bivariateCoeffNorm1_eq_sum_of_support_subset hsub]
  calc
    (∑ s ∈ range ℓ, ((parityFactorCleared ℓ (Polynomial.C Δ) A_i).coeff s).coeffNorm1)
      ≤ ∑ _s ∈ range ℓ, E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
        refine sum_le_sum fun s hs => ?_
        rw [mem_range] at hs
        exact (coeffNorm1_coeff_parityFactorCleared_le ℓ Δ hA s).trans
          (Nat.mul_le_mul_right _ (hE s hs))
    _ = ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
        rw [sum_const, card_range, smul_eq_mul, ← mul_assoc]

/-- **Appendix B.2 (`∥Ω ∏_{i ∈ I} B_i∥₁ ≤ B₁ ^ #I`)**: under the same bounds for every `i ∈ I`,
the product of cleared parity factors has `bivariateCoeffNorm1` at most
`(ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)) ^ #I`. -/
theorem bivariateCoeffNorm1_prod_parityFactorCleared_le (I : Finset κ) (ℓ : ℕ) (Δ : ℤ)
    {A_i : κ → Polynomial ℤ} {B E_ℓ : ℕ}
    (hA : ∀ i ∈ I, (A_i i).coeffNorm1 ≤ B)
    (hE : ∀ s < ℓ, (Polynomial.parityBaseDigit ℓ s).coeffNorm1 ≤ E_ℓ) :
    (∏ i ∈ I, parityFactorCleared ℓ (Polynomial.C Δ) (A_i i)).bivariateCoeffNorm1 ≤
      (ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)) ^ #I := by
  calc
    (∏ i ∈ I, parityFactorCleared ℓ (Polynomial.C Δ) (A_i i)).bivariateCoeffNorm1
      ≤ ∏ i ∈ I, (parityFactorCleared ℓ (Polynomial.C Δ) (A_i i)).bivariateCoeffNorm1 :=
        Polynomial.bivariateCoeffNorm1_prod_le I _
    _ ≤ ∏ _i ∈ I, (ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)) :=
        prod_le_prod fun i hi => bivariateCoeffNorm1_parityFactorCleared_le ℓ Δ (hA i hi) hE
    _ = (ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)) ^ #I := prod_const _

/-- **Appendix B.2 (`∥[V^s] \tilde{H}(T)∥₁ ≤ 2 ^ n * B₁ ^ #I`)**: if every cleared equation
polynomial `clearedMonomialSumPoly d_den k (θ x i) (P i)` has `coeffNorm1 ≤ B` and
`∀ j < ℓ, (parityBaseDigit ℓ j).coeffNorm1 ≤ E_ℓ`, then every coordinate polynomial
`univariateClearedParityCoord I P d_den k ℓ θ s` has `coeffNorm1` at most
`2 ^ Fintype.card ι * (ℓ * E_ℓ * (B + (d_den ^ k).natAbs) ^ (2 * ℓ - 1)) ^ #I`. -/
theorem coeffNorm1_univariateClearedParityCoord_le [Fintype ι] [DecidableEq ι] (I : Finset κ)
    (P : κ → Finset (Finset ι)) (d_den : ℤ) (k ℓ : ℕ) {B E_ℓ : ℕ}
    (θ : (ι → Bool) → κ → ι → Polynomial ℤ)
    (hA : ∀ x : ι → Bool, ∀ i ∈ I,
      (clearedMonomialSumPoly d_den k (θ x i) (P i)).coeffNorm1 ≤ B)
    (hE : ∀ j < ℓ, (Polynomial.parityBaseDigit ℓ j).coeffNorm1 ≤ E_ℓ) (s : ℕ) :
    (univariateClearedParityCoord I P d_den k ℓ θ s).coeffNorm1 ≤
      2 ^ Fintype.card ι * (ℓ * E_ℓ * (B + (d_den ^ k).natAbs) ^ (2 * ℓ - 1)) ^ #I := by
  calc
    (univariateClearedParityCoord I P d_den k ℓ θ s).coeffNorm1
      ≤ (univariateClearedParityProduct I P d_den k ℓ θ).bivariateCoeffNorm1 :=
        Polynomial.coeffNorm1_coeff_le_bivariateCoeffNorm1 _ s
    _ ≤ ∑ x : ι → Bool,
          (∏ i ∈ I,
            parityFactorCleared ℓ (Polynomial.C (d_den ^ k))
              (clearedMonomialSumPoly d_den k (θ x i) (P i))).bivariateCoeffNorm1 :=
        Polynomial.bivariateCoeffNorm1_sum_le univ _
    _ ≤ ∑ _x : ι → Bool, (ℓ * E_ℓ * (B + (d_den ^ k).natAbs) ^ (2 * ℓ - 1)) ^ #I :=
        sum_le_sum fun x _ =>
          bivariateCoeffNorm1_prod_parityFactorCleared_le I ℓ (d_den ^ k) (hA x) hE
    _ = 2 ^ Fintype.card ι * (ℓ * E_ℓ * (B + (d_den ^ k).natAbs) ^ (2 * ℓ - 1)) ^ #I := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, smul_eq_mul]

end Cslib.BitString
