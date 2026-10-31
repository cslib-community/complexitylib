/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IntegralCoordinates
public import Complexity.Foundations.Data.Polynomial.TaperedHermite
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Tapered Hermite recovery with finite precision

This file finishes Lemma D.5 of [OpenAI2026ETH] (§D.4.4, pp. 60–61): the value `F(0)` modulo
`2 ^ p` is recovered from the local jets of `F(t + α z)` modulo `2 ^ p_t`.

**Setting.** Let `K` be a `ℚ`-algebra and `B` a subring of `K` containing `ℤ_(2)`, the rationals
with odd denominator (in the manuscript, `K = ℚ[U] / (f)` and `B = O`). The nodes are the nonzero
points `t` of the grid `S = [-L, L)` of `L = 2 ^ a` slots (`recoveryNodes`), with the tapered
multiplicities `q_t = h max(0, u - v₂ t)` (`taperMult`), and `α = 2 ^ (a + 1)`. From polynomials
`G t ∈ K[z]`, the recovered value (`taperedRecovery`) is the right side of (D.9),

  `∑_t E_t(0) (G t / E_t(t + α z) mod z ^ q_t)(-t / α)`,

with the Hermite basis `E_t` and quotient of
`Polynomial.eval_eq_sum_hermiteBasis_mul_hermiteQuotient`. For `G t = F(t + α z)` and
`deg F < ∑_t q_t` it is `F(0)` (`eval_zero_eq_taperedRecovery`), the manuscript's (D.9).

**Precision.** Each `E_t(t + α z)` is a product of powers of `1 + α z / (t - q)`, so it has
coefficients in `ℤ_(2)` and constant term one, and so has the inverse power series
(`hermiteBasis_comp_eq_map`, `coeff_invOfUnit_hermiteBasis_comp_mem`). The quotient of a jet that
is divisible by `2 ^ p_t` is therefore divisible by `2 ^ p_t`. Evaluating a polynomial of degree
at most `q_t` at `-t / α` multiplies by rationals of valuation at least `-q_t (a + 1)`, and `E_t(0)`
has valuation at least `-6 h D_t` with `D_t = 2 ^ (a - v₂ t)` ((D.10),
`Polynomial.neg_le_padicValRat_eval_zero_hermiteBasis_taper`). So if the jets `G t` agree with
`F(t + α z)` modulo `2 ^ p_t` below `z ^ q_t`, where `p + 6 h D_t + q_t (a + 1) ≤ p_t`, the
recovered value agrees with `F(0)` modulo `2 ^ p` (`exists_taperedRecovery_eq_add`). The
manuscript's choice `p_t = p + 8 h D_t + 8 M (a + 1)` satisfies this when `q_t ≤ 4 M`
(`taperMult_le`); the manuscript's multiplicities have enough total weight
(`le_sum_taperMult`).

Congruences are stated in `K` as `x = y + 2 ^ p * b` with `b ∈ B`.

## Main definitions

* `Cslib.Circuits.Frontier.recoveryNodes`: the nonzero points of the grid.
* `Cslib.Circuits.Frontier.taperMult`: the tapered multiplicities `q_t`.
* `Cslib.Circuits.Frontier.taperedRecovery`: the right side of (D.9) for given jets.

## Main results

* `Cslib.Circuits.Frontier.le_sum_taperMult`: the total multiplicity is at least `2 ^ a h u`.
* `Cslib.Circuits.Frontier.taperMult_le`: `q_t ≤ 4 M` for `h = ⌈3 M / u⌉` and `u ≤ M`.
* `Cslib.Circuits.Frontier.eval_zero_eq_taperedRecovery`: (D.9).
* `Cslib.Circuits.Frontier.hermiteBasis_comp_eq_map`: `E_t(t + α z)` is integral with constant
  term one.
* `Cslib.Circuits.Frontier.exists_taperedRecovery_eq_add`: recovery modulo `2 ^ p` from jets
  modulo `2 ^ p_t`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.4, Lemma D.5,
  (D.9)–(D.10), pp. 60–61.
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### Nodes and multiplicities -/

/-- The nodes of tapered Hermite recovery: the nonzero points of the grid of `2 ^ a` slots. -/
@[expose] def recoveryNodes (a : ℕ) : Finset ℤ :=
  (cauchyGrid (2 ^ a)).erase 0

/-- The tapered multiplicity `q_t = h max(0, u - v₂ t)` of Lemma D.5, with natural
subtraction. -/
@[expose] def taperMult (u h : ℕ) (t : ℤ) : ℕ :=
  h * (u - padicValInt 2 t)

/-- The grid of `2 ^ a` slots is `[-2 ^ a, 2 ^ a)`. -/
theorem cauchyGrid_two_pow (a : ℕ) : cauchyGrid (2 ^ a) = Ico (-(2 : ℤ) ^ a) (2 ^ a) := by
  simp only [cauchyGrid, Nat.cast_pow, Nat.cast_ofNat]

theorem recoveryNodes_eq (a : ℕ) : recoveryNodes a = (Ico (-(2 : ℤ) ^ a) (2 ^ a)).erase 0 := by
  rw [recoveryNodes, cauchyGrid_two_pow]

/-- **There is enough multiplicity.** The `2 ^ a` odd nodes have multiplicity `h u` each. -/
theorem le_sum_taperMult (a u h : ℕ) :
    2 ^ a * (h * u) ≤ ∑ t ∈ recoveryNodes a, taperMult u h t := by
  have key := sum_Ico_erase_zero_padicValInt_two a fun j => ((h * (u - j) : ℕ) : ℤ)
  rw [← recoveryNodes_eq] at key
  have hsum : ((∑ t ∈ recoveryNodes a, taperMult u h t : ℕ) : ℤ) =
      ∑ j ∈ range (a + 1), 2 ^ (a - j) * ((h * (u - j) : ℕ) : ℤ) := by
    rw [← key]
    push_cast [taperMult]
    rfl
  have hle : ((2 ^ a * (h * u) : ℕ) : ℤ) ≤
      ∑ j ∈ range (a + 1), 2 ^ (a - j) * ((h * (u - j) : ℕ) : ℤ) := by
    rw [sum_range_succ']
    simp only [Nat.sub_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have : 0 ≤ ∑ j ∈ range a, (2 : ℤ) ^ (a - (j + 1)) * ((h : ℤ) * ((u - (j + 1) : ℕ) : ℤ)) :=
      sum_nonneg fun j _ => by positivity
    linarith
  exact_mod_cast hle.trans hsum.symm.le

/-- **Multiplicities are at most `4 M`** when `h = ⌈3 M / u⌉` (any `h ≤ 3 M / u + 1`) and
`u ≤ M`. -/
theorem taperMult_le {u h M : ℕ} (hh : h * u ≤ 3 * M + u) (huM : u ≤ M) (t : ℤ) :
    taperMult u h t ≤ 4 * M := by
  unfold taperMult
  calc h * (u - padicValInt 2 t) ≤ h * u := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ 4 * M := by omega

/-! ### The recovered value -/

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The value recovered by tapered Hermite interpolation from the polynomials `G t`: the right
side of (D.9) of [OpenAI2026ETH], `∑_t E_t(0) (G t / E_t(t + α z) mod z ^ q_t)(-t / α)` over the
nonzero grid points `t`, with `α = 2 ^ (a + 1)`. Only the first `q_t` coefficients of `G t`
matter (`Polynomial.hermiteQuotient_trunc`). -/
noncomputable def taperedRecovery (a u h : ℕ) (G : ℤ → K[X]) : K :=
  ∑ t ∈ recoveryNodes a,
    (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h) t).eval 0 *
      (hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h) (2 ^ (a + 1)) t
        (G t)).eval (algebraMap ℚ K (-(t : ℚ) / 2 ^ (a + 1)))

/-- `2 ^ n` as a unit of a `ℚ`-algebra. -/
private noncomputable def twoPowUnit (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) : Kˣ :=
  Units.map (algebraMap ℚ K : ℚ →* K) (Units.mk0 ((2 : ℚ) ^ n) (by positivity))

private theorem coe_twoPowUnit (n : ℕ) : ((twoPowUnit K n : Kˣ) : K) = 2 ^ n := by
  simp [twoPowUnit, map_pow, map_ofNat]

private theorem coe_twoPowUnit_inv (n : ℕ) :
    ((twoPowUnit K n)⁻¹ : Kˣ) = algebraMap ℚ K ((2 : ℚ) ^ n)⁻¹ := by
  simp [twoPowUnit, Units.val_inv_eq_inv_val]

/-- Distinct integers are units of a `ℚ`-algebra apart. -/
private theorem pairwise_isUnit_sub (s : Finset ℤ) :
    (s : Set ℤ).Pairwise fun i j => IsUnit ((i : K) - (j : K)) := by
  intro i _ j _ hij
  have h : ((i : ℚ) - j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  have := (isUnit_iff_ne_zero.mpr h).map (algebraMap ℚ K)
  simpa using this

/-- **Hermite reconstruction (D.9)** of [OpenAI2026ETH]: for `deg F < ∑_t q_t`, the recovered value
from the local polynomials `F(t + α z)` is `F(0)`. -/
theorem eval_zero_eq_taperedRecovery {a u h : ℕ} {F : K[X]}
    (hF : F.degree < ↑(∑ t ∈ recoveryNodes a, taperMult u h t)) :
    F.eval 0 = taperedRecovery a u h fun t => F.comp (C (t : K) + C (2 ^ (a + 1)) * X) := by
  rw [eval_eq_sum_hermiteBasis_mul_hermiteQuotient (pairwise_isUnit_sub _) (twoPowUnit K (a + 1))
    hF 0, taperedRecovery]
  refine sum_congr rfl fun t _ => ?_
  rw [coe_twoPowUnit, coe_twoPowUnit_inv, zero_sub, ← map_intCast (algebraMap ℚ K) t, ← map_neg,
    ← map_mul]
  congr 3
  ring

/-! ### Integrality of the Hermite basis in local coordinates -/

/-- The rationals `α / (t - q)` with `t ≠ q` on the grid, `α = 2 ^ (a + 1)`, lie in `ℤ_(2)`. -/
private theorem padicValuation_two_pow_div_le_one {a : ℕ} {t q : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hq : q ∈ cauchyGrid (2 ^ a)) (hne : q ≠ t) :
    Rat.padicValuation 2 ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) ≤ 1 := by
  have hle := padicValuation_two_pow_le_sub ht hq hne
  have hne' : ((t : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
  rw [map_div₀, div_le_one₀ ((Rat.padicValuation 2).pos_iff.mpr hne')]
  refine le_trans ?_ hle
  rw [pow_succ, map_mul]
  exact mul_le_of_le_one_right' (by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, Rat.padicValuation_natCast]
    exact Int.padicValuation_le_one 2 2)

/-- The Hermite basis over `ℚ` in local coordinates is a product of powers of
`1 + α / (t - q) z`. -/
private theorem hermiteBasis_comp_rat (a u h : ℕ) (t : ℤ) :
    (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) t).comp
        (C (t : ℚ) + C (2 ^ (a + 1)) * X) =
      ∏ q ∈ (recoveryNodes a).erase t,
        (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X) ^ taperMult u h q := by
  rw [hermiteBasis, Polynomial.prod_comp]
  refine prod_congr rfl fun q hq => ?_
  have hqt : ((t : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_mem_erase hq).symm)
  rw [pow_comp, mul_comp, C_comp, sub_comp, X_comp, C_comp, Ring.inverse_eq_inv']
  congr 1
  rw [show C (t : ℚ) + C (2 ^ (a + 1)) * X - C (q : ℚ) =
      C ((t : ℚ) - q) * (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X) by
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hqt, C_sub]; ring,
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ hqt, C_1, one_mul]

/-- **Lemma D.5, integrality.** For a nonzero grid point `t`, the Hermite basis polynomial in
local coordinates, `E_t(t + α z)`, is the image of a polynomial over `ℤ_(2)` with constant term
one: each factor is a power of `1 + α z / (t - q)` with `α / (t - q)` in `ℤ_(2)`. -/
theorem hermiteBasis_comp_eq_map (a u h : ℕ) {t : ℤ} (ht : t ∈ recoveryNodes a) :
    ∃ E : ℤ₍₂₎[X], E.coeff 0 = 1 ∧
      (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h) t).comp
          (C (t : K) + C (2 ^ (a + 1)) * X) =
        E.map ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype) := by
  have htS : t ∈ cauchyGrid (2 ^ a) := mem_of_mem_erase ht
  -- each factor is integral
  have hfac : ∀ q ∈ (recoveryNodes a).erase t,
      (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X) ∈ lifts (ℤ₍₂₎).subtype := fun q hq =>
    add_mem (one_mem _) (mul_mem (C_mem_lifts _ (⟨_, padicValuation_two_pow_div_le_one htS
      (mem_of_mem_erase (mem_of_mem_erase hq)) (ne_of_mem_erase hq)⟩ : ℤ₍₂₎)) (X_mem_lifts _))
  obtain ⟨E, hE⟩ := (mem_lifts _).mp (Subsemiring.prod_mem _ fun q hq =>
    Subsemiring.pow_mem _ (hfac q hq) (taperMult u h q))
  have hEq : E.map (ℤ₍₂₎).subtype = (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ))
      (taperMult u h) t).comp (C (t : ℚ) + C (2 ^ (a + 1)) * X) := by
    rw [hE, hermiteBasis_comp_rat]
  refine ⟨E, ?_, ?_⟩
  · apply Subtype.val_injective
    have h0 := congrArg (fun P => Polynomial.coeff P 0) hEq
    simp only [coeff_map, Subring.coe_subtype] at h0
    rw [h0, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_hermiteBasis_self (pairwise_isUnit_sub _) ht]
    rfl
  · have hv : (fun q : ℤ => algebraMap ℚ K (q : ℚ)) = fun q : ℤ => (q : K) :=
      funext fun q => map_intCast _ q
    have hlin : (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).map (algebraMap ℚ K) =
        C (t : K) + C (2 ^ (a + 1)) * X := by
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_X, map_intCast, map_pow, map_ofNat]
    rw [← Polynomial.map_map, hEq, Polynomial.map_comp,
      map_hermiteBasis _ (pairwise_isUnit_sub _) ht, hv, hlin]

/-- The inverse power series of `E_t(t + α z)` is the image of a power series over `ℤ_(2)`. -/
private theorem invOfUnit_hermiteBasis_comp_eq_map (a u h : ℕ) {t : ℤ} (ht : t ∈ recoveryNodes a) :
    ∃ ψ : PowerSeries ℤ₍₂₎,
      PowerSeries.invOfUnit (((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K))
          (taperMult u h) t).comp (C (t : K) + C (2 ^ (a + 1)) * X) : K[X]) : PowerSeries K) 1 =
        PowerSeries.map ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype) ψ := by
  obtain ⟨E, hE0, hE⟩ := hermiteBasis_comp_eq_map (K := K) a u h ht
  refine ⟨PowerSeries.invOfUnit (E : PowerSeries ℤ₍₂₎) 1, ?_⟩
  set κ := (algebraMap ℚ K).comp (ℤ₍₂₎).subtype
  set φ : PowerSeries K := ((E.map κ : K[X]) : PowerSeries K)
  have hφ : φ = PowerSeries.map κ (E : PowerSeries ℤ₍₂₎) := Polynomial.polynomial_map_coe
  have h1 : φ * PowerSeries.invOfUnit φ 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by
      rw [Polynomial.constantCoeff_coe, coeff_map, hE0, map_one, Units.val_one])
  have h2 : φ * PowerSeries.map κ (PowerSeries.invOfUnit (E : PowerSeries ℤ₍₂₎) 1) = 1 := by
    rw [hφ, ← map_mul, PowerSeries.mul_invOfUnit _ _ (by
      rw [Polynomial.constantCoeff_coe, hE0, Units.val_one]), map_one]
  rw [hE]
  calc PowerSeries.invOfUnit φ 1
      = PowerSeries.invOfUnit φ 1 * (φ * PowerSeries.map κ
          (PowerSeries.invOfUnit (E : PowerSeries ℤ₍₂₎) 1)) := by rw [h2, mul_one]
    _ = PowerSeries.map κ (PowerSeries.invOfUnit (E : PowerSeries ℤ₍₂₎) 1) := by
      rw [← mul_assoc, mul_comm _ φ, h1, one_mul]

/-! ### Congruences modulo powers of two -/

private theorem padicValRat_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact_mod_cast padicValRat.self (p := 2) one_lt_two

omit [Algebra ℚ K] in
/-- `x` is `2 ^ n` times an element of `B`. -/
private def InTwoPow (B : Subring K) (n : ℕ) (x : K) : Prop :=
  ∃ b ∈ B, x = 2 ^ n * b

omit [Algebra ℚ K] in
private theorem inTwoPow_zero (B : Subring K) (n : ℕ) : InTwoPow B n (0 : K) :=
  ⟨0, B.zero_mem, (mul_zero _).symm⟩

omit [Algebra ℚ K] in
private theorem InTwoPow.add {B : Subring K} {n : ℕ} {x y : K} (hx : InTwoPow B n x)
    (hy : InTwoPow B n y) : InTwoPow B n (x + y) := by
  obtain ⟨b, hb, rfl⟩ := hx
  obtain ⟨c, hc, rfl⟩ := hy
  exact ⟨b + c, B.add_mem hb hc, by ring⟩

omit [Algebra ℚ K] in
private theorem InTwoPow.sub {B : Subring K} {n : ℕ} {x y : K} (hx : InTwoPow B n x)
    (hy : InTwoPow B n y) : InTwoPow B n (x - y) := by
  obtain ⟨b, hb, rfl⟩ := hx
  obtain ⟨c, hc, rfl⟩ := hy
  exact ⟨b - c, B.sub_mem hb hc, by ring⟩

omit [Algebra ℚ K] in
private theorem inTwoPow_sum {B : Subring K} {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → K}
    (hf : ∀ i ∈ s, InTwoPow B n (f i)) : InTwoPow B n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact inTwoPow_zero B n
  | insert j s hj ih =>
    rw [sum_insert hj]
    exact (hf j (mem_insert_self j s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

omit [Algebra ℚ K] in
private theorem InTwoPow.mul_left {B : Subring K} {n : ℕ} {x y : K} (hx : InTwoPow B n x)
    (hy : y ∈ B) : InTwoPow B n (x * y) := by
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨b * y, B.mul_mem hb hy, by ring⟩

/-- A rational of valuation at least `-k` maps `2 ^ (n + k) B` into `2 ^ n B`. -/
private theorem InTwoPow.algebraMap_mul {B : Subring K}
    (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {n k : ℕ} {x : K} (hx : InTwoPow B (n + k) x)
    {r : ℚ} (hr : r ≠ 0) (hv : -(k : ℤ) ≤ padicValRat 2 r) :
    InTwoPow B n (algebraMap ℚ K r * x) := by
  obtain ⟨b, hb, rfl⟩ := hx
  have hr2 : r * 2 ^ k ∈ ℤ₍₂₎ := by
    have hne : r * 2 ^ k ≠ 0 := mul_ne_zero hr (by positivity)
    have hval : 0 ≤ padicValRat 2 (r * 2 ^ k) := by
      rw [padicValRat.mul hr (by positivity), padicValRat.pow, padicValRat_two]
      omega
    change Rat.padicValuation 2 (r * 2 ^ k) ≤ 1
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      hne, ↓reduceIte]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  refine ⟨algebraMap ℚ K (r * 2 ^ k) * b, B.mul_mem (hB _ hr2) hb, ?_⟩
  rw [map_mul, map_pow, map_ofNat, pow_add]
  ring

/-- **The quotient of a jet divisible by `2 ^ n` is divisible by `2 ^ n`**: the inverse power
series of `E_t(t + α z)` is integral. -/
private theorem inTwoPow_coeff_hermiteQuotient {B : Subring K}
    (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {a u h n : ℕ} {t : ℤ} (ht : t ∈ recoveryNodes a)
    {P : K[X]} (hP : ∀ j < taperMult u h t, InTwoPow B n (P.coeff j)) (j : ℕ) :
    InTwoPow B n ((hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h)
      (2 ^ (a + 1)) t P).coeff j) := by
  obtain ⟨ψ, hψ⟩ := invOfUnit_hermiteBasis_comp_eq_map (K := K) a u h ht
  rw [hermiteQuotient, hψ, PowerSeries.coeff_trunc]
  split_ifs with hj
  · rw [PowerSeries.coeff_mul]
    refine inTwoPow_sum _ fun kl hkl => ?_
    have hk : kl.1 < taperMult u h t := by
      have := mem_antidiagonal.mp hkl
      omega
    rw [Polynomial.coeff_coe, PowerSeries.coeff_map]
    exact (hP _ hk).mul_left (hB _ (PowerSeries.coeff kl.2 ψ).2)
  · exact inTwoPow_zero B n

/-- The value of `E_t(0)` in `K` is the image of the rational one. -/
private theorem eval_zero_hermiteBasis_eq (a u h : ℕ) {t : ℤ} (ht : t ∈ recoveryNodes a) :
    (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h) t).eval 0 =
      algebraMap ℚ K
        ((hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) t).eval 0) := by
  have hv : (fun q : ℤ => algebraMap ℚ K (q : ℚ)) = fun q : ℤ => (q : K) :=
    funext fun q => map_intCast _ q
  rw [← hv, ← map_hermiteBasis _ (pairwise_isUnit_sub _) ht, eval_map,
    ← map_zero (algebraMap ℚ K), eval₂_at_apply]

/-- `E_t(0) ≠ 0`: its factors are `-q / (t - q)` with `q ≠ 0`. -/
private theorem eval_zero_hermiteBasis_ne_zero (a u h : ℕ) {t : ℤ} :
    (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) t).eval 0 ≠ 0 := by
  rw [eval_hermiteBasis, prod_ne_zero_iff]
  intro q hq
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast ne_of_mem_erase (mem_of_mem_erase hq)
  have hqt : ((t : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (ne_of_mem_erase hq).symm)
  rw [Ring.inverse_eq_inv']
  exact pow_ne_zero _ (mul_ne_zero (inv_ne_zero hqt) (by rwa [zero_sub, neg_ne_zero]))

/-- **Lemma D.5, precision** ([OpenAI2026ETH], §D.4.4, pp. 60–61). Let `B` be a subring of the
`ℚ`-algebra `K` containing `ℤ_(2)`, and let `F ∈ K[T]` have degree below the total multiplicity
`∑_t q_t`. Suppose that at every nonzero grid point `t` the polynomial `G t` agrees with
`F(t + α z)` modulo `2 ^ p_t` below `z ^ q_t`, where `p + 6 h D_t + q_t (a + 1) ≤ p_t` and
`D_t = 2 ^ (a - v₂ t)`. Then the recovered value agrees with `F(0)` modulo `2 ^ p`. -/
theorem exists_taperedRecovery_eq_add (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B)
    {a u h p : ℕ} (pt : ℤ → ℕ)
    (hpt : ∀ t ∈ recoveryNodes a,
      p + 6 * h * 2 ^ (a - padicValInt 2 t) + taperMult u h t * (a + 1) ≤ pt t)
    {F : K[X]} (hF : F.degree < ↑(∑ t ∈ recoveryNodes a, taperMult u h t)) (G : ℤ → K[X])
    (hG : ∀ t ∈ recoveryNodes a, ∀ j < taperMult u h t, ∃ b ∈ B,
      (G t).coeff j = (F.comp (C (t : K) + C (2 ^ (a + 1)) * X)).coeff j + 2 ^ pt t * b) :
    ∃ b ∈ B, taperedRecovery a u h G = F.eval 0 + 2 ^ p * b := by
  suffices hsub : InTwoPow B p (taperedRecovery a u h G - F.eval 0) by
    obtain ⟨b, hb, hb'⟩ := hsub
    exact ⟨b, hb, by rw [← hb', add_sub_cancel]⟩
  rw [eval_zero_eq_taperedRecovery hF, taperedRecovery, taperedRecovery, ← sum_sub_distrib]
  refine inTwoPow_sum _ fun t ht => ?_
  set F' := F.comp (C (t : K) + C (2 ^ (a + 1)) * X)
  set J := taperMult u h t
  set Q := hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h)
    (2 ^ (a + 1)) t ((G t - F' : K[X]) : PowerSeries K)
  have hQ : ∀ j, InTwoPow B (pt t) (Q.coeff j) := by
    refine inTwoPow_coeff_hermiteQuotient hB ht (P := G t - F') (fun j hj => ?_)
    obtain ⟨b, hb, hb'⟩ := hG t ht j hj
    exact ⟨b, hb, by rw [coeff_sub, hb', add_sub_cancel_left]⟩
  have hQsub : hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h)
      (2 ^ (a + 1)) t (G t) - hermiteQuotient (recoveryNodes a) (fun q : ℤ => (q : K))
      (taperMult u h) (2 ^ (a + 1)) t F' = Q := by
    simp only [Q, hermiteQuotient, Polynomial.coe_sub, sub_mul, map_sub]
  have hdeg : Q.natDegree < J + 1 := by
    have := degree_hermiteQuotient_lt (recoveryNodes a) (fun q : ℤ => (q : K)) (taperMult u h)
      (2 ^ (a + 1)) t ((G t - F' : K[X]) : PowerSeries K)
    by_cases hQ0 : Q = 0
    · rw [hQ0, natDegree_zero]; omega
    · have := (natDegree_lt_iff_degree_lt hQ0).mpr this
      omega
  rw [← mul_sub, ← eval_sub, hQsub, eval_eq_sum_range' hdeg, mul_sum,
    eval_zero_hermiteBasis_eq a u h ht]
  refine inTwoPow_sum _ fun j hj => ?_
  have hjJ : j ≤ J := Nat.lt_succ_iff.mp (mem_range.mp hj)
  set E0 := (hermiteBasis (recoveryNodes a) (fun q : ℤ => (q : ℚ)) (taperMult u h) t).eval 0
  have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast ne_of_mem_erase ht
  have hx0 : (-(t : ℚ) / 2 ^ (a + 1)) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ht0) (by positivity)
  have hr : E0 * (-(t : ℚ) / 2 ^ (a + 1)) ^ j ≠ 0 :=
    mul_ne_zero (eval_zero_hermiteBasis_ne_zero a u h) (pow_ne_zero _ hx0)
  have hE0 : -(6 * (h : ℤ) * 2 ^ (a - padicValInt 2 t)) ≤ padicValRat 2 E0 := by
    have := neg_le_padicValRat_eval_zero_hermiteBasis_taper (a := a) u h
      (mem_of_mem_erase (by rw [← recoveryNodes_eq]; exact ht)) (ne_of_mem_erase ht)
    rw [← recoveryNodes_eq] at this
    exact this
  have hxv : -((a : ℤ) + 1) ≤ padicValRat 2 (-(t : ℚ) / 2 ^ (a + 1)) := by
    rw [padicValRat.div (neg_ne_zero.mpr ht0) (by positivity), padicValRat.neg,
      padicValRat.of_int, padicValRat.pow, padicValRat_two]
    push_cast
    omega
  have hval : -((pt t - p : ℕ) : ℤ) ≤ padicValRat 2 (E0 * (-(t : ℚ) / 2 ^ (a + 1)) ^ j) := by
    rw [padicValRat.mul (eval_zero_hermiteBasis_ne_zero a u h) (pow_ne_zero _ hx0),
      padicValRat.pow]
    have hpt' := hpt t ht
    have hJ : (j : ℤ) * padicValRat 2 (-(t : ℚ) / 2 ^ (a + 1)) ≥ -((J : ℤ) * ((a : ℤ) + 1)) := by
      have : (j : ℤ) ≤ J := by exact_mod_cast hjJ
      nlinarith
    have : ((pt t - p : ℕ) : ℤ) = (pt t : ℤ) - p := by omega
    push_cast [this]
    have hpt'' : (p : ℤ) + 6 * h * 2 ^ (a - padicValInt 2 t) + (J : ℤ) * (a + 1) ≤ pt t := by
      exact_mod_cast hpt'
    linarith
  have hk : p + (pt t - p) = pt t := by have := hpt t ht; omega
  have hQj := hQ j
  rw [← hk] at hQj
  have := hQj.algebraMap_mul hB hr hval
  rw [map_mul, map_pow] at this
  convert this using 1
  ring

/-- **Lemma D.5 with the manuscript's parameters.** Let `1 ≤ u ≤ M`, let `h` satisfy
`3 M ≤ h u ≤ 3 M + u` (as `h = ⌈3 M / u⌉` does), and let `F` have degree at most `M (2 L - 1)`,
`L = 2 ^ a`. If the jets `G t` agree with `F(t + α z)` modulo `2 ^ p_t` below `z ^ q_t`, with
`p_t = p + 8 h D_t + 8 M (a + 1)`, then the recovered value agrees with `F(0)` modulo `2 ^ p`. -/
theorem exists_taperedRecovery_eq_add_of_params (B : Subring K)
    (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {a u h p M : ℕ} (hu : 1 ≤ u) (huM : u ≤ M)
    (hh : 3 * M ≤ h * u) (hh' : h * u ≤ 3 * M + u) {F : K[X]}
    (hF : F.natDegree ≤ M * (2 * 2 ^ a - 1)) (G : ℤ → K[X])
    (hG : ∀ t ∈ recoveryNodes a, ∀ j < taperMult u h t, ∃ b ∈ B,
      (G t).coeff j = (F.comp (C (t : K) + C (2 ^ (a + 1)) * X)).coeff j +
        2 ^ (p + 8 * h * 2 ^ (a - padicValInt 2 t) + 8 * M * (a + 1)) * b) :
    ∃ b ∈ B, taperedRecovery a u h G = F.eval 0 + 2 ^ p * b := by
  refine exists_taperedRecovery_eq_add B hB
    (fun t => p + 8 * h * 2 ^ (a - padicValInt 2 t) + 8 * M * (a + 1)) (fun t _ => ?_) ?_ G hG
  · have hJ := taperMult_le hh' huM t
    have hD : 6 * h * 2 ^ (a - padicValInt 2 t) ≤ 8 * h * 2 ^ (a - padicValInt 2 t) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    have hJa : taperMult u h t * (a + 1) ≤ 8 * M * (a + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · refine (degree_le_natDegree).trans_lt ?_
    have hsum := le_sum_taperMult a u h
    have hM : 1 ≤ M := hu.trans huM
    have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have : M * (2 * 2 ^ a - 1) < 2 ^ a * (h * u) := by
      have h3 : 2 ^ a * (3 * M) ≤ 2 ^ a * (h * u) := Nat.mul_le_mul_left _ hh
      have : M * (2 * 2 ^ a - 1) < 2 ^ a * (3 * M) := by
        rw [Nat.mul_sub, mul_one]
        have : M * (2 * 2 ^ a) = 2 * (2 ^ a * M) := by ring
        have : 2 ^ a * (3 * M) = 3 * (2 ^ a * M) := by ring
        have : 1 ≤ 2 ^ a * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      omega
    exact_mod_cast (hF.trans_lt (this.trans_le hsum))

end Cslib.Circuits.Frontier
