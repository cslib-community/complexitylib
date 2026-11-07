/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CauchyModes
import Complexity.Foundations.NumberTheory.Padics.RatValuation

/-!
# The local Cauchy kernel as a product of units

Lemma D.4 of [OpenAI2026ETH] (pp. 59–60) shows that the Cauchy kernel `W_d` on the grid `S` of
`L = 2 ^ a` slots has `2`-integral coefficients in the local coordinate `z`, `T = t + α z`,
`α = 2 ^ (a + 1)`. The source evaluates it by dividing each factor `t - q + α z`, `q ≠ t`, by the
known power `2 ^ v₂(t - q)` and inverting only odd integers (p. 60). This file proves the resulting
product formula, so that a kernel value is computed with ring operations and inverses of odd
integers.

Write `t - q = 2 ^ v_q u_q` with `u_q` odd. Since `S` is a complete residue system modulo
`2 ^ (a + 1)`, the valuations `v_q`, `q ≠ t`, sum to those of the normalization
`C'(0) = ∏_{q ≠ 0} (0 - q)` (`sum_padicValInt_sub_eq`). So the powers of two cancel, and

* `W_t(t + α z) = c ∏_{q ≠ t} (u_q + 2 ^ (a + 1 - v_q) z)`,
* `W_d(t + α z) = c 2 ^ (a + 1 - v_d) z ∏_{q ≠ d, t} (u_q + 2 ^ (a + 1 - v_q) z)` for `d ≠ t`,

where `c = ∏_{q ≠ 0} u'_q⁻¹` is the inverse of the odd part of `C'(0)` (`kernelUnit`). Every
factor is integral, and `c` is a unit of `ℤ_(2)` (`localKernel_eq_prod`). Evaluating at `ζ` in a
ring receiving `ℤ_(2)` gives `kernelValue_eq_prod`.

## Main definitions

* `Cslib.Circuits.Frontier.kernelUnit`: the inverse of the odd part of `C'(0)`, in `ℤ_(2)`.

## Main results

* `Cslib.Circuits.Frontier.sum_padicValInt_sub_eq`: the valuations of `t - q` sum to those of
  `C'(0)`.
* `Cslib.Circuits.Frontier.localKernel_eq_prod`: the local kernel as a product of units.
* `Cslib.Circuits.Frontier.kernelValue_eq_prod`: its values.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.4 and its
  evaluation, pp. 59–60.
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-- An integer is `2 ^ v₂(n)` times its odd part `n / 2 ^ v₂(n)`. -/
private theorem two_pow_mul_ediv (n : ℤ) : 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) = n :=
  Int.mul_ediv_cancel' (by exact_mod_cast padicValInt_dvd (p := 2) n)

/-- The odd part of a nonzero integer is nonzero. -/
private theorem ediv_ne_zero {n : ℤ} (hn : n ≠ 0) : n / 2 ^ padicValInt 2 n ≠ 0 := by
  intro h
  exact hn (by rw [← two_pow_mul_ediv n, h, mul_zero])

/-- The odd part of a nonzero integer is not divisible by `2`. -/
private theorem padicValInt_ediv_eq_zero {n : ℤ} (hn : n ≠ 0) :
    padicValInt 2 (n / 2 ^ padicValInt 2 n) = 0 := by
  refine padicValInt.eq_zero_of_not_dvd fun ⟨c, hc⟩ => ?_
  have hc' : n / 2 ^ padicValInt 2 n = 2 * c := by exact_mod_cast hc
  have h2 : (2 : ℤ) ^ (padicValInt 2 n + 1) ∣ n := ⟨c, by
    calc n = 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) := (two_pow_mul_ediv n).symm
      _ = 2 ^ (padicValInt 2 n + 1) * c := by rw [hc', pow_succ]; ring⟩
  have h := (padicValInt_dvd_iff (p := 2) (padicValInt 2 n + 1) n).mp (by exact_mod_cast h2)
  omega

/-- The valuation of the odd part of a nonzero integer is one. -/
private theorem padicValuation_ediv {n : ℤ} (hn : n ≠ 0) :
    Rat.padicValuation 2 (((n / 2 ^ padicValInt 2 n : ℤ) : ℚ)) = 1 := by
  rw [Rat.padicValuation_intCast_of_ne_zero 2 (ediv_ne_zero hn), padicValInt_ediv_eq_zero hn]
  rfl

/-- The inverse of an odd part is `2`-integral. -/
private theorem inv_ediv_mem {n : ℤ} (hn : n ≠ 0) :
    (((n / 2 ^ padicValInt 2 n : ℤ) : ℚ))⁻¹ ∈ ℤ₍₂₎ := by
  change Rat.padicValuation 2 _ ≤ 1
  rw [map_inv₀, padicValuation_ediv hn, inv_one]

/-- Distinct grid points of `2 ^ a` slots differ by at most `a` factors of two. -/
private theorem padicValInt_sub_le {a : ℕ} {t q : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hq : q ∈ cauchyGrid (2 ^ a)) (hne : q ≠ t) : padicValInt 2 (t - q) ≤ a := by
  have hval := padicValuation_two_pow_le_sub ht hq hne
  have hne' : t - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : Rat.padicValuation 2 ((2 : ℚ) ^ a) = WithZero.exp (-(a : ℤ)) := by
    exact_mod_cast Rat.padicValuation_pow_self 2 a
  have h' : Rat.padicValuation 2 ((t : ℚ) - q) = Rat.padicValuation 2 ((t - q : ℤ) : ℚ) := by
    push_cast; rfl
  rw [h', Rat.padicValuation_intCast_of_ne_zero 2 hne', h2, WithZero.exp_le_exp] at hval
  omega

/-- A product of differences `s - q` over the other grid points is `2 ^ (∑ v₂(s - q))` times the
product of their odd parts. -/
private theorem prod_sub_eq (s : ℤ) (F : Finset ℤ) :
    ∏ q ∈ F, ((s : ℚ) - q) = 2 ^ (∑ q ∈ F, padicValInt 2 (s - q)) *
      ∏ q ∈ F, (((s - q) / 2 ^ padicValInt 2 (s - q) : ℤ) : ℚ) := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun q _ => ?_
  exact_mod_cast (two_pow_mul_ediv (s - q)).symm

/-- **The valuations of the differences sum to those of the normalization.** For `t` on the grid
of `2 ^ a` slots, `∑_{q ≠ t} v₂(t - q) = ∑_{q ≠ 0} v₂(0 - q)`. -/
theorem sum_padicValInt_sub_eq {a : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) :
    ∑ q ∈ (cauchyGrid (2 ^ a)).erase t, padicValInt 2 (t - q) =
      ∑ q ∈ (cauchyGrid (2 ^ a)).erase 0, padicValInt 2 (0 - q) := by
  have hv (s : ℤ) : Rat.padicValuation 2 (∏ q ∈ (cauchyGrid (2 ^ a)).erase s, ((s : ℚ) - q)) =
      WithZero.exp (-((∑ q ∈ (cauchyGrid (2 ^ a)).erase s, padicValInt 2 (s - q) : ℕ) : ℤ)) := by
    rw [prod_sub_eq s, map_mul, map_prod]
    rw [prod_eq_one fun q hq => padicValuation_ediv (sub_ne_zero.mpr
      (Ne.symm (ne_of_mem_erase hq))), mul_one]
    exact_mod_cast Rat.padicValuation_pow_self 2 _
  have h := padicValuation_prod_sub_eq ht
  have h0 := hv 0
  push_cast at h0
  rw [hv t, h0, WithZero.exp_inj, neg_inj] at h
  exact_mod_cast h

/-- The inverse `∏_{q ≠ 0} u'_q⁻¹` of the odd part of `C'(0) = ∏_{q ≠ 0} (0 - q)`, a unit of
`ℤ_(2)`, with `u'_q` the odd part of `0 - q`. -/
noncomputable def kernelUnit (a : ℕ) : ℤ₍₂₎ :=
  ∏ q ∈ (cauchyGrid (2 ^ a)).erase 0,
    if h : (0 : ℤ) - q = 0 then 1 else ⟨_, inv_ediv_mem h⟩

/-- The value of `kernelUnit`. -/
theorem coe_kernelUnit (a : ℕ) :
    ((kernelUnit a : ℤ₍₂₎) : ℚ) = (∏ q ∈ (cauchyGrid (2 ^ a)).erase 0,
      (((0 - q) / 2 ^ padicValInt 2 (0 - q) : ℤ) : ℚ))⁻¹ := by
  change (ℤ₍₂₎).subtype (kernelUnit a) = _
  rw [kernelUnit, map_prod, ← prod_inv_distrib]
  refine prod_congr rfl fun q hq => ?_
  have hne : (0 : ℤ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_mem_erase hq))
  rw [dite_eq_right hne]
  rfl

/-- The `2`-integral factor `u_q + 2 ^ (a + 1 - v_q) z` of the local kernel, where
`t - q = 2 ^ v_q u_q`. -/
private noncomputable def unitFactor (a : ℕ) (t q : ℤ) : ℤ₍₂₎[X] :=
  C (((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) : ℤ₍₂₎) +
    C ((2 : ℤ₍₂₎) ^ (a + 1 - padicValInt 2 (t - q))) * X

private theorem map_unitFactor (a : ℕ) (t q : ℤ) :
    (unitFactor a t q).map (ℤ₍₂₎).subtype =
      C ((((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) : ℚ)) +
        C ((2 : ℚ) ^ (a + 1 - padicValInt 2 (t - q))) * X := by
  simp only [unitFactor, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_X, map_intCast, map_pow, map_ofNat, Polynomial.map_intCast,
    Polynomial.map_pow, Polynomial.map_ofNat]

/-- A shifted factor `t + α z - q`, `q ≠ t` on the grid, is `2 ^ v_q` times the unit factor. -/
private theorem shift_eq_unitFactor {a : ℕ} {t q : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hq : q ∈ cauchyGrid (2 ^ a)) (hne : q ≠ t) :
    C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X - C (q : ℚ) =
      C ((2 : ℚ) ^ padicValInt 2 (t - q)) * (unitFactor a t q).map (ℤ₍₂₎).subtype := by
  have hle := padicValInt_sub_le ht hq hne
  have hsplit : ((t : ℚ) - q) = 2 ^ padicValInt 2 (t - q) *
      (((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) : ℚ) := by
    exact_mod_cast (two_pow_mul_ediv (t - q)).symm
  have hpow : (2 : ℚ) ^ padicValInt 2 (t - q) * 2 ^ (a + 1 - padicValInt 2 (t - q)) =
      2 ^ (a + 1) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [map_unitFactor, mul_add, ← mul_assoc, ← C_mul, ← C_mul, hpow, ← hsplit, C_sub]
  ring

/-- The shifted factors over grid points other than `t`. -/
private theorem prod_shift_eq {a : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (F : Finset ℤ)
    (hF : F ⊆ (cauchyGrid (2 ^ a)).erase t) :
    ∏ q ∈ F, (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X - C (q : ℚ)) =
      C ((2 : ℚ) ^ ∑ q ∈ F, padicValInt 2 (t - q)) *
        ∏ q ∈ F, (unitFactor a t q).map (ℤ₍₂₎).subtype := by
  rw [← prod_pow_eq_pow_sum, map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun q hq => ?_
  obtain ⟨hqt, hqS⟩ := mem_erase.mp (hF hq)
  exact shift_eq_unitFactor ht hqS hqt

/-- **The local kernel as a product of units** (Lemma D.4 and its evaluation, p. 60). For grid
points `t` and `d` of `2 ^ a` slots, with `t - q = 2 ^ v_q u_q`, `u_q` odd, the local kernel is
`kernelUnit a` times `∏_{q ≠ d, t} (u_q + 2 ^ (a + 1 - v_q) z)`, times `2 ^ (a + 1 - v_d) z` when
`d ≠ t`. -/
theorem localKernel_eq_prod {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) :
    localKernel a t d = C (kernelUnit a) *
      (if d = t then 1 else C ((2 : ℤ₍₂₎) ^ (a + 1 - padicValInt 2 (t - d))) * X) *
      ∏ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t,
        (C (((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) : ℤ₍₂₎) +
          C ((2 : ℤ₍₂₎) ^ (a + 1 - padicValInt 2 (t - q))) * X) := by
  refine Polynomial.map_injective (ℤ₍₂₎).subtype Subtype.val_injective ?_
  rw [map_localKernel ht hd, cauchyKernel, Lagrange.eval_nodal, mul_comp, C_comp, Lagrange.nodal,
    Polynomial.prod_comp]
  simp only [sub_comp, X_comp, C_comp]
  -- The normalization `C'(0) = 2 ^ S₀ w`.
  set S₀ := ∑ q ∈ (cauchyGrid (2 ^ a)).erase 0, padicValInt 2 (0 - q)
  set w := ∏ q ∈ (cauchyGrid (2 ^ a)).erase 0, (((0 - q) / 2 ^ padicValInt 2 (0 - q) : ℤ) : ℚ)
  have hC0 : ∏ q ∈ (cauchyGrid (2 ^ a)).erase 0, ((0 : ℚ) - (q : ℚ)) = 2 ^ S₀ * w := by
    have := prod_sub_eq 0 ((cauchyGrid (2 ^ a)).erase 0)
    push_cast at this
    exact this
  have hsum := sum_padicValInt_sub_eq ht
  have hRHS : (C (kernelUnit a) *
      (if d = t then 1 else C ((2 : ℤ₍₂₎) ^ (a + 1 - padicValInt 2 (t - d))) * X) *
      ∏ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t,
        (C (((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) : ℤ₍₂₎) +
          C ((2 : ℤ₍₂₎) ^ (a + 1 - padicValInt 2 (t - q))) * X)).map (ℤ₍₂₎).subtype =
      C w⁻¹ * (if d = t then 1 else C ((2 : ℚ) ^ (a + 1 - padicValInt 2 (t - d))) * X) *
        ∏ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t, (unitFactor a t q).map (ℤ₍₂₎).subtype := by
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    congr 2
    · exact congrArg C (coe_kernelUnit a)
    · split_ifs
      · exact Polynomial.map_one _
      · simp only [Polynomial.map_mul, Polynomial.map_X, map_pow, map_ofNat, Polynomial.map_pow,
          Polynomial.map_ofNat]
  rw [hRHS, hC0]
  rcases eq_or_ne d t with rfl | hdt
  · rw [ite_eq_left rfl, mul_one, erase_idem, prod_shift_eq ht _ subset_rfl, hsum, ← mul_assoc,
      ← C_mul]
    congr 2
    rw [mul_inv]
    change ((2 : ℚ) ^ S₀)⁻¹ * w⁻¹ * 2 ^ S₀ = w⁻¹
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  · rw [ite_eq_right hdt]
    have htd : t ∈ (cauchyGrid (2 ^ a)).erase d := mem_erase.mpr ⟨hdt.symm, ht⟩
    have hdt' : d ∈ (cauchyGrid (2 ^ a)).erase t := mem_erase.mpr ⟨hdt, hd⟩
    have hsub : ((cauchyGrid (2 ^ a)).erase d).erase t ⊆ (cauchyGrid (2 ^ a)).erase t :=
      fun q hq => by
        simp only [mem_erase] at hq ⊢
        exact ⟨hq.1, hq.2.2⟩
    set sv := ∑ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t, padicValInt 2 (t - q)
    set U := ∏ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t, (unitFactor a t q).map (ℤ₍₂₎).subtype
    -- `S₀ = v_d + ∑_{q ≠ d, t} v_q`.
    have hsplit : S₀ = padicValInt 2 (t - d) + sv :=
      calc S₀ = ∑ q ∈ (cauchyGrid (2 ^ a)).erase t, padicValInt 2 (t - q) := hsum.symm
        _ = padicValInt 2 (t - d) +
            ∑ q ∈ ((cauchyGrid (2 ^ a)).erase t).erase d, padicValInt 2 (t - q) :=
          (add_sum_erase _ (fun q => padicValInt 2 (t - q)) hdt').symm
        _ = padicValInt 2 (t - d) + sv := by rw [erase_right_comm]
    have hvd := padicValInt_sub_le ht hd hdt
    have hw : w ≠ 0 := prod_ne_zero_iff.mpr fun q hq => by
      exact_mod_cast ediv_ne_zero (sub_ne_zero.mpr (Ne.symm (ne_of_mem_erase hq)))
    rw [← mul_prod_erase _ _ htd, prod_shift_eq ht _ hsub,
      show C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X - C (t : ℚ) = C ((2 : ℚ) ^ (a + 1)) * X by ring]
    have hL : C (2 ^ S₀ * w)⁻¹ * (C ((2 : ℚ) ^ (a + 1)) * X * (C ((2 : ℚ) ^ sv) * U)) =
        C ((2 ^ S₀ * w)⁻¹ * 2 ^ (a + 1) * 2 ^ sv) * (X * U) := by
      rw [C_mul, C_mul]; ring
    have hR : C w⁻¹ * (C ((2 : ℚ) ^ (a + 1 - padicValInt 2 (t - d))) * X) * U =
        C (w⁻¹ * 2 ^ (a + 1 - padicValInt 2 (t - d))) * (X * U) := by
      rw [C_mul]; ring
    rw [hL, hR]
    congr 2
    have h2 : (2 : ℚ) ^ (a + 1) =
        2 ^ (a + 1 - padicValInt 2 (t - d)) * 2 ^ padicValInt 2 (t - d) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h2, hsplit, pow_add]
    field_simp

/-- **Kernel values as products of units.** In a ring `R` receiving `ℤ_(2)` through `κ`, the
kernel value `W_d(t + α ζ)` is `κ(kernelUnit a)` times `∏_{q ≠ d, t} (u_q + 2 ^ (a + 1 - v_q) ζ)`,
times `2 ^ (a + 1 - v_d) ζ` when `d ≠ t`. -/
theorem kernelValue_eq_prod {R : Type*} [CommRing R] (κ : ℤ₍₂₎ →+* R) (ζ : R) {a : ℕ}
    {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hd : d ∈ cauchyGrid (2 ^ a)) :
    kernelValue κ ζ a t d = κ (kernelUnit a) *
      (if d = t then 1 else 2 ^ (a + 1 - padicValInt 2 (t - d)) * ζ) *
      ∏ q ∈ ((cauchyGrid (2 ^ a)).erase d).erase t,
        (((t - q) / 2 ^ padicValInt 2 (t - q) : ℤ) + 2 ^ (a + 1 - padicValInt 2 (t - q)) * ζ) := by
  rw [kernelValue, localKernel_eq_prod ht hd]
  change eval₂RingHom κ ζ _ = _
  rw [map_mul, map_mul, map_prod]
  simp only [coe_eval₂RingHom, eval₂_C]
  congr 1
  · congr 1
    split_ifs
    · exact eval₂_one _ _
    · rw [eval₂_mul, eval₂_C, eval₂_X, map_pow, map_ofNat]
  · refine prod_congr rfl fun q _ => ?_
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, map_intCast, map_pow, map_ofNat]

end Cslib.Circuits.Frontier
