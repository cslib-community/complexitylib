/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IntegralCoordinates
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ModeExpansion
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The geometric expansion of the Cauchy kernel

This file proves the geometric expansion (D.12) of [OpenAI2026ETH] (§D.4.5, p. 62), which turns
the crossing entries of the Cauchy matrix near a grid point into the modes of
`Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting`.

**Local kernels** (`localKernel`). By Lemma D.4 (`cauchyKernel_comp_mem_lifts`), the Cauchy kernel
`W_d` on the grid of `L = 2 ^ a` slots has `2`-integral coefficients in local coordinates
`z ↦ W_d(t + α z)`, `α = 2 ^ (a + 1)`. `localKernel a t d` is this polynomial over `ℤ_(2)`, and for
a ring homomorphism `κ : ℤ_(2) → R` and `ζ ∈ R`, `kernelValue κ ζ a t d` is its value
`W_d(t + α ζ)` in `R`.

**The expansion.** Fix `t` and two grid points `d₀` and `d = d₀ + 2 ^ (i + 1) j` with
`2 ^ (i + 1) ∤ t - d₀`, `i ≤ a`. All kernels are `C(T) / (C'(0) (T - d))`, so
`W_d(T) (T - d) = W_{d₀}(T) (T - d₀)`. Write `t - d₀ = 2 ^ v u₀` with `u₀` odd and `v ≤ i`; dividing
by `2 ^ v` in `ℤ_(2)[z]` makes

  `W_d(t + α z) (u₀ + 2 ^ (a + 1 - v) z - 2 ^ (i + 1 - v) j)` equal to
  `W_{d₀}(t + α z) (u₀ + 2 ^ (a + 1 - v) z)`

(`localKernel_mul_eq`). In a ring `R` with `2 ^ p = 0`, `U = u₀ + 2 ^ (a + 1 - v) ζ` is a unit, and
with the *cross ratio* `ρ = 2 ^ (i + 1 - v) U⁻¹ = 2 ^ (i + 1) / (T - d₀)` (`crossRatio`) the factor
`1 - ρ j` is inverted by its geometric series, since `2 ∣ ρ`:

  `W_d(T) = ∑_{b < p} W_{d₀}(T) ρ ^ b j ^ b`        (`kernelValue_eq_sum`),

the manuscript's (D.12), there written with the remainder beyond `b + 1 < p_t` dropped modulo
`2 ^ p_t`. When `d₀ ≠ t`, `W_{d₀}(T)` is divisible by `2` (Lemma D.4), so the coefficient of `j ^ b`
is divisible by `2 ^ (b + 1)` (`two_pow_dvd_kernelValue_mul_crossRatio_pow`): the weight
`w_Z = b + 1` of the mode.

**The modes of a packing** (`TensorNetwork.cauchyModeSplitting`). Pack the edges into packets of
`2 ^ a` slots, oriented in coordinate `i` as in Lemma D.3 (2): each packet `q` has a pair of groups,
and digit `i` of an edge's slot says which of them is its row group. For a grid point `t` of
valuation `i`, a row slot `x` and a column slot `y` of a packet with two different groups lie in
different groups exactly when their digits `i` agree, and then `v₂(t - y₀ + x) ≤ i` for the tile
`y₀ = y mod 2 ^ (i + 1)` (`not_dvd_sub_sub_of_testBit_eq`). So the Cauchy matrix at `T = t + α ζ`
(`TensorNetwork.cauchyValueMatrix`) splits into its local entries and one mode per packet, tile and
`b < p`, of weight `b + 1`, and the child identity of
`Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting` applies
(`TensorNetwork.deformedContraction_cauchyValueMatrix_eq_sum`). The manuscript's modes are those
with `b + 1 < p_t`; the one with `b + 1 = p_t` has weight `p_t` and drops out of (D.14).

## Main definitions

* `Cslib.Circuits.Frontier.localKernel`: the Cauchy kernel in local coordinates over `ℤ_(2)`.
* `Cslib.Circuits.Frontier.kernelValue`: its value at `z = ζ` in a `ℤ_(2)`-algebra.
* `Cslib.Circuits.Frontier.crossRatio`: the ratio `2 ^ (i + 1) / (T - d₀)`.
* `Cslib.Circuits.Frontier.TensorNetwork.cauchyValueMatrix`: the Cauchy matrix of a packing at
  `T = t + α ζ`.
* `Cslib.Circuits.Frontier.TensorNetwork.cauchyModeCoeff`,
  `Cslib.Circuits.Frontier.TensorNetwork.cauchyModeForm`: the coefficients and forms of its modes.
* `Cslib.Circuits.Frontier.TensorNetwork.cauchyModeSplitting`: its mode splitting.

## Main results

* `Cslib.Circuits.Frontier.map_localKernel`: the local kernel is the composed Cauchy kernel.
* `Cslib.Circuits.Frontier.exists_localKernel_eq_two_mul`: away from its node it is divisible by
  `2`.
* `Cslib.Circuits.Frontier.localKernel_mul_eq`: the exact relation between the kernels at `d₀`
  and `d₀ + 2 ^ (i + 1) j`.
* `Cslib.Circuits.Frontier.kernelValue_eq_sum`: the geometric expansion (D.12).
* `Cslib.Circuits.Frontier.two_pow_dvd_kernelValue_mul_crossRatio_pow`: its coefficients are
  divisible by `2 ^ (b + 1)`.
* `Cslib.Circuits.Frontier.not_dvd_sub_sub_of_testBit_eq`: a row and a column tile with the same
  digit `i` give `v₂(t - y₀ + x) ≤ i`.
* `Cslib.Circuits.Frontier.TensorNetwork.two_pow_dvd_cauchyModeCoeff`: the modes have weight
  `b + 1`.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_cauchyValueMatrix_eq_sum`: the child
  identity (D.16) for the Cauchy matrix of a packing.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.3 (2) (p. 58),
  Lemma D.4 (pp. 59–60), and §D.4.5–§D.4.6, (D.12)–(D.16) (pp. 62–63).
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### Local kernels over `ℤ_(2)` -/

/-- The Cauchy kernel `W_d` on the grid of `2 ^ a` slots in local coordinates
`z ↦ W_d(t + α z)`, `α = 2 ^ (a + 1)`, as a polynomial over `ℤ_(2)` (Lemma D.4 of
[OpenAI2026ETH]); zero when `t` or `d` is off the grid. -/
noncomputable def localKernel (a : ℕ) (t d : ℤ) : ℤ₍₂₎[X] :=
  if h : t ∈ cauchyGrid (2 ^ a) ∧ d ∈ cauchyGrid (2 ^ a) then
    ((mem_lifts _).mp (cauchyKernel_comp_mem_lifts h.1 h.2)).choose
  else 0

/-- The local kernel is the Cauchy kernel composed with `t + α z`. -/
theorem map_localKernel {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) :
    (localKernel a t d).map (ℤ₍₂₎).subtype =
      (cauchyKernel (2 ^ a) d).comp (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X) := by
  rw [localKernel, dite_eq_left ⟨ht, hd⟩]
  exact ((mem_lifts _).mp (cauchyKernel_comp_mem_lifts ht hd)).choose_spec

private theorem map_subtype_injective :
    Function.Injective (Polynomial.map (ℤ₍₂₎).subtype) :=
  Polynomial.map_injective _ Subtype.val_injective

/-- **Lemma D.4, divisibility, over `ℤ_(2)`.** Away from its node, the local kernel is twice a
polynomial over `ℤ_(2)`. -/
theorem exists_localKernel_eq_two_mul {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) (hdt : d ≠ t) : ∃ Q : ℤ₍₂₎[X], localKernel a t d = C 2 * Q := by
  obtain ⟨P, hP, h⟩ := exists_cauchyKernel_comp_eq_two_mul ht hd hdt
  obtain ⟨Q, rfl⟩ := (mem_lifts _).mp hP
  refine ⟨Q, map_subtype_injective ?_⟩
  rw [map_localKernel ht hd, h, Polynomial.map_mul, Polynomial.map_C]
  congr 2

/-- Every kernel on the grid is `C(T) / C'(0)` divided by `T - d`. -/
private theorem cauchyKernel_mul_X_sub {L : ℕ} {d : ℤ} (hd : d ∈ cauchyGrid L) :
    cauchyKernel L d * (X - C (d : ℚ)) =
      C ((Lagrange.nodal ((cauchyGrid L).erase 0) (Int.cast : ℤ → ℚ)).eval 0)⁻¹ *
        Lagrange.nodal (cauchyGrid L) (Int.cast : ℤ → ℚ) := by
  rw [cauchyKernel, Lagrange.nodal_eq_mul_nodal_erase hd]
  ring

/-- **The kernels of a tile.** For grid points `d₀` and `d = d₀ + 2 ^ (i + 1) j`, with
`t - d₀ = 2 ^ v u₀` and `v ≤ i ≤ a`, the local kernels satisfy
`W_d (u₀ + 2 ^ (a + 1 - v) z - 2 ^ (i + 1 - v) j) = W_{d₀} (u₀ + 2 ^ (a + 1 - v) z)`: both sides
are `C(t + α z) / (C'(0) 2 ^ v)`. -/
theorem localKernel_mul_eq {a i v : ℕ} {t d₀ d j u₀ : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd₀ : d₀ ∈ cauchyGrid (2 ^ a)) (hd : d ∈ cauchyGrid (2 ^ a))
    (hdd : d = d₀ + 2 ^ (i + 1) * j) (htd : t - d₀ = 2 ^ v * u₀) (hvi : v ≤ i) (hia : i ≤ a) :
    localKernel a t d * (C (u₀ : ℤ₍₂₎) + C ((2 : ℤ₍₂₎) ^ (a + 1 - v)) * X -
        C ((2 ^ (i + 1 - v) * j : ℤ) : ℤ₍₂₎)) =
      localKernel a t d₀ * (C (u₀ : ℤ₍₂₎) + C ((2 : ℤ₍₂₎) ^ (a + 1 - v)) * X) := by
  refine map_subtype_injective ?_
  have hmap₁ : (C (u₀ : ℤ₍₂₎) + C ((2 : ℤ₍₂₎) ^ (a + 1 - v)) * X).map ℤ₍₂₎.subtype =
      C (u₀ : ℚ) + C ((2 : ℚ) ^ (a + 1 - v)) * X := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, map_intCast, map_pow, map_ofNat]
  have hmap₂ : (C ((2 ^ (i + 1 - v) * j : ℤ) : ℤ₍₂₎)).map ℤ₍₂₎.subtype =
      C ((2 : ℚ) ^ (i + 1 - v) * j) := by
    rw [Polynomial.map_C, map_intCast]
    push_cast
    rfl
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, hmap₁, hmap₂,
    map_localKernel ht hd, map_localKernel ht hd₀]
  set Y : ℚ[X] := C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X
  -- Multiply both sides by `2 ^ v`, which turns the linear factors into `Y - d` and `Y - d₀`.
  have h1 : (2 : ℚ) ^ v * u₀ = t - d₀ := by exact_mod_cast htd.symm
  have h2 : (2 : ℚ) ^ v * 2 ^ (a + 1 - v) = 2 ^ (a + 1) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  have h3 : (2 : ℚ) ^ v * (2 ^ (i + 1 - v) * j) = d - d₀ := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact_mod_cast (sub_eq_of_eq_add' hdd).symm
  have hYd : C ((2 : ℚ) ^ v) * (C (u₀ : ℚ) + C (2 ^ (a + 1 - v)) * X -
      C (2 ^ (i + 1 - v) * (j : ℚ))) = Y - C (d : ℚ) := by
    rw [mul_sub, mul_add, ← C_mul, ← mul_assoc, ← C_mul, ← C_mul, h1, h2, h3]
    simp only [Y, C_sub]
    ring
  have hYd₀ : C ((2 : ℚ) ^ v) * (C (u₀ : ℚ) + C (2 ^ (a + 1 - v)) * X) = Y - C (d₀ : ℚ) := by
    rw [mul_add, ← C_mul, ← mul_assoc, ← C_mul, h1, h2]
    simp only [Y, C_sub]
    ring
  have hcomp : ∀ e ∈ cauchyGrid (2 ^ a),
      (cauchyKernel (2 ^ a) e).comp Y * (Y - C (e : ℚ)) =
        (C ((Lagrange.nodal ((cauchyGrid (2 ^ a)).erase 0) (Int.cast : ℤ → ℚ)).eval 0)⁻¹ *
          Lagrange.nodal (cauchyGrid (2 ^ a)) (Int.cast : ℤ → ℚ)).comp Y := by
    intro e he
    rw [← cauchyKernel_mul_X_sub he, mul_comp, sub_comp, X_comp, C_comp]
  have h2v : C ((2 : ℚ) ^ v) ≠ 0 := C_ne_zero.mpr (pow_ne_zero _ two_ne_zero)
  refine mul_left_cancel₀ h2v ?_
  rw [mul_left_comm, hYd, mul_left_comm, hYd₀, hcomp d hd, hcomp d₀ hd₀]

/-! ### Values in a ring where `2` is nilpotent -/

variable {R : Type*} [CommRing R]

/-- The value `W_d(t + α ζ)` of the Cauchy kernel at `T = t + α ζ`, `α = 2 ^ (a + 1)`, in a ring `R`
receiving `ℤ_(2)` through `κ`. -/
@[expose] noncomputable def kernelValue (κ : ℤ₍₂₎ →+* R) (ζ : R) (a : ℕ) (t d : ℤ) : R :=
  (localKernel a t d).eval₂ κ ζ

/-- The *cross ratio* `ρ = 2 ^ (i + 1) / (T - d₀)` at `T = t + α ζ`: with `t - d₀ = 2 ^ v u₀`, `u₀`
odd, it is `2 ^ (i + 1 - v)` times the inverse of `u₀ + 2 ^ (a + 1 - v) ζ`. -/
@[expose] noncomputable def crossRatio (a i : ℕ) (t d₀ : ℤ) (ζ : R) : R :=
  2 ^ (i + 1 - padicValInt 2 (t - d₀)) *
    Ring.inverse ((((t - d₀) / 2 ^ padicValInt 2 (t - d₀) : ℤ) : R) +
      2 ^ (a + 1 - padicValInt 2 (t - d₀)) * ζ)

/-- An integer not divisible by `2 ^ (i + 1)` is `2 ^ v` times an odd integer, with `v ≤ i`:
`v` is its `2`-adic valuation. -/
private theorem two_adic_split {n : ℤ} {i : ℕ} (hn : ¬ (2 : ℤ) ^ (i + 1) ∣ n) :
    padicValInt 2 n ≤ i ∧ Odd (n / 2 ^ padicValInt 2 n) ∧
      n = 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hdvd : (2 : ℤ) ^ padicValInt 2 n ∣ n := by exact_mod_cast padicValInt_dvd (p := 2) n
  have hsplit := (Int.mul_ediv_cancel' hdvd).symm
  refine ⟨?_, ?_, hsplit⟩
  · by_contra h
    exact hn (by exact_mod_cast (padicValInt_dvd_iff (p := 2) (i + 1) n).mpr (Or.inr (by omega)))
  · rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    rintro ⟨c, hc⟩
    have : (2 : ℤ) ^ (padicValInt 2 n + 1) ∣ n := ⟨c, by
      calc n = 2 ^ padicValInt 2 n * (n / 2 ^ padicValInt 2 n) := hsplit
        _ = 2 ^ padicValInt 2 n * (2 * c) := by rw [hc]
        _ = 2 ^ (padicValInt 2 n + 1) * c := by ring⟩
    have h := (padicValInt_dvd_iff (p := 2) (padicValInt 2 n + 1) n).mp (by exact_mod_cast this)
    omega

/-- In a ring where `2` is nilpotent, `1 + 2 x` is a unit. -/
private theorem isUnit_one_add_two_mul {p : ℕ} (hp : (2 : R) ^ p = 0) (x : R) :
    IsUnit (1 + 2 * x) :=
  IsNilpotent.isUnit_one_add ⟨p, by rw [mul_pow, hp, zero_mul]⟩

/-- **The geometric expansion (D.12).** Let `2 ^ p = 0` in `R`, and let `d₀` and
`d = d₀ + 2 ^ (i + 1) j` be grid points of `2 ^ a` slots with `2 ^ (i + 1) ∤ t - d₀` and `i ≤ a`.
Then
`W_d(T) = ∑_{b < p} W_{d₀}(T) ρ ^ b j ^ b` at `T = t + α ζ`, with `ρ = crossRatio a i t d₀ ζ`. -/
theorem kernelValue_eq_sum (κ : ℤ₍₂₎ →+* R) (ζ : R) {p a i : ℕ} (hp : (2 : R) ^ p = 0)
    {t d₀ d j : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hd₀ : d₀ ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) (hdd : d = d₀ + 2 ^ (i + 1) * j)
    (hcross : ¬ (2 : ℤ) ^ (i + 1) ∣ t - d₀) (hia : i ≤ a) :
    kernelValue κ ζ a t d =
      ∑ b ∈ range p, kernelValue κ ζ a t d₀ * crossRatio a i t d₀ ζ ^ b * (j : R) ^ b := by
  obtain ⟨hvi, hodd, hsplit⟩ := two_adic_split hcross
  set v := padicValInt 2 (t - d₀)
  set u₀ := (t - d₀) / 2 ^ v
  have h : kernelValue κ ζ a t d * ((u₀ : R) + 2 ^ (a + 1 - v) * ζ - 2 ^ (i + 1 - v) * j) =
      kernelValue κ ζ a t d₀ * ((u₀ : R) + 2 ^ (a + 1 - v) * ζ) := by
    have h := congrArg (eval₂ κ ζ) (localKernel_mul_eq ht hd₀ hd hdd hsplit hvi hia)
    simp only [eval₂_mul, eval₂_sub, eval₂_add, eval₂_C, eval₂_X] at h
    simp only [map_intCast, map_pow, map_ofNat] at h
    push_cast at h
    exact h
  -- The unit `U = u₀ + 2 ^ (a + 1 - v) ζ`.
  set U : R := (u₀ : R) + 2 ^ (a + 1 - v) * ζ
  have hU : IsUnit U := by
    obtain ⟨c, hc⟩ := hodd
    have : U = 1 + 2 * ((c : R) + 2 ^ (a - v) * ζ) := by
      simp only [U, hc]
      rw [show a + 1 - v = a - v + 1 by omega, pow_succ]
      push_cast
      ring
    rw [this]
    exact isUnit_one_add_two_mul hp _
  set ρ := crossRatio a i t d₀ ζ
  have hρ : ρ = 2 ^ (i + 1 - v) * Ring.inverse U := rfl
  have hUρ : U * ρ = 2 ^ (i + 1 - v) := by
    rw [hρ, mul_left_comm, Ring.mul_inverse_cancel U hU, mul_one]
  -- Cancel `U`: `W_d (1 - ρ j) = W_{d₀}`.
  have hcancel : kernelValue κ ζ a t d * (1 - ρ * j) = kernelValue κ ζ a t d₀ := by
    have h' : kernelValue κ ζ a t d * (1 - ρ * j) * U = kernelValue κ ζ a t d₀ * U := by
      linear_combination h - (kernelValue κ ζ a t d * j) * hUρ
    exact hU.mul_right_cancel h'
  -- The geometric series inverts `1 - ρ j`, as `(ρ j) ^ p = 0`.
  have hnil : (ρ * j) ^ p = 0 := by
    have : ρ = 2 * (2 ^ (i - v) * Ring.inverse U) := by
      rw [hρ, show i + 1 - v = i - v + 1 by omega, pow_succ]
      ring
    rw [this, mul_assoc, mul_pow, hp, zero_mul]
  have hgeom := mul_neg_geom_sum (ρ * (j : R)) p
  rw [hnil, sub_zero] at hgeom
  calc kernelValue κ ζ a t d
      = kernelValue κ ζ a t d * ((1 - ρ * j) * ∑ b ∈ range p, (ρ * (j : R)) ^ b) := by
        rw [hgeom, mul_one]
    _ = kernelValue κ ζ a t d₀ * ∑ b ∈ range p, (ρ * (j : R)) ^ b := by rw [← mul_assoc, hcancel]
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [mul_pow, mul_assoc]

/-- **The coefficients of (D.12) have weight `b + 1`.** When `d₀ ≠ t`, the coefficient
`W_{d₀}(T) ρ ^ b` of `j ^ b` is divisible by `2 ^ (b + 1)`. -/
theorem two_pow_dvd_kernelValue_mul_crossRatio_pow (κ : ℤ₍₂₎ →+* R) (ζ : R) {a i : ℕ}
    {t d₀ : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hd₀ : d₀ ∈ cauchyGrid (2 ^ a))
    (hcross : ¬ (2 : ℤ) ^ (i + 1) ∣ t - d₀) (b : ℕ) :
    (2 : R) ^ (b + 1) ∣ kernelValue κ ζ a t d₀ * crossRatio a i t d₀ ζ ^ b := by
  have hd₀t : d₀ ≠ t := by rintro rfl; exact hcross (by rw [sub_self]; exact dvd_zero _)
  obtain ⟨Q, hQ⟩ := exists_localKernel_eq_two_mul ht hd₀ hd₀t
  have hvi := (two_adic_split hcross).1
  have hk : kernelValue κ ζ a t d₀ = 2 * Q.eval₂ κ ζ := by
    rw [kernelValue, hQ, eval₂_mul, eval₂_C, map_ofNat]
  have hρ : crossRatio a i t d₀ ζ = 2 * (2 ^ (i - padicValInt 2 (t - d₀)) *
      Ring.inverse ((((t - d₀) / 2 ^ padicValInt 2 (t - d₀) : ℤ) : R) +
        2 ^ (a + 1 - padicValInt 2 (t - d₀)) * ζ)) := by
    rw [crossRatio, show i + 1 - padicValInt 2 (t - d₀) = i - padicValInt 2 (t - d₀) + 1 by
      omega, pow_succ]
    ring
  rw [hk, hρ, mul_pow, pow_succ']
  exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)

/-! ### The modes of a packing -/

/-- A row and a column slot with the same binary digit `i`, at a grid point `t` of valuation `i`:
`t - (y₀ - x)` is not divisible by `2 ^ (i + 1)`, for the residue `y₀ < 2 ^ (i + 1)` of the column
slot. (Otherwise `y₀ ≡ x + 2 ^ i` modulo `2 ^ (i + 1)`, which flips digit `i`.) -/
theorem not_dvd_sub_sub_of_testBit_eq {t : ℤ} {i x y₀ : ℕ} (hti : (2 : ℤ) ^ i ∣ t)
    (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (hy₀ : y₀ < 2 ^ (i + 1)) (hbit : x.testBit i = y₀.testBit i) :
    ¬ (2 : ℤ) ^ (i + 1) ∣ t - ((y₀ : ℤ) - x) := by
  rintro ⟨n, hn⟩
  obtain ⟨m, rfl⟩ := hti
  have hm : ¬ (2 : ℤ) ∣ m := fun ⟨c, hc⟩ => hti' ⟨c, by rw [hc, pow_succ]; ring⟩
  obtain ⟨c, rfl⟩ : ∃ c, m = 2 * c + 1 := ⟨m / 2, by omega⟩
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] at hbit
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ i = K := ⟨_, rfl⟩
  have hKpos : 0 < K := hK ▸ by positivity
  have hpow : (2 : ℤ) ^ i = K := by exact_mod_cast hK
  have hpow' : (2 : ℤ) ^ (i + 1) = 2 * K := by rw [pow_succ, hpow, mul_comm]
  have hy₀' : y₀ < K * 2 := by rw [← hK, ← pow_succ]; exact hy₀
  rw [hK] at hbit
  rw [hpow', hpow] at hn
  -- Digit `i` of both is `h`; write `x = K (2 q + h) + lx` and `y₀ = K h + ly`.
  have hy₀K : y₀ / K < 2 := Nat.div_lt_of_lt_mul hy₀'
  have hh : x / K % 2 = y₀ / K := by
    have h1 := Nat.mod_lt (x / K) two_pos
    have h2 : y₀ / K % 2 = y₀ / K := Nat.mod_eq_of_lt hy₀K
    by_cases hx1 : x / K % 2 = 1
    · have := hbit.mp hx1
      omega
    · have := mt hbit.mpr hx1
      omega
  have hx := Nat.div_add_mod x K
  have hx2 := Nat.div_add_mod (x / K) 2
  have hy := Nat.div_add_mod y₀ K
  have hlx := Nat.mod_lt x hKpos
  have hly := Nat.mod_lt y₀ hKpos
  obtain ⟨lx, hlxd⟩ : ∃ lx, x % K = lx := ⟨_, rfl⟩
  obtain ⟨ly, hlyd⟩ : ∃ ly, y₀ % K = ly := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, x / K / 2 = q := ⟨_, rfl⟩
  obtain ⟨h, hhd⟩ : ∃ h, y₀ / K = h := ⟨_, rfl⟩
  rw [hlxd] at hx hlx
  rw [hlyd] at hy hly
  rw [hqd, hh, hhd] at hx2
  rw [hhd] at hy
  rw [← hx2] at hx
  have hxZ : (x : ℤ) = K * (2 * q + h) + lx := by exact_mod_cast hx.symm
  have hyZ : (y₀ : ℤ) = K * h + ly := by exact_mod_cast hy.symm
  have hlx' : (lx : ℤ) < K := by exact_mod_cast hlx
  have hly' : (ly : ℤ) < K := by exact_mod_cast hly
  have hK' : (0 : ℤ) < K := by exact_mod_cast hKpos
  have hlx0 : (0 : ℤ) ≤ lx := Int.natCast_nonneg lx
  have hly0 : (0 : ℤ) ≤ ly := Int.natCast_nonneg ly
  -- Then `0 < K + lx - ly < 2 K` would be a multiple of `2 K`.
  rw [hxZ, hyZ] at hn
  have hw : (K : ℤ) + lx - ly = 2 * K * (n - c - q) := by linear_combination hn
  rcases le_or_gt (n - c - q) 0 with h0 | h0
  · have : (2 * K : ℤ) * (n - c - q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    linarith
  · have : (2 * K : ℤ) * 1 ≤ 2 * K * (n - c - q) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    linarith

namespace TensorNetwork

variable {V E G P : Type*}

/-- The Cauchy matrix of a packing at `T = t + α ζ`, `α = 2 ^ (a + 1)`: between two edges of the
same packet, the Cauchy kernel at the difference of their slots, and zero between packets (the
manuscript's (D.7) at `T`). -/
@[expose] noncomputable def cauchyValueMatrix [DecidableEq P] (κ : ℤ₍₂₎ →+* R) (ζ : R) (a : ℕ)
    (t : ℤ) (packet : E → P) (slot : E → ℕ) : Matrix E E R :=
  fun e e' => if packet e = packet e' then kernelValue κ ζ a t ((slot e' : ℤ) - slot e) else 0

section Modes

variable [Fintype E] [Fintype P] [DecidableEq G] [DecidableEq P] {N : TensorNetwork R Bool V E}
  {group : V → G} {packet : E → P} {slot : E → ℕ} {sym : P → G × G} {i : ℕ}

omit [CommRing R] [Fintype E] [Fintype P] [DecidableEq G] [DecidableEq P] in
private theorem group_src_eq
    (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
      if (slot e).testBit i then (sym (packet e)).swap else sym (packet e)) (e : E) :
    group (N.src e) = if (slot e).testBit i then (sym (packet e)).2 else (sym (packet e)).1 := by
  have h := congrArg Prod.fst (horient e)
  split_ifs at h ⊢ <;> exact h

omit [CommRing R] [Fintype E] [Fintype P] [DecidableEq G] [DecidableEq P] in
private theorem group_tgt_eq
    (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
      if (slot e).testBit i then (sym (packet e)).swap else sym (packet e)) (e : E) :
    group (N.tgt e) = if (slot e).testBit i then (sym (packet e)).1 else (sym (packet e)).2 := by
  have h := congrArg Prod.snd (horient e)
  split_ifs at h ⊢ <;> exact h

/-- The coefficient of the mode `Z = (q, y₀, b)` in the row form of `e`: for a row of the packet
`q` whose two groups differ, with digit `i` of its slot `x` equal to that of `y₀`, it is
`W_{y₀ - x}(T) ρ ^ b`, the coefficient of `j ^ b` in (D.12); otherwise zero. -/
@[expose] noncomputable def cauchyModeCoeff (κ : ℤ₍₂₎ →+* R) (ζ : R) (a i : ℕ) (t : ℤ)
    (packet : E → P) (slot : E → ℕ) (sym : P → G × G) {p : ℕ} (e : E)
    (Z : P × Fin (2 ^ (i + 1)) × Fin p) : R :=
  if packet e = Z.1 ∧ (sym Z.1).1 ≠ (sym Z.1).2 ∧ (slot e).testBit i = (Z.2.1 : ℕ).testBit i then
    kernelValue κ ζ a t ((Z.2.1 : ℤ) - slot e) *
      crossRatio a i t ((Z.2.1 : ℤ) - slot e) ζ ^ (Z.2.2 : ℕ)
  else 0

/-- The form of the mode `Z = (q, y₀, b)` at the column `e'`: for a column of the packet `q` whose
two groups differ, in slot `y = y₀ + 2 ^ (i + 1) j` of the tile `y₀`, it is `j ^ b`; otherwise
zero. -/
@[expose] noncomputable def cauchyModeForm (R : Type*) [CommRing R] (i : ℕ) (packet : E → P)
    (slot : E → ℕ) (sym : P → G × G) {p : ℕ} (Z : P × Fin (2 ^ (i + 1)) × Fin p) (e' : E) : R :=
  if packet e' = Z.1 ∧ (sym Z.1).1 ≠ (sym Z.1).2 ∧ slot e' % 2 ^ (i + 1) = Z.2.1 then
    ((slot e' / 2 ^ (i + 1) : ℕ) : R) ^ (Z.2.2 : ℕ)
  else 0

omit [Fintype E] in
/-- The Cauchy matrix at `T` is its local part plus its modes: the geometric expansion (D.12) on
the crossing entries. -/
private theorem cauchyValueMatrix_eq_add_sum
    (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
      if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
    {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
    (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
    (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (e e' : E) :
    cauchyValueMatrix κ ζ a t packet slot e e' =
      (if group (N.tgt e') = group (N.src e) then cauchyValueMatrix κ ζ a t packet slot e e'
        else 0) +
        ∑ Z : P × Fin (2 ^ (i + 1)) × Fin p,
          cauchyModeCoeff κ ζ a i t packet slot sym e Z *
            cauchyModeForm R i packet slot sym Z e' := by
  have hsrc := group_src_eq horient e
  have htgt := group_tgt_eq horient e'
  -- A mode term is nonzero only at the packet of both edges, when its groups differ, at the digit
  -- of `e` and the tile of `e'`.
  have hterm : ∀ Z : P × Fin (2 ^ (i + 1)) × Fin p,
      cauchyModeCoeff κ ζ a i t packet slot sym e Z * cauchyModeForm R i packet slot sym Z e' ≠ 0 →
        packet e = Z.1 ∧ packet e' = Z.1 ∧ (sym Z.1).1 ≠ (sym Z.1).2 ∧
          (slot e).testBit i = (Z.2.1 : ℕ).testBit i ∧ slot e' % 2 ^ (i + 1) = Z.2.1 := by
    intro Z hZ
    have hc := left_ne_zero_of_mul hZ
    have hf := right_ne_zero_of_mul hZ
    unfold cauchyModeCoeff at hc
    unfold cauchyModeForm at hf
    obtain ⟨h1, h2, h3⟩ := not_not.mp fun h => hc (ite_eq_right h)
    obtain ⟨h4, -, h5⟩ := not_not.mp fun h => hf (ite_eq_right h)
    exact ⟨h1, h4, h2, h3, h5⟩
  have hbit' : ∀ y₀ : ℕ, slot e' % 2 ^ (i + 1) = y₀ → (slot e').testBit i = y₀.testBit i := by
    rintro y₀ rfl
    rw [Nat.testBit_mod_two_pow]
    simp
  by_cases hloc : group (N.tgt e') = group (N.src e)
  · -- Local entries: no mode term survives.
    rw [ite_eq_left hloc, left_eq_add]
    refine sum_eq_zero fun Z _ => by_contra fun hZ => ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := hterm Z hZ
    have hb : (slot e').testBit i = (slot e).testBit i := (hbit' _ h5).trans h4.symm
    rw [htgt, hsrc, hb, h2, h1] at hloc
    split_ifs at hloc
    exacts [h3 hloc, h3 hloc.symm]
  rw [ite_eq_right hloc, zero_add]
  by_cases hq : packet e = packet e'
  · -- Crossing entries of one packet: the geometric expansion.
    have hσ : (sym (packet e)).1 ≠ (sym (packet e)).2 := by
      intro hσ
      apply hloc
      rw [htgt, hsrc, ← hq]
      split_ifs <;> simp only [hσ]
    have hb : (slot e).testBit i = (slot e').testBit i := by
      by_contra hb
      apply hloc
      rw [htgt, hsrc, ← hq]
      rcases Bool.eq_false_or_eq_true ((slot e).testBit i) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true ((slot e').testBit i) with h2 | h2 <;>
        simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false, not_true_eq_false] at hb ⊢
    have h2a : 2 ^ (i + 1) ≤ 2 ^ a := Nat.pow_le_pow_right two_pos hia
    have hy₀lt : slot e' % 2 ^ (i + 1) < 2 ^ (i + 1) := Nat.mod_lt _ (by positivity)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin (2 ^ (i + 1)), (y₀ : ℕ) = slot e' % 2 ^ (i + 1) :=
      ⟨⟨_, hy₀lt⟩, rfl⟩
    have hx' : ((slot e : ℕ) : ℤ) < 2 ^ a := by exact_mod_cast hslot e
    have hy₀' : ((y₀ : ℕ) : ℤ) < 2 ^ a := by
      rw [hy₀]
      exact_mod_cast lt_of_lt_of_le hy₀lt h2a
    have hy' : ((slot e' : ℕ) : ℤ) < 2 ^ a := by exact_mod_cast hslot e'
    rw [Fintype.sum_prod_type, sum_eq_single (packet e), Fintype.sum_prod_type,
      sum_eq_single y₀]
    · have hcoef : ∀ b : Fin p,
          cauchyModeCoeff κ ζ a i t packet slot sym e (packet e, y₀, b) *
              cauchyModeForm R i packet slot sym (packet e, y₀, b) e' =
            kernelValue κ ζ a t ((y₀ : ℕ) - slot e) *
                crossRatio a i t ((y₀ : ℕ) - slot e) ζ ^ (b : ℕ) *
              (((slot e' / 2 ^ (i + 1) : ℕ) : ℤ) : R) ^ (b : ℕ) := by
        intro b
        unfold cauchyModeCoeff cauchyModeForm
        rw [ite_eq_left ⟨rfl, hσ, hb.trans (hbit' _ hy₀.symm)⟩,
          ite_eq_left ⟨hq.symm, hσ, hy₀.symm⟩, Int.cast_natCast]
      simp only [hcoef]
      rw [Fin.sum_univ_eq_sum_range (fun b => kernelValue κ ζ a t ((y₀ : ℕ) - slot e) *
          crossRatio a i t ((y₀ : ℕ) - slot e) ζ ^ b *
            (((slot e' / 2 ^ (i + 1) : ℕ) : ℤ) : R) ^ b) p,
        cauchyValueMatrix, ite_eq_left hq]
      have hdiv := Nat.mod_add_div (slot e') (2 ^ (i + 1))
      refine kernelValue_eq_sum κ ζ hp ht ?_ ?_ ?_
        (not_dvd_sub_sub_of_testBit_eq hti hti' y₀.isLt (hb.trans (hbit' _ hy₀.symm))) hia.le
      · rw [mem_cauchyGrid]
        push_cast
        constructor <;> omega
      · rw [mem_cauchyGrid]
        push_cast
        constructor <;> omega
      · have : ((slot e' : ℕ) : ℤ) = ((y₀ : ℕ) : ℤ) +
            2 ^ (i + 1) * ((slot e' / 2 ^ (i + 1) : ℕ) : ℤ) := by
          rw [hy₀]
          exact_mod_cast hdiv.symm
        rw [this]
        ring
    · intro y₀' _ hne
      refine sum_eq_zero fun b _ => by_contra fun hZ => hne ?_
      exact Fin.ext ((hterm _ hZ).2.2.2.2.symm.trans hy₀.symm)
    · exact fun h => absurd (mem_univ _) h
    · intro q' _ hne
      refine sum_eq_zero fun Z _ => by_contra fun hZ => hne ?_
      exact (hterm _ hZ).1.symm
    · exact fun h => absurd (mem_univ _) h
  · -- Different packets: the entry and every mode term vanish.
    rw [cauchyValueMatrix, ite_eq_right hq]
    refine (sum_eq_zero fun Z _ => by_contra fun hZ => hq ?_).symm
    obtain ⟨h1, h2, -⟩ := hterm Z hZ
    exact h1.trans h2.symm

/-- **The modes of the Cauchy matrix (§D.4.5).** Let the edges of `N` be packed into packets of
`2 ^ a` slots, with an orientation in coordinate `i < a`: each packet `q` has a pair of groups
`sym q`, and an edge in slot `x` of `q` runs from group `(sym q).1` to group `(sym q).2` when digit
`i` of `x` is `0`, and the other way when it is `1`. Let `t` be a grid point of valuation `i` and
`2 ^ p = 0` in `R`. Then the Cauchy matrix at `T = t + α ζ` has a mode splitting: entries between
the same group are local, and for each packet `q` whose two groups differ, each *tile* `y₀` of the
column slots `y ≡ y₀ (mod 2 ^ (i + 1))` and each `b < p` there is a mode with coefficient
`W_{y₀ - x}(T) ρ ^ b` in the row form of slot `x` (`cauchyModeCoeff`) and form `∑ j ^ b X_y` over
the columns `y = y₀ + 2 ^ (i + 1) j` of the tile (`cauchyModeForm`): the manuscript's (D.12). -/
noncomputable def cauchyModeSplitting (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false)
    (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
      if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
    {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
    (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
    (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) :
    N.ModeSplitting (cauchyValueMatrix κ ζ a t packet slot) G P
      (P × Fin (2 ^ (i + 1)) × Fin p) where
  side := side
  group := group
  packet := packet
  localPart e e' :=
    if group (N.tgt e') = group (N.src e) then cauchyValueMatrix κ ζ a t packet slot e e' else 0
  modePacket Z := Z.1
  source Z := if (Z.2.1 : ℕ).testBit i then (sym Z.1).1 else (sym Z.1).2
  target Z := if (Z.2.1 : ℕ).testBit i then (sym Z.1).2 else (sym Z.1).1
  coeff := cauchyModeCoeff κ ζ a i t packet slot sym
  form := cauchyModeForm R i packet slot sym
  side_src := hsrc
  side_tgt := htgt
  apply_eq := cauchyValueMatrix_eq_add_sum horient hslot hia κ ζ hp ht hti hti'
  localPart_ne_zero e e' h := by
    simp only [ne_eq, ite_eq_right_iff, not_forall, cauchyValueMatrix] at h
    obtain ⟨hg, hq, -⟩ := h
    exact ⟨hq.symm, hg⟩
  coeff_ne_zero e Z h := by
    unfold cauchyModeCoeff at h
    obtain ⟨hq, -, hb⟩ := not_not.mp fun hc => h (ite_eq_right hc)
    refine ⟨hq.symm, ?_⟩
    rw [group_src_eq horient e, hb, hq]
  form_ne_zero Z e h := by
    unfold cauchyModeForm at h
    obtain ⟨hq, -, hy⟩ := not_not.mp fun hc => h (ite_eq_right hc)
    refine ⟨hq.symm, ?_⟩
    have hb : (slot e).testBit i = (Z.2.1 : ℕ).testBit i := by
      rw [← hy, Nat.testBit_mod_two_pow]
      simp
    rw [group_tgt_eq horient e, hb, hq]

omit [Fintype E] [Fintype P] in
/-- **The modes have weight `b + 1`:** the coefficient of the mode `(q, y₀, b)` is divisible by
`2 ^ (b + 1)`, so the child identity (D.16) applies with these weights. -/
theorem two_pow_dvd_cauchyModeCoeff {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a)
    (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (e : E)
    (Z : P × Fin (2 ^ (i + 1)) × Fin p) :
    (2 : R) ^ ((Z.2.2 : ℕ) + 1) ∣ cauchyModeCoeff κ ζ a i t packet slot sym e Z := by
  unfold cauchyModeCoeff
  split_ifs with h
  · have h2a : 2 ^ (i + 1) ≤ 2 ^ a := Nat.pow_le_pow_right two_pos hia
    have hx : ((slot e : ℕ) : ℤ) < 2 ^ a := by exact_mod_cast hslot e
    have hy₀ : ((Z.2.1 : ℕ) : ℤ) < 2 ^ a := by exact_mod_cast lt_of_lt_of_le Z.2.1.isLt h2a
    refine two_pow_dvd_kernelValue_mul_crossRatio_pow κ ζ ht ?_
      (not_dvd_sub_sub_of_testBit_eq hti hti' Z.2.1.isLt h.2.2) _
    rw [mem_cauchyGrid]
    push_cast
    constructor <;> omega
  · exact dvd_zero _

/-- **The child identity for the Cauchy matrix** ((D.16) of [OpenAI2026ETH] at an interpolation
value). With `2 ^ p = 0` in `R`, the deformed contraction along the Cauchy matrix of a packing at
`T = t + α ζ`, for a grid point `t` of valuation `i`, is the sum over the exponent tuples of total
weight `∑ (b + 1) β_{(q, y₀, b)} < p` of the products over the groups of the contractions of the
children of `cauchyModeSplitting`. -/
theorem deformedContraction_cauchyValueMatrix_eq_sum [Fintype V] [DecidableEq V] [Fintype G]
    [DecidableEq E] (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false)
    (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
      if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
    {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
    (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
    (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) :
    N.deformedContraction side (cauchyValueMatrix κ ζ a t packet slot) =
      ∑ β ∈ modeBudget (fun Z : P × Fin (2 ^ (i + 1)) × Fin p => (Z.2.2 : ℕ) + 1) p,
        ∏ g, ((cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').child β
          g).contraction :=
  (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti
    hti').deformedContraction_eq_sum_prod_contraction_child _ (fun _ => Nat.succ_pos _) hp
    fun e Z => two_pow_dvd_cauchyModeCoeff hslot hia κ ζ ht hti hti' e Z

end Modes

end TensorNetwork

end Cslib.Circuits.Frontier
