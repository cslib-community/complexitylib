/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The ML-DSA high-order/low-order decomposition

ML-DSA (CRYSTALS-Dilithium, [DucasEtAl2018], standardized as [NISTFIPS204]) rounds each
coefficient `r ∈ ℤ_q` of a commitment to its *high bits* and keeps the *low bits* as a small
remainder. For an even rounding range `α = 2 γ₂` dividing `q - 1`, the `Decompose` algorithm of
[NISTFIPS204] takes the canonical representative `r⁺ ∈ [0, q)` of `r`, the centered remainder
`r₀ = r⁺ mod± α ∈ (-γ₂, γ₂]`, and returns `(r₁, r₀) = ((r⁺ - r₀) / α, r₀)`, except in the one
*wrap-around* case `r⁺ - r₀ = q - 1`, where it returns `(0, r₀ - 1)`. `HighBits` and `LowBits` are
the two components.

This module defines the decomposition on `ZMod q` and proves the facts that the scheme and its
security reduction use:

* the decomposition reconstructs its input: `r = r₁ · α + r₀` in `ℤ_q`
  (`intCast_highBits_mul_add_lowBits`);
* the low bits are short, `|r₀| ≤ γ₂` (`abs_lowBits_le`), and the high bits lie in
  `[0, (q - 1) / α)` (`highBits_nonneg`, `highBits_lt`);
* the decomposition is *unique*: any representation `r = a · α + b` with `0 ≤ a < (q - 1) / α` and
  `-γ₂ < b ≤ γ₂` is the decomposition of `r` (`decompose_intCast_mul_add`). The wrap-around rule
  is exactly what makes this hold at `a = 0`, `b < 0`.
  The wrap-around case can itself output `r₀ = -γ₂`, outside this box (e.g. `r = q - γ₂` when
  `2 γ₂ ∣ q - 1`), so the decomposition does not always land in the box;
* consequently, adding a short `s` with `‖s‖_∞ ≤ β` to a value whose low bits satisfy
  `|r₀| < γ₂ - β` leaves the high bits unchanged and shifts the low bits by `s`
  (`highBits_add_of_abs_lowBits_lt`, `lowBits_add_of_abs_lowBits_lt`). This is the rounding fact
  behind ML-DSA's correctness: the verifier recomputes `HighBits(A y - c s₂)`, which equals the
  signer's `HighBits(A y)`.

## Main definitions

* `Cslib.Crypto.MLDSA.decompose`, `Cslib.Crypto.MLDSA.highBits`, `Cslib.Crypto.MLDSA.lowBits`:
  the `Decompose`, `HighBits` and `LowBits` algorithms of [NISTFIPS204].

## Main results

* `Cslib.Crypto.MLDSA.intCast_highBits_mul_add_lowBits`: reconstruction.
* `Cslib.Crypto.MLDSA.abs_lowBits_le`, `Cslib.Crypto.MLDSA.highBits_nonneg`,
  `Cslib.Crypto.MLDSA.highBits_lt`: ranges of the two components.
* `Cslib.Crypto.MLDSA.decompose_intCast_mul_add`: uniqueness of the decomposition.
* `Cslib.Crypto.MLDSA.highBits_add_of_abs_lowBits_lt`,
  `Cslib.Crypto.MLDSA.lowBits_add_of_abs_lowBits_lt`: stability of the high bits under short
  perturbations.

## References

* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

public section

namespace Cslib.Crypto.MLDSA

/-- The `Decompose` algorithm of [NISTFIPS204] with rounding range `2 γ₂`: from the canonical
representative `r⁺ = r.val ∈ [0, q)` and the centered remainder `r₀ = r⁺ mod± 2 γ₂`, return
`((r⁺ - r₀) / (2 γ₂), r₀)`, or `(0, r₀ - 1)` in the wrap-around case `r⁺ - r₀ = q - 1`. -/
def decompose (q γ₂ : ℕ) (r : ZMod q) : ℤ × ℤ :=
  let r₀ : ℤ := ((r.val : ℤ) : ZMod (2 * γ₂)).valMinAbs
  if (r.val : ℤ) - r₀ = (q : ℤ) - 1 then (0, r₀ - 1)
  else (((r.val : ℤ) - r₀) / (2 * γ₂ : ℕ), r₀)

/-- `HighBits` of [NISTFIPS204]: the first component of `decompose`. -/
def highBits (q γ₂ : ℕ) (r : ZMod q) : ℤ := (decompose q γ₂ r).1

/-- `LowBits` of [NISTFIPS204]: the second component of `decompose`. -/
def lowBits (q γ₂ : ℕ) (r : ZMod q) : ℤ := (decompose q γ₂ r).2

variable {q γ₂ : ℕ}

/-- The centered remainder used by `decompose`. -/
private abbrev centeredRem (q γ₂ : ℕ) (r : ZMod q) : ℤ :=
  ((r.val : ℤ) : ZMod (2 * γ₂)).valMinAbs

private theorem centeredRem_bounds (hγ : 0 < γ₂) (r : ZMod q) :
    -(γ₂ : ℤ) < centeredRem q γ₂ r ∧ centeredRem q γ₂ r ≤ γ₂ := by
  have : NeZero (2 * γ₂) := ⟨by omega⟩
  have h : centeredRem q γ₂ r * 2 ∈ Set.Ioc (-((2 * γ₂ : ℕ) : ℤ)) ((2 * γ₂ : ℕ) : ℤ) :=
    ZMod.valMinAbs_mem_Ioc _
  simp only [Set.mem_Ioc] at h
  push_cast at h
  constructor <;> linarith [h.1, h.2]

private theorem dvd_sub_centeredRem (r : ZMod q) :
    ((2 * γ₂ : ℕ) : ℤ) ∣ (r.val : ℤ) - centeredRem q γ₂ r :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (ZMod.coe_valMinAbs _)

/-- Unfolding `highBits` and `lowBits` in the wrap-around case. -/
private theorem decompose_of_wrap {r : ZMod q}
    (h : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1) :
    decompose q γ₂ r = (0, centeredRem q γ₂ r - 1) := by
  simp only [decompose, centeredRem] at h ⊢
  simp only [h, ↓reduceIte]

/-- Unfolding `highBits` and `lowBits` away from the wrap-around case. -/
private theorem decompose_of_not_wrap {r : ZMod q}
    (h : (r.val : ℤ) - centeredRem q γ₂ r ≠ (q : ℤ) - 1) :
    decompose q γ₂ r =
      (((r.val : ℤ) - centeredRem q γ₂ r) / (2 * γ₂ : ℕ), centeredRem q γ₂ r) := by
  simp only [decompose, centeredRem] at h ⊢
  simp only [h, ↓reduceIte]

/-- The low bits are short: `|LowBits r| ≤ γ₂`. -/
theorem abs_lowBits_le (hγ : 0 < γ₂) (r : ZMod q) : |lowBits q γ₂ r| ≤ γ₂ := by
  obtain ⟨h₁, h₂⟩ := centeredRem_bounds (q := q) hγ r
  by_cases h : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1
  · rw [lowBits, decompose_of_wrap h, abs_le]
    constructor <;> linarith
  · rw [lowBits, decompose_of_not_wrap h, abs_le]
    constructor <;> linarith

/-- **Reconstruction.** `r = HighBits r · 2 γ₂ + LowBits r` in `ℤ_q`. -/
theorem intCast_highBits_mul_add_lowBits [NeZero q] (r : ZMod q) :
    ((highBits q γ₂ r * (2 * γ₂ : ℕ) + lowBits q γ₂ r : ℤ) : ZMod q) = r := by
  by_cases h : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1
  · rw [highBits, lowBits, decompose_of_wrap h]
    have : (0 : ℤ) * (2 * γ₂ : ℕ) + (centeredRem q γ₂ r - 1) = (r.val : ℤ) - q := by linarith
    rw [this]
    push_cast
    simp
  · rw [highBits, lowBits, decompose_of_not_wrap h, Int.ediv_mul_cancel (dvd_sub_centeredRem r),
      sub_add_cancel]
    simp

/-- In a valid ML-DSA modulus, `q = (q - 1) / (2 γ₂) · 2 γ₂ + 1`. -/
private theorem q_eq (hdvd : 2 * γ₂ ∣ q - 1) [NeZero q] :
    (q : ℤ) = (((q - 1) / (2 * γ₂) : ℕ) : ℤ) * (2 * γ₂ : ℕ) + 1 := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hmul : (q - 1) / (2 * γ₂) * (2 * γ₂) = q - 1 := Nat.div_mul_cancel hdvd
  generalize (q - 1) / (2 * γ₂) = m at hmul ⊢
  have : q = m * (2 * γ₂) + 1 := by omega
  exact_mod_cast this

/-- The high bits are nonnegative. -/
theorem highBits_nonneg (hγ : 0 < γ₂) (r : ZMod q) : 0 ≤ highBits q γ₂ r := by
  by_cases h : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1
  · rw [highBits, decompose_of_wrap h]
  · rw [highBits, decompose_of_not_wrap h]
    obtain ⟨k, hk⟩ := dvd_sub_centeredRem (γ₂ := γ₂) r
    obtain ⟨h₁, h₂⟩ := centeredRem_bounds (q := q) hγ r
    have hv : (0 : ℤ) ≤ r.val := Int.natCast_nonneg _
    rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
    push_cast at hk
    by_contra hneg
    have hk1 : k ≤ -1 := by omega
    have : (2 * γ₂ : ℤ) * k ≤ -(2 * γ₂) := by nlinarith
    linarith

/-- When `2 γ₂ ∣ q - 1`, the high bits lie below `(q - 1) / (2 γ₂)`, the number of high-order
buckets. -/
theorem highBits_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 1 < q) (r : ZMod q) :
    highBits q γ₂ r < ((q - 1) / (2 * γ₂) : ℕ) := by
  have : NeZero q := ⟨by omega⟩
  set m : ℕ := (q - 1) / (2 * γ₂) with hm
  have hqm := q_eq (q := q) (γ₂ := γ₂) hdvd
  rw [← hm] at hqm
  have hrv : (r.val : ℤ) < q := by exact_mod_cast ZMod.val_lt r
  obtain ⟨h₁, h₂⟩ := centeredRem_bounds (q := q) hγ r
  by_cases h : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1
  · rw [highBits, decompose_of_wrap h]
    -- `q - 1 = m · 2 γ₂ ≥ 1` forces `m ≥ 1`.
    have hq' : (1 : ℤ) < q := by exact_mod_cast hq
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0] at hqm
      push_cast at hqm
      linarith
    · change (0 : ℤ) < m
      exact_mod_cast hm0
  · rw [highBits, decompose_of_not_wrap h]
    obtain ⟨k, hk⟩ := dvd_sub_centeredRem (γ₂ := γ₂) r
    rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
    push_cast at hk hqm
    -- `r⁺ - r₀ = 2 γ₂ k ≤ q - 2 + γ₂ < q - 1 + 2 γ₂`, so `k ≤ m`, and `k ≠ m` off the wrap case.
    have hk_le : k ≤ m := by
      by_contra hlt
      have hlt : (m : ℤ) + 1 ≤ k := by omega
      have : (2 * γ₂ : ℤ) * (m + 1) ≤ 2 * γ₂ * k := by
        apply mul_le_mul_of_nonneg_left (by omega) (by positivity)
      nlinarith
    have hk_ne : k ≠ m := by
      intro hkm
      apply h
      rw [hk, hkm, hqm]
      ring
    omega

/-- The centered remainder of `r` is the unique `c ∈ (-γ₂, γ₂]` congruent to `r⁺` modulo
`2 γ₂`. -/
private theorem centeredRem_eq (hγ : 0 < γ₂) {r : ZMod q} {c : ℤ} (hc₁ : -(γ₂ : ℤ) < c)
    (hc₂ : c ≤ γ₂) (hdc : ((2 * γ₂ : ℕ) : ℤ) ∣ (r.val : ℤ) - c) : centeredRem q γ₂ r = c := by
  have : NeZero (2 * γ₂) := ⟨by omega⟩
  rw [centeredRem, ZMod.valMinAbs_spec]
  refine ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hdc
    exact ⟨-t, by linarith⟩
  · simp only [Set.mem_Ioc]
    push_cast
    constructor <;> linarith

/-- **Uniqueness of the decomposition.** If `r = a · 2 γ₂ + b` in `ℤ_q` with
`0 ≤ a < (q - 1) / (2 γ₂)` and `-γ₂ < b ≤ γ₂`, then `decompose r = (a, b)`. -/
theorem decompose_intCast_mul_add (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) [NeZero q] {a b : ℤ}
    (ha₀ : 0 ≤ a) (ha : a < ((q - 1) / (2 * γ₂) : ℕ)) (hb₁ : -(γ₂ : ℤ) < b) (hb₂ : b ≤ γ₂) :
    decompose q γ₂ ((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q) = (a, b) := by
  set m : ℕ := (q - 1) / (2 * γ₂) with hm
  have hqm : (q : ℤ) = m * (2 * γ₂) + 1 := by
    have := q_eq (q := q) (γ₂ := γ₂) hdvd
    rw [← hm] at this
    push_cast at this
    exact this
  have hcast : ((2 * γ₂ : ℕ) : ℤ) = 2 * (γ₂ : ℤ) := by push_cast; ring
  have hγ' : (1 : ℤ) ≤ γ₂ := by exact_mod_cast hγ
  have hm1 : (1 : ℤ) ≤ m := by omega
  have hmγ : (2 * γ₂ : ℤ) ≤ m * (2 * γ₂) := by nlinarith
  have hval : ((((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q).val : ℕ) : ℤ) =
      (a * (2 * γ₂ : ℕ) + b) % q := ZMod.val_intCast _
  generalize ((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q) = r at hval ⊢
  rw [hcast] at hval
  by_cases hx : 0 ≤ a * (2 * γ₂) + b
  · -- No reduction modulo `q` happens, and this is not the wrap-around case.
    have hxq : a * (2 * γ₂) + b < q := by
      have : a * (2 * γ₂) ≤ (m - 1) * (2 * γ₂) :=
        mul_le_mul_of_nonneg_right (by omega) (by positivity)
      linarith
    have hv : (r.val : ℤ) = a * (2 * γ₂) + b := by
      rw [hval, Int.emod_eq_of_lt hx hxq]
    have hr₀ : centeredRem q γ₂ r = b :=
      centeredRem_eq hγ hb₁ hb₂ ⟨a, by rw [hv, hcast]; ring⟩
    have hnw : (r.val : ℤ) - centeredRem q γ₂ r ≠ (q : ℤ) - 1 := by
      intro heq
      have h2 : a * (2 * γ₂) = m * (2 * γ₂) := by linarith
      have := mul_right_cancel₀ (by positivity : (2 * γ₂ : ℤ) ≠ 0) h2
      omega
    rw [decompose_of_not_wrap hnw, hr₀, hv, add_sub_cancel_right, hcast,
      Int.mul_ediv_cancel _ (by positivity)]
  · -- Then `a = 0` and `-γ₂ < b < 0`: the representative is `q + b`, the wrap-around case.
    have hx : a * (2 * γ₂) + b < 0 := lt_of_not_ge hx
    have ha0 : a = 0 := by
      by_contra hne
      have h1 : 1 ≤ a := by omega
      have : (2 * γ₂ : ℤ) ≤ a * (2 * γ₂) := by nlinarith
      linarith
    subst ha0
    have hb0 : b < 0 := by linarith
    have hv : (r.val : ℤ) = b + q := by
      have hmod : (b + q) % q = b % q := by simp
      rw [hval, zero_mul, zero_add, ← hmod]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    have hr₀ : centeredRem q γ₂ r = b + 1 :=
      centeredRem_eq hγ (by linarith) (by linarith) ⟨m, by rw [hv, hqm, hcast]; ring⟩
    have hw : (r.val : ℤ) - centeredRem q γ₂ r = (q : ℤ) - 1 := by
      rw [hv, hr₀]
      ring
    rw [decompose_of_wrap hw, hr₀, add_sub_cancel_right]

/-- Uniqueness, high-bits component. -/
theorem highBits_intCast_mul_add (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) [NeZero q] {a b : ℤ}
    (ha₀ : 0 ≤ a) (ha : a < ((q - 1) / (2 * γ₂) : ℕ)) (hb₁ : -(γ₂ : ℤ) < b) (hb₂ : b ≤ γ₂) :
    highBits q γ₂ ((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q) = a := by
  rw [highBits, decompose_intCast_mul_add hγ hdvd ha₀ ha hb₁ hb₂]

/-- Uniqueness, low-bits component. -/
theorem lowBits_intCast_mul_add (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) [NeZero q] {a b : ℤ}
    (ha₀ : 0 ≤ a) (ha : a < ((q - 1) / (2 * γ₂) : ℕ)) (hb₁ : -(γ₂ : ℤ) < b) (hb₂ : b ≤ γ₂) :
    lowBits q γ₂ ((a * (2 * γ₂ : ℕ) + b : ℤ) : ZMod q) = b := by
  rw [lowBits, decompose_intCast_mul_add hγ hdvd ha₀ ha hb₁ hb₂]

/-- A multiple `a · 2 γ₂` of the rounding range with `0 ≤ a < (q - 1) / (2 γ₂)` has high bits
`a`. -/
theorem highBits_intCast_mul (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) [NeZero q] {a : ℤ}
    (ha₀ : 0 ≤ a) (ha : a < ((q - 1) / (2 * γ₂) : ℕ)) :
    highBits q γ₂ ((a * (2 * γ₂ : ℕ) : ℤ) : ZMod q) = a := by
  have := highBits_intCast_mul_add (b := 0) hγ hdvd ha₀ ha (by omega) (by omega)
  rwa [add_zero] at this

/-- Adding a short perturbation to a value with small low bits: the decomposition of `r + s` is
`(HighBits r, LowBits r + s)`, where `s` is read through its centered representative. -/
theorem decompose_add_of_abs_lowBits_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 1 < q)
    {β : ℕ} {r s : ZMod q} (hs : |s.valMinAbs| ≤ β)
    (hr : |lowBits q γ₂ r| < (γ₂ : ℤ) - β) :
    decompose q γ₂ (r + s) = (highBits q γ₂ r, lowBits q γ₂ r + s.valMinAbs) := by
  have : NeZero q := ⟨by omega⟩
  have hsum : r + s =
      ((highBits q γ₂ r * (2 * γ₂ : ℕ) + (lowBits q γ₂ r + s.valMinAbs) : ℤ) : ZMod q) := by
    rw [← add_assoc, Int.cast_add, intCast_highBits_mul_add_lowBits, ZMod.coe_valMinAbs]
  rw [abs_lt] at hr
  rw [abs_le] at hs
  rw [hsum]
  exact decompose_intCast_mul_add hγ hdvd (highBits_nonneg hγ r) (highBits_lt hγ hdvd hq r)
    (by linarith [hr.1, hs.1]) (by linarith [hr.2, hs.2])

/-- **High bits are stable under short perturbations.** If `|s| ≤ β` and
`|LowBits r| < γ₂ - β`, then `HighBits (r + s) = HighBits r`. -/
theorem highBits_add_of_abs_lowBits_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 1 < q)
    {β : ℕ} {r s : ZMod q} (hs : |s.valMinAbs| ≤ β)
    (hr : |lowBits q γ₂ r| < (γ₂ : ℤ) - β) :
    highBits q γ₂ (r + s) = highBits q γ₂ r := by
  rw [highBits, decompose_add_of_abs_lowBits_lt hγ hdvd hq hs hr]

/-- Under the hypotheses of `highBits_add_of_abs_lowBits_lt`, the low bits shift by `s`. -/
theorem lowBits_add_of_abs_lowBits_lt (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ q - 1) (hq : 1 < q)
    {β : ℕ} {r s : ZMod q} (hs : |s.valMinAbs| ≤ β)
    (hr : |lowBits q γ₂ r| < (γ₂ : ℤ) - β) :
    lowBits q γ₂ (r + s) = lowBits q γ₂ r + s.valMinAbs := by
  rw [lowBits, decompose_add_of_abs_lowBits_lt hγ hdvd hq hs hr]

end Cslib.Crypto.MLDSA
