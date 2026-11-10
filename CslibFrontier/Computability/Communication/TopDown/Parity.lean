/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.TopDown.Adversary
public import CslibFrontier.Foundations.Data.BitString.Parity
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Korten's communication lower bound for parity

The two parity classes of `n` bits have deficit one, and every nonempty fiber of either is half
full, since flipping a free coordinate exchanges them; a mask of rate `4 / n` is nonempty with
probability at least `3 / 4`, so each class consists of `(4 / n, 1)`-limits of the other. Korten's
adversary then shows that no protocol with `d + 1` messages of `m` bits solves the
Karchmer–Wigderson game of parity once `16 (32768 · 194 ^ d (m + 1)) ^ d ≤ n`
(`RoundProtocol.not_solvesKW_parity`), so protocols with `d` messages need
`Ω(n ^ (1 / (d - 1)))` bits [Korten, Theorem 3][Korten2026]
(`not_solvesKW_parity`).

## Main results

* `Cslib.Communication.RoundProtocol.not_solvesKW_parity`: the bound with explicit
  constants.
* `Cslib.Communication.not_solvesKW_parity`: Korten's lower bound.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Communication

open Cslib.BitString Finset

/-- The parity classes are nonempty of deficit at most one. -/
private theorem parity_class_nonempty_deficit {n : ℕ} (hn : 0 < n) (b : Bool) :
    (univ.filter fun x : Fin n → Bool => parity n x = b).Nonempty ∧
      uniformDeficit (univ.filter fun x : Fin n → Bool => parity n x = b) ≤ 1 := by
  let X := univ.filter (fun x : Fin n → Bool => parity n x = b)
  have hbal := expect_ite_eq_one_half_of_update_not (parity n) ⟨0, hn⟩
    (fun x => parity_update_not x _) b
  have hratio : (X.card : ℝ) / (2 : ℝ) ^ n = 1 / 2 := by
    simpa only [Fintype.expect_eq_sum_div_card, sum_boole, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hbal
  have hcard : (X.card : ℝ) = (2 : ℝ) ^ n / 2 := by
    have he := (div_eq_iff (show (2 : ℝ) ^ n ≠ 0 by positivity)).mp hratio
    linarith
  have hX : X.Nonempty := by
    apply card_pos.mp
    have he : (0 : ℝ) < X.card := by rw [hcard]; positivity
    exact_mod_cast he
  refine ⟨hX, (uniformDeficit_le_iff hX).mpr ?_⟩
  simp only [Fintype.card_fin]
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one, ← hcard]

/-- The points are density limits of a parity class when masks are nonempty with probability at
least `3 / 4`. -/
theorem parity_isDensityLimit {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hsmall : (1 - p) ^ n ≤ 1 / 4) (b : Bool) (x : Fin n → Bool) :
    IsDensityLimit (univ.filter fun z : Fin n → Bool => parity n z = b) p 1 x := by
  have hpoint (P : Fin n → Bool) : (if ∃ i, P i = true then (1 : ℝ) else 0) ≤
      if (2 : ℝ) ^ (-(1 : ℝ)) ≤ coordinateDensity
        (univ.filter fun z : Fin n → Bool => parity n z = b) P x then 1 else 0 := by
    by_cases h : ∃ i, P i = true
    · obtain ⟨i, hi⟩ := h
      have hd := coordinateDensity_filter_eq_one_half_of_update_not (parity n) i
        (fun x => parity_update_not x i) P x hi b
      simp only [hd]
      norm_num [show ∃ j, P j = true from ⟨i, hi⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  have hh := bernoulliAverage_mono hp hp' hpoint
  have he : bernoulliAverage p
      (fun P : Fin n → Bool => if ∃ i, P i = true then (1 : ℝ) else 0) =
        1 - (1 - p) ^ n := by
    convert bernoulliAverage_nonempty (ι := Fin n) p using 1
    · congr 1
      funext P
      split_ifs <;> rfl
    · simp
  rw [he] at hh
  have hg := (show (3 : ℝ) / 4 ≤ 1 - (1 - p) ^ n by linarith).trans hh
  unfold IsDensityLimit
  convert hg using 1

private theorem parity_isDensityLimit_four_div {n : ℕ} (hn : 4 ≤ n) (b : Bool)
    (x : Fin n → Bool) :
    IsDensityLimit (univ.filter fun z : Fin n → Bool => parity n z = b)
      (4 / n) 1 x := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp1 : (4 : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr hn4
  apply parity_isDensityLimit (by positivity) hp1 _ b x
  have ht := Real.one_sub_pow_mul_one_add_mul_le_one hp1 n
  have hnp : (n : ℝ) * (4 / n) = 4 := by field_simp
  rw [hnp] at ht
  nlinarith

namespace RoundProtocol

variable {M : Type*} [Fintype M]

private theorem not_solves_parity_classes {n d : ℕ} (P : KWRoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ)) :
    ¬ P.Solves DiffersAt ↑(univ.filter fun x => parity n x = false)
      ↑(univ.filter fun y => parity n y = true) := by
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + 1) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hn16 : (16 : ℝ) ≤ n := by nlinarith [one_le_pow₀ (n := d) hC]
  have hn4 : 4 ≤ n := by exact_mod_cast (show (4 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have hX := parity_class_nonempty_deficit (show 0 < n by omega) false
  have hY := parity_class_nonempty_deficit (show 0 < n by omega) true
  apply P.not_solves_bilateral_density hM hm le_rfl (show (0 : ℝ) < 4 / n by positivity)
    hX.1 hY.1 hX.2 hY.2
    (fun x _ => parity_isDensityLimit_four_div hn4 true x)
    (fun y _ => parity_isDensityLimit_four_div hn4 false y)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnpos).mpr
  nlinarith

/-- **Korten's bound for parity, with explicit constants**: no protocol with `d + 1` messages of at
most `m` bits solves the Karchmer–Wigderson game of parity on `n` bits when
`16 (32768 · 194 ^ d (m + 1)) ^ d ≤ n`. -/
theorem not_solvesKW_parity {n d : ℕ} (P : KWRoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW (parity n) := by
  intro hsol
  apply not_solves_parity_classes P hM hm hsize
  intro x hx y hy
  exact hsol x y (mem_filter.mp hx).2 (mem_filter.mp hy).2

end RoundProtocol

private theorem finite_budget_of_cost {n d : ℕ} (hd : 0 < d)
    (hlarge : (32 * (32768 * 194 ^ d)) ^ d ≤ n) {m : ℝ} (hm : 0 ≤ m)
    (hcost : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (32 * (32768 * (194 : ℝ) ^ d))) :
    16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ) := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d
  let r : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlarge' : (32 * C) ^ d ≤ (n : ℝ) := by
    dsimp [C]
    exact_mod_cast hlarge
  have hroot : 32 * C ≤ r := by
    have hh := Real.rpow_le_rpow (show 0 ≤ (32 * C) ^ d by positivity)
      hlarge' (show 0 ≤ (d : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) (Nat.ne_of_gt hd)] at hh
    exact hh
  have hcost' : m * (32 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hcost
  have hstep : C * (m + 1) ≤ r / 16 := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ C * (m + 1) by positivity) hstep d
  have hrootpow : r ^ d = (n : ℝ) := Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)
  rw [div_pow, hrootpow] at hpow
  have hden : (16 : ℝ) ≤ (16 : ℝ) ^ d := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) (Nat.succ_le_of_lt hd)
  have hh : 16 * ((n : ℝ) / (16 : ℝ) ^ d) ≤ n := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hden)]
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hh

universe u in
/-- **Korten's communication lower bound for parity** [Korten, Theorem 3][Korten2026]: for every
`d ≥ 2` there is `ε > 0` such that, for all large `n`, no protocol with `d` messages from an
alphabet of at most `2 ^ (ε n ^ (1 / (d - 1)))` letters solves the Karchmer–Wigderson game of parity
on `n` bits. -/
theorem not_solvesKW_parity (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ {M : Type u} [Fintype M],
      (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) →
        ∀ P : KWRoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (parity n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show rounds ≠ 0 by omega)
  have hd : 0 < d := by omega
  let ε : ℝ := 1 / (32 * (32768 * (194 : ℝ) ^ d))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, (32 * (32768 * 194 ^ d)) ^ d, fun n hn M _ hM P => ?_⟩
  have hm : 0 ≤ ε * (n : ℝ) ^ (((d + 1 - 1 : ℕ) : ℝ)⁻¹) := by positivity
  have hc : ε * (n : ℝ) ^ (((d + 1 - 1 : ℕ) : ℝ)⁻¹) ≤
      (n : ℝ) ^ ((d : ℝ)⁻¹) / (32 * (32768 * (194 : ℝ) ^ d)) := by
    simp only [ε, Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  exact P.not_solvesKW_parity hM hm (finite_budget_of_cost hd hn hm hc)

end Cslib.Communication
