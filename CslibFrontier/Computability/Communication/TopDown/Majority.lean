/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CslibFrontier.Foundations.BooleanAnalysis.Fibers
public import CslibFrontier.Computability.Communication.TopDown.Rectangle
public import CslibFrontier.Computability.Communication.TopDown.Adversary
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

/-!
# Top-down lower bounds for majority

The two Hamming layers on either side of the threshold of strict majority (`strictMajority`, which
is false at a tie) have entropy deficit `O(log n)`, and from every point at least half of the
coordinates lead to the other layer by one flip. This gives bilateral density limits at rate
`16 / n`, so Korten's adversary applies, and the logarithmic initial deficit keeps the exponent
`1 / (d - 1)`: no protocol with `d` messages of `ε n ^ (1 / (d - 1))` bits solves the
Karchmer–Wigderson game of strict majority on `n` bits for large `n`
(`not_solvesKW_strictMajority`). This extends the parity argument of Korten
[Korten2026].

## Main definitions

* `Cslib.Communication.strictMajorityDeficitBound`: the deficit of the starting layers.

## Main results

* `Cslib.Communication.RoundProtocol.not_solvesKW_strictMajority`: the bound with explicit
  constants.
* `Cslib.Communication.not_solvesKW_strictMajority`: the communication lower bound for
  strict majority.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

/-! ### Hamming layers and the initial majority deficit

Strict majority (`strictMajority`) is false at a tie, so the two layers at weights `n / 2` and
`n / 2 + 1` straddle its threshold.
-/

namespace Cslib.Communication

open BitString
open Finset
open Filter Asymptotics

/-- A common deficit and density-limit bound for the two majority boundary layers.
The logarithmic term bounds their entropy deficit; `128` bounds the mask size. -/
noncomputable def strictMajorityDeficitBound (n : ℕ) : ℝ :=
  128 + Real.logb 2 (2 * ((n : ℝ) + 1))

/-! ### Absorbing the logarithmic initial deficit

The middle-layer deficit bound is little-o of every positive power of `n`.
Thus replacing the parity deficit `1` with this logarithmic bound preserves
the exponent `1/(d-1)` in a `d`-round communication lower bound.
-/

private theorem strictMajorityDeficitBound_eventually_le {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → strictMajorityDeficitBound n ≤ c * (n : ℝ) ^ r := by
  have hlog := isLittleO_log_rpow_atTop hr
  have hconst : (fun _ : ℝ => (130 : ℝ)) =o[atTop] (fun x : ℝ => x ^ r) :=
    Real.isLittleO_const_log_atTop.trans hlog
  have hs := hconst.add (hlog.const_mul_left (Real.log 2)⁻¹)
  have he : ∀ᶠ n : ℕ in atTop,
      ‖(130 : ℝ) + (Real.log 2)⁻¹ * Real.log n‖ ≤ c * ‖(n : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually (hs.def hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hbound := hN n (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbound
  have hl : Real.logb 2 (2 * ((n : ℝ) + 1)) ≤ Real.logb 2 (4 * (n : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hfour : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_mul (by norm_num) (ne_of_gt hnpos), hfour] at hl
  have heq : Real.logb 2 (n : ℝ) = (Real.log 2)⁻¹ * Real.log n := by
    rw [Real.logb, div_eq_mul_inv, mul_comm]
  rw [heq] at hl
  unfold strictMajorityDeficitBound
  exact (show 128 + Real.logb 2 (2 * ((n : ℝ) + 1)) ≤
    130 + (Real.log 2)⁻¹ * Real.log n by linarith).trans ((le_abs_self _).trans hbound)

private theorem finite_budget_with_deficit_of_cost {n d : ℕ} (hd : 0 < d) {m k : ℝ}
    (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hcost : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d)))
    (hkcost : k ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d))) :
    64 * (32768 * (194 : ℝ) ^ d * (m + k)) ^ d ≤ (n : ℝ) := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d
  let r : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  have hm' : m * (128 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hcost
  have hk' : k * (128 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hkcost
  have hstep : C * (m + k) ≤ r / 64 := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ C * (m + k) by positivity) hstep d
  have hrootpow : r ^ d = (n : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)
  rw [div_pow, hrootpow] at hpow
  have hden : (64 : ℝ) ≤ (64 : ℝ) ^ d := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 64) (Nat.succ_le_of_lt hd)
  have hh : 64 * ((n : ℝ) / (64 : ℝ) ^ d) ≤ n := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hden)]
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hh

/-! ### The two layers around the threshold of strict majority

The largest binomial coefficient is at least `2^n/(n+1)`, and its upper
neighbor is at least half as large. This gives a logarithmic entropy
deficit for both boundary layers, for even as well as odd input sizes.
-/

private theorem le_strictMajorityDeficitBound (n : ℕ) : 128 ≤ strictMajorityDeficitBound n := by
  have h := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold strictMajorityDeficitBound
  linarith

private theorem two_pow_le_succ_mul_choose_half (n : ℕ) : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := by
  calc
    _ = ∑ r ∈ range (n + 1), n.choose r := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _r ∈ range (n + 1), n.choose (n / 2) :=
      sum_le_sum (fun r _ => Nat.choose_le_middle r n)
    _ = _ := by simp

private theorem choose_half_le_two_mul_choose_half_succ {n : ℕ} (hn : 2 ≤ n) :
    n.choose (n / 2) ≤ 2 * n.choose (n / 2 + 1) := by
  have he := Nat.choose_succ_right_eq n (n / 2)
  have hh := Nat.mul_le_mul_left (n.choose (n / 2 + 1))
    (show n / 2 + 1 ≤ 2 * (n - n / 2) by omega)
  have hpos : 0 < n - n / 2 := by omega
  nlinarith

private theorem weightLayer_deficit {n r : ℕ} (hr : r ≤ n)
    (hcard : 2 ^ n ≤ (2 * (n + 1)) * n.choose r) :
    (weightLayer n r).Nonempty ∧
      uniformDeficit (weightLayer n r) ≤ strictMajorityDeficitBound n := by
  have hne : (weightLayer n r).Nonempty := weightLayer_nonempty hr
  refine ⟨hne, ?_⟩
  have hd : uniformDeficit (weightLayer n r) ≤ Real.logb 2 (2 * ((n : ℝ) + 1)) := by
    apply (uniformDeficit_le_iff hne).mpr
    simp only [Fintype.card_fin, card_weightLayer]
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast,
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (by simpa only [mul_comm] using hcard : 2 ^ n ≤ n.choose r * (2 * (n + 1)))
  unfold strictMajorityDeficitBound
  linarith

private theorem majority_layers_deficit {n : ℕ} (hn : 2 ≤ n) :
    ((weightLayer n (n / 2)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2)) ≤ strictMajorityDeficitBound n) ∧
    ((weightLayer n (n / 2 + 1)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2 + 1)) ≤ strictMajorityDeficitBound n) := by
  have hmid := two_pow_le_succ_mul_choose_half n
  have hnext := Nat.mul_le_mul_left (n + 1) (choose_half_le_two_mul_choose_half_succ hn)
  constructor
  · exact weightLayer_deficit (by omega) (by nlinarith)
  · exact weightLayer_deficit (by omega) (by nlinarith)

/-! ### Density limits from many single-bit neighbors

At rate `16/n`, a mask hits any set of at least `n/2` coordinates with
probability at least `8/9`. Its expected size is `16`, so the probability
that it has more than `128` coordinates is at most `1/8`. A selected
single-bit neighbor then gives fiber density at least `2^(-128)`.

Applying this to the two middle Hamming layers initializes Korten's top-down adversary for strict
majority, extending his initialization for parity [Korten2026].
-/

private theorem coordinateDensity_of_neighbor {n : ℕ} (X : Finset (Fin n → Bool))
    (P x : Fin n → Bool) (i : Fin n) (hi : P i = true)
    (hx : Function.update x i (!x i) ∈ X) (hsmall : weight P ≤ 128) :
    (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x := by
  have he : completePattern P x (fun j => Function.update x i (!x i) j) =
      Function.update x i (!x i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [completePattern, hi]
    · by_cases hP : P j = true <;> simp [completePattern, hP, Function.update_of_ne hj]
  have hne : (coordinateFiber X P x).Nonempty := by
    refine ⟨(fun j => Function.update x i (!x i) j), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rwa [he]
  have hc : (1 : ℝ) ≤ (coordinateFiber X P x).card := by
    exact_mod_cast card_pos.mpr hne
  unfold coordinateDensity
  rw [Fintype.card_subtype]
  change (2 : ℝ) ^ (-(128 : ℝ)) ≤
    (coordinateFiber X P x).card / (2 : ℝ) ^ weight P
  apply (le_div_iff₀ (by positivity)).mpr
  have hpw := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsmall
  calc
    _ ≤ (2 : ℝ) ^ (-(128 : ℝ)) * (2 : ℝ) ^ (128 : ℕ) := by gcongr
    _ = 1 := by rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]; norm_num
    _ ≤ _ := hc

private theorem isDensityLimit_of_many_neighbors {n : ℕ} (hn : 16 ≤ n)
    (X : Finset (Fin n → Bool)) (x s : Fin n → Bool) (hs : n ≤ 2 * weight s)
    (hneighbor : ∀ i, s i = true → Function.update x i (!x i) ∈ X) :
    IsDensityLimit X (16 / n) 128 x := by
  let p : ℝ := 16 / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  have hmean : (n : ℝ) * p = 16 := by dsimp [p]; field_simp
  have hs' : (n : ℝ) ≤ 2 * weight s := by exact_mod_cast hs
  have hhit : 8 ≤ (weight s : ℝ) * p := by
    nlinarith [mul_le_mul_of_nonneg_right hs' hp]
  have hnone : (1 - p) ^ weight s ≤ 1 / 9 := by
    have hh := Real.one_sub_pow_mul_one_add_mul_le_one hp' (weight s)
    have hnon : 0 ≤ (1 - p) ^ weight s := pow_nonneg (sub_nonneg.mpr hp') _
    nlinarith
  have hpoint (P : Fin n → Bool) :
      (if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) -
        (1 / 128) * (weight P : ℝ) ≤
      if (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x then 1 else 0 := by
    by_cases hhit : ∃ i, s i = true ∧ P i = true
    · rw [ite_eq_left hhit]
      by_cases hsmall : weight P ≤ 128
      · obtain ⟨i, hi, hPi⟩ := hhit
        rw [ite_eq_left
          (coordinateDensity_of_neighbor X P x i hPi (hneighbor i hi) hsmall)]
        have := Nat.cast_nonneg (α := ℝ) (weight P)
        linarith
      · have hlarge : (128 : ℝ) < weight P := by exact_mod_cast (Nat.lt_of_not_ge hsmall)
        split_ifs <;> linarith
    · rw [ite_eq_right hhit]
      have := Nat.cast_nonneg (α := ℝ) (weight P)
      split_ifs <;> linarith
  have hh := bernoulliAverage_mono hp hp' hpoint
  have hhits : bernoulliAverage p (fun P : Fin n → Bool =>
      if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) = 1 - (1 - p) ^ weight s := by
    convert bernoulliAverage_hits p s
  rw [bernoulliAverage_sub, hhits, bernoulliAverage_const_mul, bernoulliAverage_weight,
    Fintype.card_fin, hmean] at hh
  unfold IsDensityLimit
  change (3 : ℝ) / 4 ≤ bernoulliAverage p _
  linarith

private theorem majority_layers_limits {n : ℕ} (hn : 16 ≤ n) :
    (∀ x ∈ weightLayer n (n / 2),
      IsDensityLimit (weightLayer n (n / 2 + 1)) (16 / n) (strictMajorityDeficitBound n) x) ∧
    (∀ y ∈ weightLayer n (n / 2 + 1),
      IsDensityLimit (weightLayer n (n / 2)) (16 / n) (strictMajorityDeficitBound n) y) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (16 : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  constructor
  · intro x hx
    have hx' : weight x = n / 2 := (mem_filter.mp hx).2
    have hl := isDensityLimit_of_many_neighbors hn (weightLayer n (n / 2 + 1)) x
      (fun i => !x i) (by rw [weight_not, Fintype.card_fin, hx']; omega) ?_
    · exact hl.mono_right (by positivity) hp (le_strictMajorityDeficitBound n)
    intro i hi
    have hi' : x i = false := by simpa using hi
    simp only [mem_weightLayer, hi', Bool.not_false]
    rw [weight_update_true hi', hx']
  · intro y hy
    have hy' : weight y = n / 2 + 1 := (mem_filter.mp hy).2
    have hl := isDensityLimit_of_many_neighbors hn (weightLayer n (n / 2)) y
      y (by rw [hy']; omega) ?_
    · exact hl.mono_right (by positivity) hp (le_strictMajorityDeficitBound n)
    intro i hi
    have hc := weight_update_false hi
    simp only [mem_weightLayer, hi, Bool.not_true]
    omega

/-! ### The communication lower bound for strict majority

The bilateral density adversary starts from the two layers around the threshold, and the power-law
budget absorbs their logarithmic entropy deficit. This extends the argument of Korten
[Korten2026], whose Theorem 3 is the case of parity.
-/

namespace RoundProtocol

variable {M : Type*} [Fintype M]

/-- The bound for strict majority with explicit constants: no protocol with `d + 1` messages of at
most `m` bits solves the Karchmer–Wigderson game of strict majority on `n` bits when
`64 (32768 · 194 ^ d (m + strictMajorityDeficitBound n)) ^ d ≤ n`. -/
theorem not_solvesKW_strictMajority {n d : ℕ} (P : KWRoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 64 * (32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW (strictMajority n) := by
  have hk := le_strictMajorityDeficitBound n
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hn64 : (64 : ℝ) ≤ n := by nlinarith [one_le_pow₀ (n := d) hC]
  have hn16 : 16 ≤ n := by exact_mod_cast (show (16 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have ⟨hX, hY⟩ := majority_layers_deficit (show 2 ≤ n by omega)
  have ⟨hleft, hright⟩ := majority_layers_limits hn16
  have hbudget :
      (32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n)) ^ d * (16 / n) ≤ 1 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
  intro hsol
  apply P.not_solves_bilateral_density hM hm (by linarith)
    (show (0 : ℝ) < 16 / n by positivity) hX.1 hY.1 hX.2 hY.2 hleft hright hbudget
  intro x hx y hy
  apply hsol x y
  · apply strictMajority_eq_false_iff.mpr
    exact ((mem_filter.mp hx).2).le
  · apply strictMajority_eq_true_iff.mpr
    have := (mem_filter.mp hy).2
    change weight y = n / 2 + 1 at this
    omega

end RoundProtocol

universe u in
/-- **The communication lower bound for strict majority**, extending
[Korten, Theorem 3][Korten2026]: for every `d ≥ 2` there is `ε > 0` such that, for all large `n`, no
protocol with `d` messages from an alphabet of at most `2 ^ (ε n ^ (1 / (d - 1)))` letters solves
the Karchmer–Wigderson game of strict majority on `n` bits. -/
theorem not_solvesKW_strictMajority (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ {M : Type u} [Fintype M],
      (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) →
        ∀ P : KWRoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (strictMajority n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show rounds ≠ 0 by omega)
  have hd : 0 < d := by omega
  let ε : ℝ := 1 / (128 * (32768 * (194 : ℝ) ^ d))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := strictMajorityDeficitBound_eventually_le
    (show (0 : ℝ) < (d : ℝ)⁻¹ by positivity) hε
  refine ⟨ε, hε, N, fun n hn M _ hM P => ?_⟩
  have hm : 0 ≤ ε * (n : ℝ) ^ (((d + 1 - 1 : ℕ) : ℝ)⁻¹) := by positivity
  apply P.not_solvesKW_strictMajority hM hm
  have hk := le_strictMajorityDeficitBound n
  apply finite_budget_with_deficit_of_cost hd hm (by linarith)
  · simp only [ε, Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  · simpa only [ε, one_div, div_eq_mul_inv, mul_comm, one_mul] using hN n hn

end Cslib.Communication
