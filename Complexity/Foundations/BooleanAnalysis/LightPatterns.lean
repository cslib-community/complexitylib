/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Complexity.Foundations.BooleanAnalysis.HarmonicTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Korten's light-patterns lemma

Let `mass` be a distribution on the points of the cube `ι → Bool` with min-entropy deficit at most
`k`, that is, `mass x ≤ 2 ^ (k - |ι|)`. Select each coordinate independently with rate
`r ≤ 1 / (512 k)`. With probability at least `63 / 64`, at most `2 ^ (|R| - k)` patterns on the
selected coordinates `R` are *light*, of marginal probability at most `2 ^ (-|R| - 2 k - 2)`
[Korten, Lemma 10][Korten2026] (`le_bernoulliAverage_card_coordinateMass_le`).

The proof transfers a lower set of masks from rate `1 / 4` to a small rate `r`: its probability at
rate `r` is at least its probability at rate `1 / 4` to the power `5 r`
(`bernoulliAverage_lowerSet_transfer`). The masks on which the harmonic mean transform of the
density of `mass` is large form such a lower set, of probability at least `2 ^ (-k / 2 - 1)` at
rate `1 / 4` (`le_bernoulliAverage_le_harmonicTransform`), so they have probability at least
`63 / 64` at rate `r` (`le_bernoulliAverage_le_harmonicTransform_of_rpow`). On these masks the
harmonic mean bounds the number of light patterns.

## Main definitions

* `Cslib.BitString.coordinateMass`: the marginal of a distribution on the selected
  coordinates.

## Main results

* `Cslib.BitString.bernoulliAverage_lowerSet_transfer`: transference for lower sets at a
  small rate.
* `Cslib.BitString.le_bernoulliAverage_le_harmonicTransform_of_rpow`: the harmonic mean transform at
  a sparse random set.
* `Cslib.BitString.le_bernoulliAverage_card_coordinateMass_le`: Korten's light-patterns lemma.
* `Cslib.BitString.le_bernoulliAverage_expect_coordinateMarginal_le`: the same, for densities.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open scoped BigOperators
open Finset

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Transference at a small rate -/

/-- **Transference for lower sets** at a small rate `r ≤ 1 / 20`: the probability of a nonempty
lower set at rate `r` is at least its probability at rate `1 / 4` to the power `5 r`, as in the
proof of [Korten, Lemma 10][Korten2026]. Nonemptiness covers `r = 0`, where the right side is
one. -/
theorem bernoulliAverage_lowerSet_transfer {A : Set (ι → Bool)}
    (hA : IsLowerSet A) (hA' : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 20) :
    bernoulliAverage (1 / 4) (A.indicator 1) ^ (5 * r) ≤ bernoulliAverage r (A.indicator 1) := by
  rcases hr.eq_or_lt with rfl | hr
  · obtain ⟨s, hs⟩ := hA'
    have hz : (fun _ => false) ∈ A := hA (fun i => Bool.false_le (s i)) hs
    simp [bernoulliAverage_zero, Set.indicator_of_mem hz]
  let h := ⌊1 / (4 * r)⌋₊
  have hr1 : r ≤ 1 := by linarith
  have hmul : (1 / (4 * r)) * r = 1 / 4 := by field_simp
  have hupper : (h : ℝ) * r ≤ 1 / 4 := by
    have hf := mul_le_mul_of_nonneg_right (Nat.floor_le (show 0 ≤ 1 / (4 * r) by positivity)) hr.le
    rwa [hmul] at hf
  have hlower : 1 ≤ (h : ℝ) * (5 * r) := by
    have hf := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (1 / (4 * r))) hr
    rw [hmul] at hf
    dsimp [h]
    nlinarith
  have hpos : 0 < (h : ℝ) := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (by positivity : 0 ≤ 5 * r)
    linarith
  have hinv : (h : ℝ)⁻¹ ≤ 5 * r := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).mpr (by nlinarith)
  have hbase := bernoulliAverage_indicator_mem_Icc A
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  calc
    _ ≤ bernoulliAverage (1 / 4) (A.indicator 1) ^ (h : ℝ)⁻¹ :=
      Real.rpow_le_rpow_of_exponent_ge' hbase.1 hbase.2 (by positivity) hinv
    _ ≤ _ := by
      apply (Real.rpow_inv_le_iff_of_pos hbase.1
        (bernoulliAverage_indicator_mem_Icc A hr.le hr1).1 hpos).mpr
      rw [Real.rpow_natCast]
      exact bernoulliAverage_lowerSet_pow_le hA hr.le hr1 (by norm_num) h hupper

/-! ### The harmonic mean transform at a sparse random set -/

/-- For `1 ≤ k` and `0 ≤ r ≤ 1 / (512 k)`, `(1 / (2 * √(2 ^ k))) ^ (5 r) ≥ 63 / 64`. -/
private theorem sixtyThree_div_sixtyFour_le_rpow {k r : ℝ} (hk : 1 ≤ k) (hr : 0 ≤ r)
    (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ (1 / (2 * Real.sqrt ((2 : ℝ) ^ k))) ^ (5 * r) := by
  let B : ℝ := (2 : ℝ) ^ k
  let a : ℝ := 1 / (2 * Real.sqrt B)
  have hBp : 0 < B := Real.rpow_pos_of_pos (by norm_num) k
  have ha : 0 < a := by dsimp [a]; positivity
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hrk : r ≤ r * k := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  have hlog : Real.log a = -(k / 2 + 1) * Real.log 2 := by
    dsimp [a, B]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hBp.le,
      Real.log_rpow (by norm_num)]
    ring
  have he := Real.add_one_le_exp (Real.log a * (5 * r))
  rw [← Real.rpow_def_of_pos ha, hlog] at he
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hloss : (k / 2 + 1) * (5 * r) * Real.log 2 ≤ (k / 2 + 1) * (5 * r) :=
    mul_le_of_le_one_right (by positivity) hlog2
  nlinarith

/-- **The harmonic mean transform at a sparse random set**, as in the proof of
[Korten, Lemma 10][Korten2026]: for a density `f` relative to the uniform distribution bounded by
`2 ^ k`, `k ≥ 1`, the transform at a random set of rate `r ≤ 1 / (512 k)` is at least
`1 / (4 · 2 ^ k)` with probability at least `63 / 64`. -/
theorem le_bernoulliAverage_le_harmonicTransform_of_rpow
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1)
    {k r : ℝ} (hk : 1 ≤ k) (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r
      (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0) := by
  let B : ℝ := (2 : ℝ) ^ k
  let a : ℝ := 1 / (2 * Real.sqrt B)
  let A : Set (ι → Bool) := {s | 1 / (4 * B) ≤ harmonicTransform f s}
  have hB : 1 ≤ B := Real.one_le_rpow (by norm_num) (by linarith)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : IsLowerSet A := fun _ _ hst ht => ht.trans (harmonicTransform_antitone hf hst)
  have hA' : A.Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    change 1 / (4 * B) ≤ harmonicTransform f (fun _ => false)
    rw [harmonicTransform_empty, hmean]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr20 : r ≤ 1 / 20 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  have hind : A.indicator 1 =
      fun s => if 1 / (4 * B) ≤ harmonicTransform f s then (1 : ℝ) else 0 := by
    funext s
    by_cases h : 1 / (4 * B) ≤ harmonicTransform f s
    · rw [Set.indicator_of_mem (show s ∈ A from h), ite_eq_left h]
      rfl
    · rw [Set.indicator_of_notMem (show s ∉ A from h), ite_eq_right h]
  have hgood : a ≤ bernoulliAverage (1 / 4) (A.indicator 1) :=
    hind ▸ le_bernoulliAverage_le_harmonicTransform hf hmean hB hbound
  have htransfer := (Real.rpow_le_rpow ha.le hgood (by positivity : 0 ≤ 5 * r)).trans
    (bernoulliAverage_lowerSet_transfer hA hA' hr hr20)
  rw [← hind]
  exact (sixtyThree_div_sixtyFour_le_rpow hk hr hr').trans htransfer

/-- Korten's light-patterns lemma for densities: with probability at least `63 / 64`, the fraction
of patterns of marginal density at most `2 ^ (-2 k - 2)` is at most `2 ^ (-k)`. -/
theorem le_bernoulliAverage_expect_coordinateMarginal_le
    {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k) then 1 else 0) := by
  have ht : (2 : ℝ) ^ (-2 * k - 2) / (1 / (4 * (2 : ℝ) ^ k)) = (2 : ℝ) ^ (-k) := by
    have hfour : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [one_div, div_inv_eq_mul, hfour, ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  refine (le_bernoulliAverage_le_harmonicTransform_of_rpow hf hmean hk hbound hr hr').trans
    (bernoulliAverage_mono hr hr1 fun s => ?_)
  by_cases hs : 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s
  · have hlight := coordinateMarginal_light_fraction_le hf s (by positivity) hs
      (by positivity : 0 ≤ (2 : ℝ) ^ (-2 * k - 2))
    rw [ht] at hlight
    simp only [ite_eq_left hs, ite_eq_left hlight, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> norm_num

/-! ### Marginal probability masses on coordinate patterns

The marginal of a probability mass function on the cube sums its masses over the completions of a
pattern on the selected coordinates. It is the marginal `coordinateMarginal` of the density
relative to the uniform distribution, scaled by the number of patterns. -/

/-- Sum of the masses of all completions of a coordinate pattern. For a
nonnegative mass function summing to one, this is the probability of the pattern. -/
def coordinateMass (mass : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  ∑ rest : {i // selected i ≠ true} → Bool,
    mass (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

/-- Marginalization preserves total probability mass. -/
theorem sum_coordinateMass (mass : (ι → Bool) → ℝ) (s : ι → Bool) :
    (∑ z, coordinateMass mass s z) = ∑ x, mass x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  rw [← e.symm.sum_comp mass, Fintype.sum_prod_type]
  rfl

/-- Marginal masses of a nonnegative mass function are nonnegative. -/
theorem coordinateMass_nonneg {mass : (ι → Bool) → ℝ} (hm : ∀ x, 0 ≤ mass x) (s : ι → Bool)
    (z : {i // s i = true} → Bool) : 0 ≤ coordinateMass mass s z :=
  sum_nonneg fun _ _ => hm _

/-- The marginal mass of a pattern is the marginal of `mass` at the pattern times the number
`2 ^ |{i | s i ≠ true}|` of its completions. -/
theorem coordinateMass_eq_mul_coordinateMarginal (mass : (ι → Bool) → ℝ) (s : ι → Bool)
    (z : {i // s i = true} → Bool) :
    coordinateMass mass s z =
      (2 : ℝ) ^ Fintype.card {i // s i ≠ true} * coordinateMarginal mass s z := by
  rw [coordinateMarginal, Fintype.expect_eq_sum_div_card, coordinateMass]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- Normalizing the input mass by `2^n` normalizes each marginal by `2^|R|`. -/
private theorem coordinateMarginal_normalize (mass : (ι → Bool) → ℝ) (s : ι → Bool)
    (z : {i // s i = true} → Bool) :
    coordinateMarginal (fun x => (2 : ℝ) ^ Fintype.card ι * mass x) s z =
      (2 : ℝ) ^ Fintype.card {i // s i = true} * coordinateMass mass s z := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  have hc : (2 : ℝ) ^ Fintype.card ι =
      (2 : ℝ) ^ Fintype.card {i // s i = true} *
        (Fintype.card ({i // s i ≠ true} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod] at h
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast h
  unfold coordinateMarginal coordinateMass
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hc]
  have hp : (0 : ℝ) < Fintype.card ({i // s i ≠ true} → Bool) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ({i // s i ≠ true} → Bool))
  field_simp

/-! ### Korten's light-patterns lemma -/

/-- Scaling `mass` by `2 ^ |ι|` converts the marginal-density threshold `2 ^ (-2 k - 2)` into the
pattern-mass count bound at threshold `2 ^ (-|s| - 2 k - 2)`. -/
private theorem ite_expect_coordinateMarginal_le_of_normalize (mass : (ι → Bool) → ℝ) (k : ℝ)
    (s : ι → Bool) :
    let f : (ι → Bool) → ℝ := fun x => (2 : ℝ) ^ Fintype.card ι * mass x
    (if (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k) then (1 : ℝ) else 0) ≤
      if ((univ.filter fun z => coordinateMass mass s z ≤
          (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * k - 2)).card : ℝ) ≤
        (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - k) then 1 else 0 := by
  intro f
  let m := Fintype.card {i // s i = true}
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hthreshold : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) =
      (2 : ℝ) ^ (-2 * k - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcount : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ m = (2 : ℝ) ^ ((m : ℝ) - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have he (z : {i // s i = true} → Bool) :
      coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) ↔
        coordinateMass mass s z ≤ (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) := by
    change coordinateMarginal (fun x => (2 : ℝ) ^ Fintype.card ι * mass x) s z ≤ _ ↔ _
    rw [coordinateMarginal_normalize, ← hthreshold]
    exact mul_le_mul_iff_right₀ hp
  have havg : (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then
        (1 : ℝ) else 0) =
      ((univ.filter fun z => coordinateMass mass s z ≤
        (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2)).card : ℝ) / (2 : ℝ) ^ m := by
    simp_rw [he]
    rw [Fintype.expect_eq_sum_div_card]
    simp [m]
  simp only [havg, div_le_iff₀ hp, hcount]
  exact le_rfl

/-- **Korten's light-patterns lemma** [Korten, Lemma 10][Korten2026], with its constants and
pattern count. Nonnegative masses summing to one represent a distribution;
the pointwise bound is min-entropy deficit at most the real parameter `k`. -/
theorem le_bernoulliAverage_card_coordinateMass_le
    {mass : (ι → Bool) → ℝ}
    (hm : ∀ x, 0 ≤ mass x) (hmean : (∑ x, mass x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, mass x ≤ (2 : ℝ) ^ (k - Fintype.card ι))
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if ((univ.filter fun z => coordinateMass mass s z ≤
          (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * k - 2)).card : ℝ) ≤
        (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - k) then 1 else 0) := by
  let f : (ι → Bool) → ℝ := fun x => (2 : ℝ) ^ Fintype.card ι * mass x
  have hf : ∀ x, 0 ≤ f x := fun x => mul_nonneg (by positivity) (hm x)
  have hsum : (𝔼 x, f x) = 1 := by
    dsimp [f]
    rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hmean]
    simp
  have hproduct : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (k - Fintype.card ι) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hfb : ∀ x, f x ≤ (2 : ℝ) ^ k := fun x =>
    (mul_le_mul_of_nonneg_left (hbound x) (by positivity)).trans_eq hproduct
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  exact (le_bernoulliAverage_expect_coordinateMarginal_le hf hsum hk hfb hr hr').trans
    (bernoulliAverage_mono hr hr1 (ite_expect_coordinateMarginal_le_of_normalize mass k))

end

end Cslib.BitString
