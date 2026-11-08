/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardCore
public import Cslib.Computability.Circuit.Boolean.Counting
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Computability.Circuit.Counting
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.BitString.BinarySymmetricChannel
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event

/-!
# Impagliazzo's hard-core lemma: hard-core sets

A *hard-core set* of density `δ` for a Boolean function `f` on `n` bits against circuits of size
`s` with advantage `ε` (`IsHardCoreSet`) is a set `H` of at least `δ 2 ^ n` inputs on which every
Boolean function of De Morgan circuit complexity at most `s` agrees with `f` on at most a
`1 / 2 + ε` fraction. A set is hard-core exactly when its indicator is a hard-core measure
(`isHardCoreSet_iff_isHardCoreMeasure`), so the set form is the stronger one. Impagliazzo's
hard-core lemma [Impagliazzo1995] is usually quoted in this set form, as in [Holenstein2005],
Section 2.

This file derives hard-core sets from the hard-core measures of
`CslibFrontier.Computability.Circuit.Boolean.HardCore` by randomized rounding, following
[Holenstein2005], Section 2.1.1: put each input `x` in `H` independently with probability `M x`.
Hoeffding's inequality bounds, for one predictor at a time, the deviation of `|H|` and of the
agreement on `H` from their means, and a union bound over the `C` functions of complexity at most
`s` (the finite set `Cslib.Circuits.Boolean.computableFunctions n s`) leaves a good outcome
(`exists_finset_card_agree_lt`). Rounding costs no circuit size, only density and advantage
(`IsHardCoreMeasure.exists_isHardCoreSet_sub`). Padding the measure first, raising each weight
`M x` to `(1 - w) M x + w`, adds the density that rounding loses
(`IsHardCoreMeasure.pad`), so a hard-core measure of density `δ` gives a hard-core set with at
least `δ 2 ^ n` elements, at the price of `2 γ` extra advantage
(`IsHardCoreMeasure.exists_isHardCoreSet`).

The rounding theorems assume the counting condition
`(C + 1) exp (-2 (γ δ (1 - δ))² 2 ^ n) < 1`, stated as an explicit hypothesis. The De Morgan
counting bound `Cslib.Circuits.Boolean.card_computableFunctions_mul_factorial_le` gives
`log C = O((s + 1) log (n + s + 1))` (made explicit in
`Cslib.Circuits.Boolean.card_computableFunctions_le_two_pow`), so the condition holds once
`(s + 1) log (n + s + 1)` is small compared with `γ² δ² (1 - δ)² 2 ^ n`, for instance for every
polynomial size bound `s` and fixed `γ`, `δ` when `n` is large.

## Scope

The circuits are arbitrary De Morgan circuits, sizes are counted as in `Cslib.Circuits.complexity`,
and the hard-core set is only shown to exist. Starting from hardness `δ` (every circuit of the
larger size errs on at least a `δ` fraction of the inputs), the set has density `δ`, the
parameters of Impagliazzo's lemma as recalled in [Holenstein2005], Section 2. Holenstein's
optimal density, a set of density `δ` from hardness `δ / 2` ([Holenstein2005], Lemma 2.1), is not
formalized here.

## Main definitions

* `Cslib.Circuits.Boolean.IsHardCoreSet`: a hard-core set of density `δ` against circuits of size
  `s` with advantage `ε`.

## Main results

* `Cslib.Circuits.Boolean.isHardCoreSet_iff_isHardCoreMeasure`: hard-core sets are the hard-core
  measures with `0`/`1` weights.
* `Cslib.Circuits.Boolean.exists_finset_card_agree_lt`: randomized rounding of a measure against a
  finite family of predictors.
* `Cslib.Circuits.Boolean.IsHardCoreMeasure.exists_isHardCoreSet`: a hard-core measure of density
  `δ` and advantage `ε` gives a hard-core set of density `δ` and advantage `ε + 2 γ`.
* `Cslib.Circuits.Boolean.exists_isHardCoreSet`: Impagliazzo's hard-core lemma in set form, with
  the size loss `s ↦ T s + 2 + 2 T (T + 2)` for any `T` with `3 ε² δ² T ≥ 1`.
* `Cslib.Circuits.Boolean.exists_isHardCoreSet_of_le`: the same, from hardness for a given size `S`.

## References

* [R. Impagliazzo, *Hard-core distributions for somewhat hard problems*][Impagliazzo1995]
* [T. Holenstein, *Key agreement from weak bit agreement*][Holenstein2005], Sections 2 and 2.1.1
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- A *hard-core set* `H` of density `δ` for `f` against circuits of size `s` with advantage
`ε` [Impagliazzo1995]: it contains at least `δ 2 ^ n` inputs, and every Boolean function of De
Morgan circuit complexity at most `s` agrees with `f` on at most a `1 / 2 + ε` fraction of
them. -/
structure IsHardCoreSet (f : BooleanFunction n) (s : ℕ) (δ ε : ℝ) (H : Finset (BitString n)) :
    Prop where
  /-- The set has density at least `δ`. -/
  mul_two_pow_le_card : δ * 2 ^ n ≤ #H
  /-- Every function computed with at most `s` gates agrees with `f` on at most a `1 / 2 + ε`
  fraction of the set. -/
  card_agree_le : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ s →
    (#{x ∈ H | g x = f x} : ℝ) ≤ (1 / 2 + ε) * #H

/-- A set is hard-core exactly when its indicator is a hard-core measure. -/
theorem isHardCoreSet_iff_isHardCoreMeasure {f : BooleanFunction n} {s : ℕ} {δ ε : ℝ}
    {H : Finset (BitString n)} :
    IsHardCoreSet f s δ ε H ↔ IsHardCoreMeasure f s δ ε fun x => if x ∈ H then 1 else 0 := by
  have hsum : ∑ x, (if x ∈ H then (1 : ℝ) else 0) = #H := by simp
  have hagree (g : BooleanFunction n) :
      ∑ x with g x = f x, (if x ∈ H then (1 : ℝ) else 0) = #{x ∈ H | g x = f x} := by
    rw [sum_boole, filter_filter]
    congr 2
    ext x
    simp [and_comm]
  constructor
  · intro h
    refine ⟨fun x => by split_ifs <;> simp, hsum ▸ h.mul_two_pow_le_card, fun g hg => ?_⟩
    rw [hsum, hagree]
    exact h.card_agree_le g hg
  · intro h
    refine ⟨hsum ▸ h.mul_two_pow_le_sum, fun g hg => ?_⟩
    rw [← hsum, ← hagree]
    exact h.sum_agree_le g hg

/-- Hard-core sets are monotone: they stay hard-core against fewer gates, at a lower density
and with a larger advantage. -/
theorem IsHardCoreSet.mono {f : BooleanFunction n} {s s' : ℕ} {δ δ' ε ε' : ℝ}
    {H : Finset (BitString n)} (hH : IsHardCoreSet f s δ ε H) (hs : s' ≤ s) (hδ : δ' ≤ δ)
    (hε : ε ≤ ε') : IsHardCoreSet f s' δ' ε' H where
  mul_two_pow_le_card := le_trans (by gcongr) hH.mul_two_pow_le_card
  card_agree_le g hg := (hH.card_agree_le g (hg.trans hs)).trans (by gcongr)

open Cslib.BitString in
/-- **Randomized rounding of a measure** [Holenstein2005]. Let `M` have weights in `[0, 1]`, let
`G` be a finite family of predictors, and let `a ∈ [0, 1]` bound the fraction of the mass of `M`
on which each predictor in `G` agrees with `f`. If `(|G| + 1) exp (-2 t² / 2 ^ n) < 1`, some set
`H` has more than `∑ x, M x - t` elements, and every predictor in `G` agrees with `f` on fewer
than `a |H| + t` of them. The set is the outcome of putting each input `x` in `H` independently
with probability `M x`; Hoeffding's inequality bounds each deviation, and a union bound over the
`|G| + 1` events leaves a good outcome. -/
theorem exists_finset_card_agree_lt (f : BooleanFunction n) (M : BitString n → ℝ)
    (hM : ∀ x, M x ∈ Set.Icc (0 : ℝ) 1) (G : Finset (BooleanFunction n)) {a t : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hG : ∀ g ∈ G, ∑ x with g x = f x, M x ≤ a * ∑ x, M x)
    (ht : 0 ≤ t) (hcount : (#G + 1) * Real.exp (-2 * t ^ 2 / 2 ^ n) < 1) :
    ∃ H : Finset (BitString n), ∑ x, M x - t < #H ∧
      ∀ g ∈ G, (#{x ∈ H | g x = f x} : ℝ) < a * #H + t := by
  classical
  -- Put `x` in the set with probability `M x`, independently.
  let coin (x : BitString n) : PMF Bool := flipBit ⟨M x, hM x⟩
  let S : PMF (BitString n → Bool) := Cslib.Probability.PMF.pi coin
  have hcoin (x : BitString n) (b : Bool) : (coin x b).toReal = if b then M x else 1 - M x :=
    flipBit_apply_toReal _ b
  have hN : (Fintype.card (BitString n) : ℝ) = 2 ^ n := by rw [BitString.card]; push_cast; rfl
  -- The size and the agreement of each predictor, as sums of independent scores.
  let size (b : Bool) : ℝ := if b then 1 else 0
  let score (g : BooleanFunction n) (x : BitString n) (b : Bool) : ℝ :=
    if b then (if g x = f x then 1 else 0) else a
  let bad₀ : Set (BitString n → Bool) :=
    {ω | ∑ x, size (ω x) ≤ (∑ x, ∑ b, (coin x b).toReal * size b) - t}
  let bad (g : BooleanFunction n) : Set (BitString n → Bool) :=
    {ω | (∑ x, ∑ b, (coin x b).toReal * score g x b) + t ≤ ∑ x, score g x (ω x)}
  have hexp : Real.exp (-2 * t ^ 2 / (Fintype.card (BitString n) * 1 ^ 2)) =
      Real.exp (-2 * t ^ 2 / 2 ^ n) := by rw [hN, one_pow, mul_one]
  have hbad₀ : (S.toOuterMeasure bad₀).toReal ≤ Real.exp (-2 * t ^ 2 / 2 ^ n) :=
    hexp ▸ Cslib.Probability.PMF.pi_sum_le_mean_sub coin (fun _ => size) zero_le_one
      (fun _ b _ => by cases b <;> simp [size]) ht
  have hbad (g : BooleanFunction n) :
      (S.toOuterMeasure (bad g)).toReal ≤ Real.exp (-2 * t ^ 2 / 2 ^ n) :=
    hexp ▸ Cslib.Probability.PMF.pi_sum_ge_mean_add coin (score g) zero_le_one
      (fun x b _ => by
        cases b
        · exact ha
        · simp only [score, ite_true]; split_ifs <;> simp) ht
  -- A union bound over the `|G| + 1` events.
  have hunion : (S.toOuterMeasure (bad₀ ∪ ⋃ g ∈ G, bad g)).toReal < 1 := by
    have hne : S.toOuterMeasure bad₀ + ∑ g ∈ G, S.toOuterMeasure (bad g) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨Cslib.Probability.PMF.toOuterMeasure_ne_top _ _,
        ENNReal.sum_ne_top.mpr fun _ _ => Cslib.Probability.PMF.toOuterMeasure_ne_top _ _⟩
    calc (S.toOuterMeasure (bad₀ ∪ ⋃ g ∈ G, bad g)).toReal
        ≤ (S.toOuterMeasure bad₀ + ∑ g ∈ G, S.toOuterMeasure (bad g)).toReal :=
          ENNReal.toReal_mono hne ((MeasureTheory.measure_union_le _ _).trans
            (add_le_add le_rfl (MeasureTheory.measure_biUnion_finset_le G bad)))
      _ = (S.toOuterMeasure bad₀).toReal + ∑ g ∈ G, (S.toOuterMeasure (bad g)).toReal := by
          rw [ENNReal.toReal_add (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
            (ENNReal.sum_ne_top.mpr fun _ _ => Cslib.Probability.PMF.toOuterMeasure_ne_top _ _),
            ENNReal.toReal_sum fun _ _ => Cslib.Probability.PMF.toOuterMeasure_ne_top _ _]
      _ ≤ Real.exp (-2 * t ^ 2 / 2 ^ n) + ∑ _g ∈ G, Real.exp (-2 * t ^ 2 / 2 ^ n) :=
          add_le_add hbad₀ (sum_le_sum fun g _ => hbad g)
      _ = (#G + 1) * Real.exp (-2 * t ^ 2 / 2 ^ n) := by rw [sum_const, nsmul_eq_mul]; ring
      _ < 1 := hcount
  obtain ⟨ω, -, hω⟩ : ∃ ω ∈ S.support, ω ∉ bad₀ ∪ ⋃ g ∈ G, bad g := by
    by_contra! h
    have h1 := (PMF.toOuterMeasure_apply_eq_one_iff S _).mpr h
    rw [h1, ENNReal.toReal_one] at hunion
    exact lt_irrefl _ hunion
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨hω₀, hωG⟩ := hω
  -- The set of inputs whose coin came up `true`.
  refine ⟨({x | ω x = true} : Finset (BitString n)), ?_, fun g hg => ?_⟩
  · have hmean : ∑ x, ∑ b, (coin x b).toReal * size b = ∑ x, M x :=
      sum_congr rfl fun x _ => by simp [hcoin, size]
    have hsize : ∑ x, size (ω x) = #{x | ω x = true} := by
      simp only [size]
      rw [sum_boole]
    have h := hω₀
    simp only [bad₀, Set.mem_ofPred_eq, not_le, hmean, hsize] at h
    exact h
  · have hmean : ∑ x, ∑ b, (coin x b).toReal * score g x b =
        (∑ x with g x = f x, M x) + a * (2 ^ n - ∑ x, M x) := by
      have hx (x : BitString n) : ∑ b, (coin x b).toReal * score g x b =
          (if g x = f x then M x else 0) + a * (1 - M x) := by
        simp only [Fintype.sum_bool, hcoin, score, ite_true, Bool.false_eq_true, ite_false]
        split_ifs <;> ring
      rw [sum_congr rfl fun x _ => hx x, sum_add_distrib, ← sum_filter, ← mul_sum, sum_sub_distrib,
        sum_const, card_univ, nsmul_eq_mul, mul_one, hN]
    have hscore : ∑ x, score g x (ω x) =
        #{x | ω x = true ∧ g x = f x} + a * (2 ^ n - #{x | ω x = true}) := by
      have hx (x : BitString n) : score g x (ω x) =
          (if ω x = true ∧ g x = f x then 1 else 0) + a * (1 - if ω x = true then 1 else 0) := by
        simp only [score]
        by_cases hωx : ω x = true <;> by_cases hgx : g x = f x <;> simp [hωx, hgx]
      rw [sum_congr rfl fun x _ => hx x, sum_add_distrib, sum_boole, ← mul_sum, sum_sub_distrib,
        sum_boole, sum_const, card_univ, nsmul_eq_mul, mul_one, hN]
    have hfilter : #{x ∈ ({x | ω x = true} : Finset (BitString n)) | g x = f x} =
        #{x | ω x = true ∧ g x = f x} := by rw [filter_filter]
    have h := hωG g hg
    simp only [bad, Set.mem_ofPred_eq, not_le, hmean, hscore] at h
    have hGg := hG g hg
    rw [hfilter]
    nlinarith

/-- **From a hard-core measure to a hard-core set, losing density** [Holenstein2005]. Let `M` be a
hard-core measure of density `δ` for `f` against circuits of size `s` with advantage `ε ≥ 0`,
and let `0 ≤ η < δ`. If `(C + 1) exp (-2 η² 2 ^ n) < 1`, where `C` is the number of Boolean
functions of De Morgan circuit complexity at most `s`, then `f` has a hard-core set of density
`δ - η` against circuits of size `s` with advantage `ε + η / (δ - η)`. -/
theorem IsHardCoreMeasure.exists_isHardCoreSet_sub {f : BooleanFunction n} {s : ℕ} {δ ε η : ℝ}
    {M : BitString n → ℝ} (hM : IsHardCoreMeasure f s δ ε M) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hηδ : η < δ)
    (hcount : (#(computableFunctions n s) + 1) * Real.exp (-2 * η ^ 2 * 2 ^ n) < 1) :
    ∃ H, IsHardCoreSet f s (δ - η) (ε + η / (δ - η)) H := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hexp : -2 * (η * 2 ^ n) ^ 2 / 2 ^ n = -2 * η ^ 2 * 2 ^ n := by
    field_simp
  have hagree (g : BooleanFunction n) (hg : g ∈ computableFunctions n s) :
      ∑ x with g x = f x, M x ≤ min (1 / 2 + ε) 1 * ∑ x, M x := by
    have h := hM.sum_agree_le g (Circuits.mem_computableFunctions_iff_complexity_le.mp hg)
    have hle : ∑ x with g x = f x, M x ≤ ∑ x, M x :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => (hM.mem_Icc x).1
    rcases min_choice (1 / 2 + ε) 1 with hmin | hmin <;> rw [hmin]
    · exact h
    · linarith
  obtain ⟨H, hsize, hH⟩ := exists_finset_card_agree_lt (t := η * 2 ^ n) f M hM.mem_Icc
    (computableFunctions n s) ⟨le_min (by linarith) zero_le_one, min_le_right _ _⟩ hagree
    (by positivity)
    (by rw [hexp]; exact hcount)
  have hcard : (δ - η) * 2 ^ n < #H := by nlinarith [hM.mul_two_pow_le_sum]
  have hgap : 0 < δ - η := sub_pos.mpr hηδ
  refine ⟨H, hcard.le, fun g hg => ?_⟩
  have h := hH g (Circuits.mem_computableFunctions_iff_complexity_le.mpr hg)
  have hmin : min (1 / 2 + ε) 1 * (#H : ℝ) ≤ (1 / 2 + ε) * #H :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  have hslack : η * 2 ^ n ≤ η / (δ - η) * #H := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hgap]
    nlinarith
  linarith

/-- **Padding a hard-core measure.** Raising every weight of a hard-core measure `M` of density
`δ` and advantage `ε` to `(1 - w) M x + w` gives a hard-core measure of density
`δ + w (1 - δ)` and advantage `ε + γ`, provided `w ∈ [0, 1]`, `γ ≥ 0` and
`w (1 / 2 - ε - γ) ≤ γ (1 - w) δ`. -/
theorem IsHardCoreMeasure.pad {f : BooleanFunction n} {s : ℕ} {δ ε w γ : ℝ}
    {M : BitString n → ℝ} (hM : IsHardCoreMeasure f s δ ε M) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (hγ : 0 ≤ γ) (hwγ : w * (1 / 2 - ε - γ) ≤ γ * (1 - w) * δ) :
    IsHardCoreMeasure f s (δ + w * (1 - δ)) (ε + γ) fun x => (1 - w) * M x + w := by
  obtain ⟨hw0, hw1⟩ := hw
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hsum : ∑ x, ((1 - w) * M x + w) = (1 - w) * ∑ x, M x + w * 2 ^ n := by
    rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, BitString.card, nsmul_eq_mul]
    push_cast
    ring
  have hδM := hM.mul_two_pow_le_sum
  refine ⟨fun x => ?_, ?_, fun g hg => ?_⟩
  · obtain ⟨h0, h1⟩ := hM.mem_Icc x
    constructor <;> nlinarith
  · rw [hsum]
    nlinarith
  · have hagree : ∑ x with g x = f x, ((1 - w) * M x + w) =
        (1 - w) * ∑ x with g x = f x, M x + w * #{x | g x = f x} := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      ring
    have hcount : (#{x | g x = f x} : ℝ) ≤ 2 ^ n := by
      have h := card_filter_le (univ : Finset (BitString n)) fun x => g x = f x
      rw [card_univ, BitString.card] at h
      exact_mod_cast h
    have hle := hM.sum_agree_le g hg
    rw [hagree, hsum]
    have h1 : (1 - w) * ∑ x with g x = f x, M x ≤ (1 - w) * ((1 / 2 + ε) * ∑ x, M x) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    have h2 : w * (#{x | g x = f x} : ℝ) ≤ w * 2 ^ n := mul_le_mul_of_nonneg_left hcount hw0
    have h3 : γ * (1 - w) * (δ * 2 ^ n) ≤ γ * (1 - w) * ∑ x, M x :=
      mul_le_mul_of_nonneg_left hδM (mul_nonneg hγ (by linarith))
    have h4 : w * (1 / 2 - ε - γ) * 2 ^ n ≤ γ * (1 - w) * δ * 2 ^ n :=
      mul_le_mul_of_nonneg_right hwγ hN.le
    nlinarith

/-- **From a hard-core measure to a hard-core set of the same density** [Impagliazzo1995],
[Holenstein2005]. Let `M` be a hard-core measure of density `δ ∈ (0, 1)` for `f` against
circuits of size `s` with advantage `ε ≥ 0`, and let `0 < γ ≤ 1`. If
`(C + 1) exp (-2 (γ δ (1 - δ))² 2 ^ n) < 1`, where `C` is the number of Boolean functions of De
Morgan circuit complexity at most `s`, then `f` has a hard-core set with at least `δ 2 ^ n`
elements against circuits of size `s` with advantage `ε + 2 γ`. The measure is first padded to
density `δ + γ δ (1 - δ)` (`IsHardCoreMeasure.pad`), so that rounding it
(`IsHardCoreMeasure.exists_isHardCoreSet_sub`) loses no density. -/
theorem IsHardCoreMeasure.exists_isHardCoreSet {f : BooleanFunction n} {s : ℕ} {δ ε γ : ℝ}
    {M : BitString n → ℝ} (hM : IsHardCoreMeasure f s δ ε M) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hcount : (#(computableFunctions n s) + 1) *
      Real.exp (-2 * (γ * δ * (1 - δ)) ^ 2 * 2 ^ n) < 1) :
    ∃ H, IsHardCoreSet f s δ (ε + 2 * γ) H := by
  have hγδ : γ * δ ≤ 1 := by nlinarith
  have hpos : 0 ≤ γ * δ * (1 / 2 + ε + γ * (1 - δ)) := by
    have : 0 ≤ 1 - δ := by linarith
    positivity
  have hpad := hM.pad (w := γ * δ) (γ := γ) ⟨by positivity, hγδ⟩ hγ.le (by nlinarith [hpos])
  have hη : 0 < γ * δ * (1 - δ) := by
    have : 0 < 1 - δ := by linarith
    positivity
  obtain ⟨H, hH⟩ := hpad.exists_isHardCoreSet_sub (η := γ * δ * (1 - δ)) (by linarith) hη.le
    (by nlinarith) hcount
  have hδ' : δ + γ * δ * (1 - δ) - γ * δ * (1 - δ) = δ := by ring
  have hratio : γ * δ * (1 - δ) / (δ + γ * δ * (1 - δ) - γ * δ * (1 - δ)) ≤ γ := by
    rw [hδ', div_le_iff₀ hδ]
    nlinarith
  exact ⟨H, hH.mono le_rfl hδ'.ge (by linarith)⟩

/-- **Impagliazzo's hard-core lemma, set form** [Impagliazzo1995], with explicit parameters. Let
`0 < δ < 1`, `0 < ε`, `0 < γ ≤ 1`, and let `T` be a number of rounds with `1 ≤ 3 ε² δ² T`. If
every Boolean function of De Morgan circuit complexity at most `T s + (2 + T (2 (T + 2)))` agrees
with `f` on at most a `1 - δ` fraction of the inputs, and
`(C + 1) exp (-2 (γ δ (1 - δ))² 2 ^ n) < 1`, where `C` is the number of functions of complexity
at most `s`, then some set `H` of at least `δ 2 ^ n` inputs is hard-core: every function of
complexity at most `s` agrees with `f` on at most a `1 / 2 + ε + 2 γ` fraction of `H`. -/
theorem exists_isHardCoreSet {f : BooleanFunction n} {s T : ℕ} {δ ε γ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T)
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ T * s + (2 + T * (2 * (T + 2))) →
        (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ)
    (hcount : (#(computableFunctions n s) + 1) *
      Real.exp (-2 * (γ * δ * (1 - δ)) ^ 2 * 2 ^ n) < 1) :
    ∃ H, IsHardCoreSet f s δ (ε + 2 * γ) H := by
  obtain ⟨M, hM⟩ := exists_isHardCoreMeasure hδ hε hT hf
  exact hM.exists_isHardCoreSet hδ hδ1 hε.le hγ hγ1 hcount

/-- **Impagliazzo's hard-core lemma, set form** [Impagliazzo1995], from hardness for a given size.
Let `0 < δ < 1`, `0 < ε`, `0 < γ ≤ 1`, let `T` be a number of rounds with `1 ≤ 3 ε² δ² T`, and let
`2 + T (2 (T + 2)) ≤ S`. If every Boolean function of De Morgan circuit complexity at most `S`
agrees with `f` on at most a `1 - δ` fraction of the inputs, and the counting condition
`(C + 1) exp (-2 (γ δ (1 - δ))² 2 ^ n) < 1` holds for the number `C` of functions of complexity at
most `s = (S - (2 + T (2 (T + 2)))) / T`, then some set of at least `δ 2 ^ n` inputs is hard-core
against circuits of size `s` with advantage `ε + 2 γ`. -/
theorem exists_isHardCoreSet_of_le {f : BooleanFunction n} {S T : ℕ} {δ ε γ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T)
    (hS : 2 + T * (2 * (T + 2)) ≤ S)
    (hf : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ S →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ)
    (hcount : (#(computableFunctions n ((S - (2 + T * (2 * (T + 2)))) / T)) + 1) *
      Real.exp (-2 * (γ * δ * (1 - δ)) ^ 2 * 2 ^ n) < 1) :
    ∃ H, IsHardCoreSet f ((S - (2 + T * (2 * (T + 2)))) / T) δ (ε + 2 * γ) H := by
  obtain ⟨M, hM⟩ := exists_isHardCoreMeasure_of_le hδ hε hT hS hf
  exact hM.exists_isHardCoreSet hδ hδ1 hε.le hγ hγ1 hcount

end Cslib.Circuits.Boolean
