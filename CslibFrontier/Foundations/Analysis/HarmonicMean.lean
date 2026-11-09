/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.Function
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Harmonic means on finite types

The harmonic mean of a nonnegative function on a finite type (`Cslib.harmonicMean`), zero as soon
as a value is zero, has a variational formula: it is the least energy `𝔼 (f w ^ 2)` of a
nonnegative weight `w` of mean one [Korten, Lemma 11][Korten2026]
(`Cslib.harmonicMean_variational`). Completing the square gives the lower bound
(`Cslib.harmonicMean_le_energy`), and an explicit weight attains it, including when a value
vanishes (`Cslib.harmonicMean_exists_weight`). Hence the harmonic mean is monotone
(`Cslib.harmonicMean_mono`) and concave (`Cslib.concaveOn_harmonicMean`), and at most the
arithmetic mean (`Cslib.harmonicMean_le_expect`).

## Main definitions

* `Cslib.harmonicMean`: the uniform harmonic mean on a finite type, zero whenever an entry is zero.

## Main results

* `Cslib.harmonicMean_le_energy`, `Cslib.harmonicMean_exists_weight`,
  `Cslib.harmonicMean_variational`: the variational formula for the harmonic mean.
* `Cslib.harmonicMean_mono`, `Cslib.concaveOn_harmonicMean`, `Cslib.harmonicMean_le_expect`,
  `Cslib.expect_harmonicMean_le`: monotonicity, concavity, comparison with the arithmetic mean, and
  Jensen's inequality.
* `Cslib.harmonicMean_light_fraction_le`: reciprocal-density Markov bound for small entries.
* `Cslib.harmonicMean_pair`, `Cslib.harmonicMean_bool`: two-point harmonic mean decomposition on
  `Bool × α` and on `Bool`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib

open scoped BigOperators
open Finset

/-- The uniform harmonic mean, with value zero whenever an entry is zero. -/
noncomputable def harmonicMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  if ∃ x, f x = 0 then 0 else (𝔼 x, (f x)⁻¹)⁻¹

section

variable {α : Type*} [Fintype α]

/-- A zero entry makes the harmonic mean zero: inside the average, `0⁻¹` counts as `∞` rather than
as Lean's `0⁻¹ = 0`. -/
theorem harmonicMean_eq_zero_of_exists {f : α → ℝ} (hf : ∃ x, f x = 0) : harmonicMean f = 0 := by
  rw [harmonicMean, ite_eq_left hf]

/-- The harmonic mean of positive entries is the reciprocal of the mean of their reciprocals. -/
theorem harmonicMean_of_pos {f : α → ℝ} (hf : ∀ x, 0 < f x) :
    harmonicMean f = (𝔼 x, (f x)⁻¹)⁻¹ :=
  ite_eq_right fun ⟨x, hx⟩ => (hf x).ne' hx

/-- Harmonic means of nonnegative entries are nonnegative. -/
theorem harmonicMean_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := by
  unfold harmonicMean
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))

/-- An equivalence of finite types preserves harmonic means. -/
theorem harmonicMean_equiv {β : Type*} [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : harmonicMean (fun x => f (e x)) = harmonicMean f := by
  have hz : (∃ x, f (e x) = 0) ↔ ∃ y, f y = 0 := e.exists_congr_left.trans (by simp)
  simp only [harmonicMean, hz]
  rw [Fintype.expect_equiv e (fun x => (f (e x))⁻¹) (fun y => (f y)⁻¹) (fun _ => rfl)]

variable [Nonempty α]

/-- Every weight with mean one bounds the harmonic mean by its quadratic energy.
The weight need not be nonnegative for this direction. -/
theorem harmonicMean_le_energy {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 := by
  by_cases hz : ∃ x, f x = 0
  · rw [harmonicMean_eq_zero_of_exists hz]
    exact expect_nonneg fun x _ => mul_nonneg (hf x) (sq_nonneg _)
  have hpos (x : α) : 0 < f x := (hf x).lt_of_ne' fun h => hz ⟨x, h⟩
  have he : (𝔼 x, (f x)⁻¹) ≠ 0 :=
    (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty).ne'
  let h := (𝔼 x, (f x)⁻¹)⁻¹
  have hs := expect_nonneg (s := univ)
    (fun x _ => mul_nonneg (hf x) (sq_nonneg (w x - h / f x)))
  have hid (x : α) : f x * (w x - h / f x) ^ 2 =
      f x * w x ^ 2 - 2 * h * w x + h ^ 2 * (f x)⁻¹ := by
    field_simp [(hpos x).ne']
    ring
  simp_rw [hid, expect_add_distrib, expect_sub_distrib, ← mul_expect] at hs
  rw [hw] at hs
  have hh : h ^ 2 * (𝔼 x, (f x)⁻¹) = h := by
    dsimp [h]
    field_simp
  rw [hh] at hs
  rw [harmonicMean_of_pos hpos]
  dsimp [h] at hs
  linarith

/-- A nonnegative weight of mean one attains the variational minimum,
including when an entry of `f` is zero. -/
theorem harmonicMean_exists_weight {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧
      (𝔼 x, f x * w x ^ 2) = harmonicMean f := by
  classical
  by_cases hz : ∃ x, f x = 0
  · obtain ⟨a, ha⟩ := hz
    refine ⟨fun x => if x = a then Fintype.card α else 0, ?_, ?_, ?_⟩
    · intro x; dsimp only; split_ifs <;> positivity
    · rw [Fintype.expect_eq_sum_div_card]
      simp [Fintype.card_ne_zero]
    · rw [harmonicMean_eq_zero_of_exists ⟨a, ha⟩]
      apply expect_eq_zero
      intro x _
      by_cases hx : x = a <;> simp [hx, ha]
  · have hpos (x : α) : 0 < f x := (hf x).lt_of_ne' fun h => hz ⟨x, h⟩
    have he : (𝔼 x, (f x)⁻¹) ≠ 0 :=
      (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty).ne'
    let h := (𝔼 x, (f x)⁻¹)⁻¹
    refine ⟨fun x => h * (f x)⁻¹, ?_, ?_, ?_⟩
    · intro x
      exact mul_nonneg (inv_nonneg.mpr
        (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))) (inv_nonneg.mpr (hf x))
    · rw [← mul_expect]
      exact inv_mul_cancel₀ he
    · have hid (x : α) : f x * (h * (f x)⁻¹) ^ 2 = h ^ 2 * (f x)⁻¹ := by
        field_simp [(hpos x).ne']
      simp_rw [hid, ← mul_expect]
      rw [harmonicMean_of_pos hpos]
      dsimp [h]
      field_simp

/-- **The variational formula for the harmonic mean** [Korten, Lemma 11][Korten2026], on every
nonempty finite type: the harmonic mean is the least energy `𝔼 (f w ^ 2)` of a nonnegative weight
`w` of mean one. -/
theorem harmonicMean_variational {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f = sInf {a : ℝ | ∃ w : α → ℝ,
      (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧ (𝔼 x, f x * w x ^ 2) = a} := by
  symm
  apply IsLeast.csInf_eq
  constructor
  · exact harmonicMean_exists_weight hf
  · rintro _ ⟨w, _, hw, rfl⟩
    exact harmonicMean_le_energy hf hw

/-- Harmonic means are monotone in their nonnegative entries. -/
theorem harmonicMean_mono {f g : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    harmonicMean f ≤ harmonicMean g := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight
    (fun x => (hf x).trans (hfg x))
  rw [← he]
  exact (harmonicMean_le_energy hf hw).trans
    (expect_le_expect fun x _ => mul_le_mul_of_nonneg_right (hfg x) (sq_nonneg _))

/-- The harmonic mean is concave on nonnegative functions. -/
theorem concaveOn_harmonicMean : ConcaveOn ℝ (Set.Ici 0) (harmonicMean : (α → ℝ) → ℝ) := by
  refine ⟨convex_Ici 0, fun f hf g hg a b ha hb _ => ?_⟩
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight (f := a • f + b • g)
    (fun x => add_nonneg (mul_nonneg ha (hf x)) (mul_nonneg hb (hg x)))
  rw [← he, smul_eq_mul, smul_eq_mul]
  calc
    _ ≤ a * (𝔼 x, f x * w x ^ 2) + b * (𝔼 x, g x * w x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hf hw) ha)
        (mul_le_mul_of_nonneg_left (harmonicMean_le_energy hg hw) hb)
    _ = _ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
        expect_add_distrib, ← mul_expect]

/-- The harmonic mean is at most the arithmetic mean. -/
theorem harmonicMean_le_expect {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := by
  simpa using harmonicMean_le_energy (w := fun _ => 1) hf (by simp)

/-- **Jensen's inequality for the harmonic mean**: the average of harmonic means is at most the
harmonic mean of the average. -/
theorem expect_harmonicMean_le {β : Type*} [Fintype β]
    {f : β → α → ℝ} (hf : ∀ y x, 0 ≤ f y x) :
    (𝔼 y, harmonicMean (f y)) ≤ harmonicMean (fun x => 𝔼 y, f y x) := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight
    (fun x => expect_nonneg fun y _ => hf y x)
  calc
    _ ≤ 𝔼 y, 𝔼 x, f y x * w x ^ 2 :=
      expect_le_expect fun y _ => harmonicMean_le_energy (hf y) hw
    _ = 𝔼 x, (𝔼 y, f y x) * w x ^ 2 := by
      rw [expect_comm]
      simp_rw [expect_mul]
    _ = _ := he

/-- The harmonic mean of a constant on a nonempty finite set is that constant. -/
theorem harmonicMean_const (c : ℝ) :
    harmonicMean (fun _ : α => c) = c := by
  by_cases hc : c = 0 <;> simp [harmonicMean, hc]

/-- A positive harmonic-mean lower bound controls the fraction of small entries.
This is the reciprocal-density Markov step used for light patterns. -/
theorem harmonicMean_light_fraction_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  have hp (x : α) : 0 < f x := by
    refine (hf x).lt_of_ne' fun h => ?_
    rw [harmonicMean_eq_zero_of_exists ⟨x, h⟩] at ha'
    exact (not_le_of_gt ha) ha'
  have he : 0 < 𝔼 x, (f x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hp x)) univ_nonempty
  have hinv : (𝔼 x, (f x)⁻¹) ≤ 1 / a := by
    rw [harmonicMean_of_pos hp, ← one_div] at ha'
    have hmul := (le_div_iff₀ he).mp ha'
    apply (le_div_iff₀ ha).mpr
    linarith
  calc
    _ ≤ 𝔼 x, b * (f x)⁻¹ := by
      apply expect_le_expect
      intro x _
      split_ifs with h
      · rw [← div_eq_mul_inv]
        exact (one_le_div (hp x)).mpr h
      · exact mul_nonneg hb (inv_nonneg.mpr (hf x))
    _ = b * (𝔼 x, (f x)⁻¹) := (mul_expect _ _ _).symm
    _ ≤ b * (1 / a) := mul_le_mul_of_nonneg_left hinv hb
    _ = _ := by ring

/-- The harmonic mean of a function on `Bool × α` is the two-point harmonic mean
`2 h₀ h₁ / (h₀ + h₁)` of the harmonic means `h₀`, `h₁` of its two halves. -/
theorem harmonicMean_pair {f : Bool → α → ℝ} (hf : ∀ b x, 0 ≤ f b x) :
    harmonicMean (fun x : Bool × α => f x.1 x.2) =
      2 * harmonicMean (f false) * harmonicMean (f true) /
        (harmonicMean (f false) + harmonicMean (f true)) := by
  by_cases h0 : ∃ b x, f b x = 0
  · obtain ⟨b, x, hx⟩ := h0
    rw [harmonicMean_eq_zero_of_exists (f := fun x : Bool × α => f x.1 x.2) ⟨(b, x), hx⟩]
    cases b <;> simp [harmonicMean_eq_zero_of_exists ⟨x, hx⟩]
  have hpos (b : Bool) (x : α) : 0 < f b x := (hf b x).lt_of_ne' fun h => h0 ⟨b, x, h⟩
  have hp (b : Bool) : 0 < 𝔼 x, (f b x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hpos b x)) univ_nonempty
  rw [harmonicMean_of_pos (f := fun x : Bool × α => f x.1 x.2) fun x => hpos x.1 x.2,
    harmonicMean_of_pos (hpos false), harmonicMean_of_pos (hpos true), Fintype.expect_prod_type,
    Fintype.expect_bool]
  have hsum := add_pos (hp false) (hp true)
  field_simp [(hp false).ne', (hp true).ne', hsum.ne']
  simpa only [one_div, add_comm] using (div_self hsum.ne').symm

/-- The harmonic mean on `Bool` of `a` at `false` and `b` at `true` is `2 a b / (a + b)`. -/
theorem harmonicMean_bool {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    harmonicMean (fun x : Bool => if x then b else a) = 2 * a * b / (a + b) := by
  rw [← harmonicMean_equiv (Equiv.prodPUnit Bool : Bool × Unit ≃ Bool)]
  have h := harmonicMean_pair (α := Unit) (f := fun x _ => if x then b else a)
    fun x _ => by cases x <;> assumption
  simpa only [Equiv.prodPUnit_apply, Bool.false_eq_true, ↓reduceIte, harmonicMean_const] using h

end

end Cslib
