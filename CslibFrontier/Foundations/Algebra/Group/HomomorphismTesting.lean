/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Hamming
public import CslibFrontier.Foundations.Data.Finset.Expect
public import CslibFrontier.Foundations.Data.Finset.Quantile
public import CslibFrontier.Probability.Collision
public import CslibFrontier.Probability.PMF.Expect
public import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Homomorphism testing on finite abelian groups

Uniform rejection of the additive consistency test and plurality correction by the votes
`f (x + y) - f y`. The domain and codomain may be trivial. For rejection `ε < 1/6`,
every plurality correction is a homomorphism within normalized Hamming distance `2ε`.
The minimum over homomorphisms is attained and gives the unconditional source bound.

The proof uses a collision lower bound from two failing additive equations, then a union bound
on three correction failures to prove additivity. A differing value of `f` forces at least
half its votes to reject, giving the distance bound by averaging.

## Main definitions

* `Cslib.HomomorphismTesting.rejection`: uniform independent test rejection.
* `Cslib.HomomorphismTesting.IsPlurality`: plurality specification allowing arbitrary ties.
* `Cslib.HomomorphismTesting.correction`: bundled corrected homomorphism.
* `Cslib.HomomorphismTesting.distance`: minimum normalized disagreement.

## Main results

* `Cslib.HomomorphismTesting.concentration`: every plurality has mass at least `1 - 2ε`.
* `Cslib.HomomorphismTesting.plurality_add`: additivity below rejection `1/6`.
* `Cslib.HomomorphismTesting.closeness`: disagreement at most `2ε`.
* `Cslib.HomomorphismTesting.three_mul_distance_sub_six_sq_le_rejection`: the unconditional
  quadratic bound `3δ - 6δ² ≤ ε` (Exercise 9.20).
* `Cslib.HomomorphismTesting.min_le_rejection`: the unconditional source endpoint.

These are finite probability statements; no running time or representation is specified.

## References

* [Goldreich2007DraftR5], draft Exercises 9.20–9.21 (r5 PDF 68–70, printed 450–452).
-/

public section

open scoped BigOperators
open Finset


namespace Cslib.HomomorphismTesting

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]

open Classical in
/-- Uniform independent rejection probability of the additive consistency test. -/
@[expose] noncomputable def rejection (f : G → H) : ℝ :=
  𝔼 p : G × G, if f p.1 + f p.2 ≠ f (p.1 + p.2) then 1 else 0

open Classical in
/-- A two-query vote for the value at `x`. -/
@[expose] def vote (f : G → H) (x y : G) : H := f (x + y) - f y

open Classical in
/-- Every value has at most as many votes as the selected value. Ties are allowed. -/
@[expose] def IsPlurality (f : G → H) (φ : G → H) : Prop :=
  ∀ x b, #{y | vote f x y = b} ≤ #{y | vote f x y = φ x}

open Classical in
/-- Plurality corrections exist without a tie-breaking convention. -/
theorem exists_plurality (f : G → H) : ∃ φ, IsPlurality f φ := by
  classical
  exact ⟨fun x => (Fintype.exists_forall_card_filter_le_card_filter (vote f x)).choose,
    fun x => (Fintype.exists_forall_card_filter_le_card_filter (vote f x)).choose_spec⟩

open Classical in
/-- An actual homomorphism passes every test. -/
@[simp] theorem rejection_hom (f : G →+ H) : rejection (f : G → H) = 0 := by
  simp [rejection, map_add]

open Classical in
private theorem rejection_eq_expect (f : G → H) : rejection f =
    𝔼 a, 𝔼 b, if f a + f b ≠ f (a + b) then (1 : ℝ) else 0 :=
  Fintype.expect_prod_type _

open Classical in
/-- Independent votes for a fixed point agree with probability at least `1 - 2ε`. -/
theorem collision_lower (f : G → H) (x : G) :
    1 - 2 * rejection f ≤
      𝔼 a, 𝔼 b, if vote f x a = vote f x b then (1 : ℝ) else 0 := by
  classical
  let bad (a b : G) : ℝ := if f a + f b ≠ f (a + b) then 1 else 0
  have point (a b : G) :
      1 - bad (x + a) b - bad a (x + b) ≤
        (if vote f x a = vote f x b then (1 : ℝ) else 0) := by
    dsimp [bad, vote]
    by_cases h₁ : f (x + a) + f b = f ((x + a) + b)
    · by_cases h₂ : f a + f (x + b) = f (a + (x + b))
      · have he : f (x + a) - f a = f (x + b) - f b := by
          have hsum : x + a + b = a + (x + b) := by abel
          rw [hsum] at h₁
          exact sub_eq_sub_iff_add_eq_add.mpr (h₁.trans (h₂.symm.trans (add_comm _ _)))
        simp [h₁, h₂, he]
      · by_cases hc : f (x + a) - f a = f (x + b) - f b <;> simp [h₁, h₂, hc]
    · by_cases h₂ : f a + f (x + b) = f (a + (x + b)) <;>
        by_cases hc : f (x + a) - f a = f (x + b) - f b <;> simp [h₁, h₂, hc]
  have h := expect_le_expect (s := univ) (fun a _ =>
    expect_le_expect (s := univ) (fun b _ => point a b))
  have h₁ : (𝔼 a, 𝔼 b, bad (x + a) b) = rejection f := by
    rw [show (𝔼 a, 𝔼 b, bad (x + a) b) = 𝔼 a, 𝔼 b, bad a b from
      Fintype.expect_add_left (fun a => 𝔼 b, bad a b) x]
    exact (rejection_eq_expect f).symm
  have h₂ : (𝔼 a, 𝔼 b, bad a (x + b)) = rejection f := by
    simp_rw [Fintype.expect_add_left]
    exact (rejection_eq_expect f).symm
  simp only [expect_sub_distrib, Fintype.expect_const] at h
  rw [h₁, h₂] at h
  linarith

open Classical in
/-- Every plurality value carries mass at least `1 - 2ε`. -/
theorem concentration (f : G → H) {φ : G → H} (hφ : IsPlurality f φ) (x : G) :
    1 - 2 * rejection f ≤
      𝔼 y, if vote f x y = φ x then (1 : ℝ) else 0 := by
  classical
  open Probability.PMF in
  have hc : collisionProbability ((Probability.PMF.uniformOfFintype G).map (vote f x)) =
      𝔼 a, 𝔼 b, if vote f x a = vote f x b then (1 : ℝ) else 0 := by
    rw [collisionProbability_eq_probability]
    simp only [PMF.bind_map, PMF.map_comp, Function.comp_def,
      toReal_uniformOfFintype_bind_apply, toReal_uniformOfFintype_map_apply,
      decide_eq_true_eq, ← Fintype.expect_boole]
  obtain ⟨b, hb⟩ := Probability.PMF.exists_le_toReal_of_le_collisionProbability
    ((Probability.PMF.uniformOfFintype G).map (vote f x)) (hc.symm ▸ collision_lower f x)
  rw [Probability.PMF.toReal_uniformOfFintype_map_apply] at hb
  rw [Fintype.expect_boole]
  refine hb.trans ?_
  rw [nnratCast_dens, nnratCast_dens]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hφ x b) (Nat.cast_nonneg _)

open Classical in
/-- The error probability of the correction at each point is at most `2ε`. -/
theorem correction_error (f : G → H) {φ : G → H} (hφ : IsPlurality f φ) (x : G) :
    (𝔼 y, if φ x ≠ vote f x y then (1 : ℝ) else 0) ≤ 2 * rejection f := by
  have h := concentration f hφ x
  have he : (𝔼 y, if φ x ≠ vote f x y then (1 : ℝ) else 0) =
      1 - 𝔼 y, if vote f x y = φ x then (1 : ℝ) else 0 := by
    rw [← Fintype.expect_const (ι := G) (1 : ℝ), ← expect_sub_distrib]
    exact expect_congr rfl fun y _ => by split_ifs <;> simp_all
  linarith

open Classical in
/-- Below rejection `1/6`, every plurality correction preserves addition. -/
theorem plurality_add (f : G → H) {φ : G → H} (hφ : IsPlurality f φ)
    (hε : rejection f < 1 / 6) (x y : G) : φ (x + y) = φ x + φ y := by
  let e (z r : G) : ℝ := if φ z ≠ vote f z r then 1 else 0
  have h₁ := correction_error f hφ x
  have h₂ := correction_error f hφ y
  have h₃ := correction_error f hφ (x + y)
  have ht : (𝔼 r, (e x r + e y (r - y) + e (x + y) (r - y))) < 1 := by
    have shift (z : G) : (𝔼 r, e z (r - y)) = 𝔼 r, e z r :=
      Fintype.expect_equiv (Equiv.subRight y) _ _ fun _ => rfl
    rw [expect_add_distrib, expect_add_distrib, shift, shift]
    dsimp [e] at *
    linarith
  obtain ⟨r, -, hr⟩ := exists_lt_of_expect_lt univ_nonempty ht
  have good : φ x = vote f x r ∧ φ y = vote f y (r - y) ∧
      φ (x + y) = vote f (x + y) (r - y) := by
    dsimp [e] at hr
    split_ifs at hr <;> simp_all <;> norm_num at hr
  obtain ⟨hx, hy, hxy⟩ := good
  rw [hx, hy, hxy]
  dsimp [vote]
  have ha : y + (r - y) = r := by abel
  have hb : x + y + (r - y) = x + r := by abel
  rw [ha, hb]
  abel

open Classical in
/-- The plurality correction bundled as an additive homomorphism. -/
@[expose] noncomputable def correction (f : G → H) {φ : G → H} (hφ : IsPlurality f φ)
    (hε : rejection f < 1 / 6) : G →+ H :=
  AddMonoidHom.mk' φ (plurality_add f hφ hε)

open Classical in
/-- Below rejection `1/6`, the plurality correction differs on at most `2ε` of the domain. -/
theorem closeness (f : G → H) {φ : G → H} (hφ : IsPlurality f φ)
    (hε : rejection f < 1 / 6) :
    (hammingDist f φ : ℝ) / Fintype.card G ≤ 2 * rejection f := by
  have point (x : G) :
      (1 / 2 : ℝ) * (if f x ≠ φ x then 1 else 0) ≤
        𝔼 y, if f x + f y ≠ f (x + y) then (1 : ℝ) else 0 := by
    by_cases hx : f x = φ x
    · simp only [hx, ne_eq, not_true_eq_false, ite_false, mul_zero]
      exact expect_nonneg fun _ _ => by positivity
    · have hc := concentration f hφ x
      have hm : (𝔼 y, if vote f x y = φ x then (1 : ℝ) else 0) ≤
          𝔼 y, if f x + f y ≠ f (x + y) then (1 : ℝ) else 0 := by
        refine expect_le_expect fun y _ => ?_
        by_cases hv : vote f x y = φ x
        · have hn : f x + f y ≠ f (x + y) := by
            intro he
            apply hx
            rw [← hv]
            dsimp [vote]
            rw [← he, add_sub_cancel_right]
          simp [hv, hn]
        · simp only [hv, ite_false]
          positivity
      simp only [hx, ne_eq, not_false_eq_true, ite_true, mul_one]
      linarith
  have h := expect_le_expect (s := univ) fun x _ => point x
  rw [← mul_expect, ← hammingDist_div_eq_expect, ← rejection_eq_expect] at h
  linarith

open Classical in
/-- Disagreement only at the first query, among `x`, `y`, and `x + y`. -/
@[expose] def OnlyFirstDisagreement (f : G → H) (h : G →+ H) (x y : G) : Prop :=
  f x ≠ h x ∧ f y = h y ∧ f (x + y) = h (x + y)

open Classical in
private theorem disagreement_moments (f : G → H) (h : G →+ H) :
    let a := fun x => if f x ≠ h x then (1 : ℝ) else 0
    let d := (hammingDist f h : ℝ) / Fintype.card G
    (𝔼 x : G, 𝔼 _y : G, a x) = d ∧ (𝔼 _x : G, 𝔼 y : G, a y) = d ∧
    (𝔼 x : G, 𝔼 y : G, a (x + y)) = d ∧
    (𝔼 x : G, 𝔼 y : G, a x * a y) = d ^ 2 ∧
    (𝔼 x : G, 𝔼 y : G, a x * a (x + y)) = d ^ 2 ∧
    (𝔼 x : G, 𝔼 y : G, a y * a (x + y)) = d ^ 2 := by
  classical
  dsimp only
  let a := fun x => if f x ≠ h x then (1 : ℝ) else 0
  have hd : (𝔼 x, a x) = (hammingDist f h : ℝ) / Fintype.card G :=
    (hammingDist_div_eq_expect f h).symm
  have hab : (𝔼 x : G, 𝔼 y : G, a x * a y) = (𝔼 x, a x) ^ 2 := by
    simp_rw [← mul_expect, ← expect_mul]
    ring
  have hac : (𝔼 x : G, 𝔼 y : G, a x * a (x + y)) = (𝔼 x, a x) ^ 2 := by
    simp_rw [← mul_expect, Fintype.expect_add_left, ← expect_mul]
    ring
  have hbc : (𝔼 x : G, 𝔼 y : G, a y * a (x + y)) = (𝔼 x, a x) ^ 2 := by
    rw [expect_comm]
    simp_rw [add_comm, ← mul_expect, Fintype.expect_add_left, ← expect_mul]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.expect_const] using hd
  · simpa only [Fintype.expect_const] using hd
  · change (𝔼 x : G, 𝔼 y : G, a (x + y)) = _
    simpa only [Fintype.expect_add_left, Fintype.expect_const] using hd
  · exact hab.trans (congrArg (· ^ 2) hd)
  · exact hac.trans (congrArg (· ^ 2) hd)
  · exact hbc.trans (congrArg (· ^ 2) hd)

open Classical in
/-- Goldreich r5 Exercise 9.20(2), for any supplied homomorphism, not just a closest one. -/
theorem disagreement_sub_two_sq_le_onlyFirst (f : G → H) (h : G →+ H) :
    let d := (hammingDist f h : ℝ) / Fintype.card G
    d - 2 * d ^ 2 ≤
      𝔼 x : G, 𝔼 y : G, if OnlyFirstDisagreement f h x y then (1 : ℝ) else 0 := by
  classical
  obtain ⟨ha, _, _, hab, hac, _⟩ := disagreement_moments f h
  have point (x y : G) :
      (if f x ≠ h x then (1 : ℝ) else 0) -
        (if f x ≠ h x then 1 else 0) * (if f y ≠ h y then 1 else 0) -
        (if f x ≠ h x then 1 else 0) * (if f (x + y) ≠ h (x + y) then 1 else 0) ≤
      if OnlyFirstDisagreement f h x y then 1 else 0 := by
    dsimp [OnlyFirstDisagreement]
    split_ifs <;> simp_all
  have hp := expect_le_expect (s := univ) fun x _ =>
    expect_le_expect (s := univ) fun y _ => point x y
  simp only [expect_sub_distrib] at hp
  dsimp only at ha hab hac
  rw [ha, hab, hac] at hp
  dsimp only
  linarith

open Classical in
/-- Goldreich r5 Exercise 9.20(1): rejection dominates three times the first-only event.
Nearestness is unnecessary: all three exactly-one events have the same probability, since
individual disagreement means are `d`, pairwise means are `d²`, and the triple term is shared. -/
theorem three_mul_onlyFirst_le_rejection (f : G → H) (h : G →+ H) :
    3 * (𝔼 x : G, 𝔼 y : G,
      if OnlyFirstDisagreement f h x y then (1 : ℝ) else 0) ≤ rejection f := by
  classical
  let a := fun x => if f x ≠ h x then (1 : ℝ) else 0
  have point (x y : G) :
      3 * (if OnlyFirstDisagreement f h x y then (1 : ℝ) else 0) ≤
        (if f x + f y ≠ f (x + y) then 1 else 0) +
        2 * a x - a y - a (x + y) - a x * a y - a x * a (x + y) +
        2 * (a y * a (x + y)) := by
    have hm := h.map_add x y
    dsimp [a, OnlyFirstDisagreement]
    by_cases hx : f x = h x <;> by_cases hy : f y = h y <;>
      by_cases hz : f (x + y) = h (x + y) <;>
      by_cases hr : f x + f y = f (x + y) <;>
      simp_all only [not_true_eq_false, not_false_eq_true, ite_true, ite_false,
        and_self, false_and, and_false,
        add_left_cancel_iff, add_right_cancel_iff] <;> norm_num
  have hp := expect_le_expect (s := univ) fun x _ =>
    expect_le_expect (s := univ) fun y _ => point x y
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := disagreement_moments f h
  change (𝔼 x : G, 𝔼 y : G, a x) = _ at ha
  change (𝔼 x : G, 𝔼 y : G, a y) = _ at hb
  change (𝔼 x : G, 𝔼 y : G, a (x + y)) = _ at hc
  change (𝔼 x : G, 𝔼 y : G, a x * a y) = _ at hab
  change (𝔼 x : G, 𝔼 y : G, a x * a (x + y)) = _ at hac
  change (𝔼 x : G, 𝔼 y : G, a y * a (x + y)) = _ at hbc
  have pull (b : G → G → ℝ) (c : ℝ) :
      (𝔼 x, 𝔼 y, c * b x y) = c * (𝔼 x, 𝔼 y, b x y) := by
    simp_rw [← mul_expect]
  simp only [expect_add_distrib, expect_sub_distrib] at hp
  rw [pull _ 3, pull _ 2, pull _ 2] at hp
  rw [ha, hb, hc, hab, hac, hbc, ← rejection_eq_expect] at hp
  linarith

open Classical in
/-- The quadratic rejection bound at the actual disagreement with any homomorphism. -/
theorem three_mul_disagreement_sub_six_sq_le_rejection (f : G → H) (h : G →+ H) :
    let d := (hammingDist f h : ℝ) / Fintype.card G
    3 * d - 6 * d ^ 2 ≤ rejection f := by
  have h₁ := disagreement_sub_two_sq_le_onlyFirst f h
  have h₂ := three_mul_onlyFirst_le_rejection f h
  dsimp only at *
  linarith

variable [Fintype H]

open Classical in
omit [Fintype H] in
/-- A closest additive homomorphism exists, including for trivial groups. -/
theorem exists_closest [Finite H] (f : G → H) : ∃ h : G →+ H,
    ∀ k : G →+ H, hammingDist f h ≤ hammingDist f k := by
  classical
  let := Fintype.ofFinite H
  let : Fintype (G →+ H) := Fintype.ofInjective (fun h : G →+ H => (h : G → H))
    DFunLike.coe_injective
  obtain ⟨h, -, hh⟩ := univ.exists_min_image (fun h : G →+ H => hammingDist f h)
    (show (univ : Finset (G →+ H)).Nonempty from ⟨0, mem_univ _⟩)
  exact ⟨h, fun k => hh k (mem_univ _)⟩

open Classical in
/-- Minimum normalized disagreement with an additive homomorphism. -/
noncomputable def distance (f : G → H) : ℝ :=
  (hammingDist f (exists_closest f).choose : ℝ) / Fintype.card G

open Classical in
/-- The minimum distance is attained by a bundled homomorphism. -/
theorem distance_attained (f : G → H) : ∃ h : G →+ H,
    distance f = (hammingDist f h : ℝ) / Fintype.card G :=
  ⟨(exists_closest f).choose, rfl⟩

open Classical in
/-- The minimum distance is bounded by disagreement with any homomorphism. -/
theorem distance_le (f : G → H) (h : G →+ H) :
    distance f ≤ (hammingDist f h : ℝ) / Fintype.card G := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast (exists_closest f).choose_spec h) (Nat.cast_nonneg _)

open Classical in
/-- Goldreich Exercise 9.21: rejection is at least `min (1/6) (δ/2)`. -/
theorem min_le_rejection (f : G → H) : min (1 / 6) (distance f / 2) ≤ rejection f := by
  by_cases hε : rejection f < 1 / 6
  · obtain ⟨φ, hφ⟩ := exists_plurality f
    have hd := (distance_le f (correction f hφ hε)).trans (closeness f hφ hε)
    exact (min_le_right _ _).trans (by linarith)
  · exact (min_le_left _ _).trans (le_of_not_gt hε)

open Classical in
/-- Goldreich r5 Exercise 9.20: the unconditional quadratic bound at minimum distance. -/
theorem three_mul_distance_sub_six_sq_le_rejection (f : G → H) :
    3 * distance f - 6 * distance f ^ 2 ≤ rejection f := by
  obtain ⟨h, hh⟩ := distance_attained f
  rw [hh]
  exact three_mul_disagreement_sub_six_sq_le_rejection f h

end Cslib.HomomorphismTesting
