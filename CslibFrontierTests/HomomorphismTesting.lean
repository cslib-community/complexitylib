/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Foundations.Algebra.Group.HomomorphismTesting
import Mathlib.Data.ZMod.Basic

/-! # Finite abelian homomorphism testing clients -/

open Cslib.HomomorphismTesting
open scoped BigOperators
set_option linter.privateModule false

open Classical in
/-- The non-Boolean group `ZMod 3` passes the test under its identity homomorphism. -/
example : rejection (fun x : ZMod 3 => x) = 0 :=
  rejection_hom (AddMonoidHom.id (ZMod 3))

open Classical in
/-- Both groups may be trivial. -/
example : rejection (fun _ : ZMod 1 => (0 : ZMod 1)) = 0 :=
  rejection_hom (0 : ZMod 1 →+ ZMod 1)

open Classical in
/-- A trivial codomain allows every domain point. -/
example : rejection (fun _ : ZMod 3 => (0 : ZMod 1)) = 0 :=
  rejection_hom (0 : ZMod 3 →+ ZMod 1)

open Classical in
/-- Constant zero works with a trivial domain and an arbitrary finite codomain. -/
example : rejection (fun _ : ZMod 1 => (0 : ZMod 3)) = 0 :=
  rejection_hom (0 : ZMod 1 →+ ZMod 3)

open Classical in
/-- The correction reads `f (x + y)` and `f y`; every plurality satisfies its mass guarantee. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    (f : G → H) : ∃ φ : G → H, ∀ x,
      1 - 2 * rejection f ≤ 𝔼 y, if vote f x y = φ x then (1 : ℝ) else 0 := by
  obtain ⟨φ, hφ⟩ := exists_plurality f
  exact ⟨φ, concentration f hφ⟩

open Classical in
/-- Below the threshold the same correction is a homomorphism with the promised distance. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    (f : G → H) (hε : rejection f < 1 / 6) : ∃ h : G →+ H,
      (hammingDist f h : ℝ) / Fintype.card G ≤ 2 * rejection f := by
  obtain ⟨φ, hφ⟩ := exists_plurality f
  exact ⟨correction f hφ hε, closeness f hφ hε⟩

open Classical in
/-- Conditional threshold coverage uses the public unconditional theorem for general groups. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G → H) (hε : rejection f = 1 / 6) :
    min (1 / 6) (distance f / 2) ≤ (1 / 6 : ℝ) := by
  simpa only [hε] using min_le_rejection f

open Classical in
/-- A function far from every homomorphism has the corresponding rejection guarantee. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G → H) (d : ℝ)
    (hfar : ∀ h : G →+ H, d ≤ (hammingDist f h : ℝ) / Fintype.card G) :
    min (1 / 6) (d / 2) ≤ rejection f := by
  obtain ⟨h, hh⟩ := distance_attained f
  have hd : d ≤ distance f := by simpa [hh] using hfar h
  exact (min_le_min_left _ (div_le_div_of_nonneg_right hd (by norm_num))).trans
    (min_le_rejection f)

open Classical in
/-- Supplied homomorphisms need no optimality certificate or rejection threshold. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    (f : G → H) (h : G →+ H) :
    3 * ((hammingDist f h : ℝ) / Fintype.card G) -
      6 * ((hammingDist f h : ℝ) / Fintype.card G) ^ 2 ≤ rejection f :=
  three_mul_disagreement_sub_six_sq_le_rejection f h

private theorem zmod_four_hom_eq_zero (h : ZMod 4 →+ ZMod 3) : h = 0 := by
  ext x
  have hx : 4 • x = 0 := (show ∀ z : ZMod 4, 4 • z = 0 by decide) x
  have hh : 4 • h x = 0 := by rw [← map_nsmul, hx, map_zero]
  exact (show ∀ z : ZMod 3, 4 • z = 0 → z = 0 by decide) (h x) hh

open Classical in
private theorem distance_zmod_four (f : ZMod 4 → ZMod 3) :
    distance f = (hammingDist f (0 : ZMod 4 →+ ZMod 3) : ℝ) / 4 := by
  obtain ⟨h, hh⟩ := distance_attained f
  rw [zmod_four_hom_eq_zero h] at hh
  convert hh using 1; congr 3

open Classical in
/-- The increasing-range boundary is an actual distance, not a supplied lower bound. -/
private theorem distance_quarter :
    distance (fun x : ZMod 4 => if x = 0 then (1 : ZMod 3) else 0) = 1 / 4 := by
  rw [distance_zmod_four]
  have hd : hammingDist (fun x : ZMod 4 => if x = 0 then (1 : ZMod 3) else 0)
      (0 : ZMod 4 →+ ZMod 3) = 1 := by decide
  rw [hd]
  norm_num

open Classical in
/-- The zero-bound boundary is also attained by a concrete function. -/
private theorem distance_half :
    distance (fun x : ZMod 4 => if x = 0 ∨ x = 1 then (1 : ZMod 3) else 0) =
    1 / 2 := by
  rw [distance_zmod_four]
  have hd : hammingDist
      (fun x : ZMod 4 => if x = 0 ∨ x = 1 then (1 : ZMod 3) else 0)
      (0 : ZMod 4 →+ ZMod 3) = 2 := by decide
  rw [hd]
  norm_num

open Classical in
/-- A genuinely nonadditive function on a non-Boolean group. -/
example : rejection (fun _ : ZMod 3 => (1 : ZMod 3)) = 1 := by
  simp [rejection]

open Classical in
/-- Even with a trivial domain, a nonzero constant rejects everywhere. -/
example : rejection (fun _ : ZMod 1 => (1 : ZMod 3)) = 1 := by
  simp [rejection]

open Classical in
/-- The constant nonzero function has distance one; the quadratic right side is negative. -/
private theorem distance_one : distance (fun _ : ZMod 1 => (1 : ZMod 3)) = 1 := by
  obtain ⟨h, hh⟩ := distance_attained (fun _ : ZMod 1 => (1 : ZMod 3))
  have he : h = 0 := by ext x; have : x = 0 := Subsingleton.elim _ _; simp [this]
  rw [he] at hh
  have hd : hammingDist (fun _ : ZMod 1 => (1 : ZMod 3))
      (0 : ZMod 1 →+ ZMod 3) = 1 := by decide
  have hh' : distance (fun _ : ZMod 1 => (1 : ZMod 3)) =
      (hammingDist (fun _ : ZMod 1 => (1 : ZMod 3))
        (0 : ZMod 1 →+ ZMod 3) : ℝ) / Fintype.card (ZMod 1) := by
    convert hh using 1; congr 3
  simpa [hd] using hh'

open Classical in
/-- A single error on `ZMod 3` gives an exact nonhomomorphic rejection probability. -/
example : rejection (fun x : ZMod 3 => if x = 0 then (1 : ZMod 3) else 0) = 7 / 9 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [rejection, Fintype.expect_prod_type]
  simp +decide [Finset.expect, hu, Finset.sum_insert, Finset.sum_singleton,
    Finset.card_insert_of_notMem]
  norm_num [NNRat.smul_def]

open Classical in
/-- The supplied zero homomorphism directly gives part (2), without event manipulation. -/
example : (1 / 3 : ℝ) - 2 * (1 / 3) ^ 2 ≤
    𝔼 x : ZMod 3, 𝔼 y : ZMod 3,
      if OnlyFirstDisagreement (fun z => if z = 0 then (1 : ZMod 3) else 0) 0 x y
        then (1 : ℝ) else 0 := by
  have hb := disagreement_sub_two_sq_le_onlyFirst
    (fun z : ZMod 3 => if z = 0 then (1 : ZMod 3) else 0) 0
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  dsimp only at hb
  simp +decide [hammingDist, hu, Finset.filter_insert,
    Finset.filter_singleton] at hb
  norm_num at hb ⊢
  simp only [← hu] at hb
  linarith

open Classical in
/-- Part (1) applies without any certificate that the supplied homomorphism is nearest. -/
example {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    (f : G → H) (h : G →+ H) :
    3 * (𝔼 x : G, 𝔼 y : G,
      if OnlyFirstDisagreement f h x y then (1 : ℝ) else 0) ≤ rejection f :=
  three_mul_onlyFirst_le_rejection f h

open Classical in
example : (3 / 8 : ℝ) ≤
    rejection (fun x : ZMod 4 => if x = 0 then (1 : ZMod 3) else 0) := by
  have hb := three_mul_distance_sub_six_sq_le_rejection
    (fun x : ZMod 4 => if x = 0 then (1 : ZMod 3) else 0)
  rw [distance_quarter] at hb
  norm_num at hb ⊢
  exact hb

open Classical in
example : 0 ≤ rejection
    (fun x : ZMod 4 => if x = 0 ∨ x = 1 then (1 : ZMod 3) else 0) := by
  have hb := three_mul_distance_sub_six_sq_le_rejection
    (fun x : ZMod 4 => if x = 0 ∨ x = 1 then (1 : ZMod 3) else 0)
  rw [distance_half] at hb
  norm_num at hb ⊢
  exact hb

open Classical in
example : 3 * distance (fun _ : ZMod 1 => (1 : ZMod 3)) -
    6 * distance (fun _ : ZMod 1 => (1 : ZMod 3)) ^ 2 = -3 := by
  rw [distance_one]
  norm_num
