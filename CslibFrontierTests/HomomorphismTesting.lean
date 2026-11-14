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
