/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Trim
import Mathlib.Tactic.NormNum

/-!
# Distinct exit directions at orthogonal drawing vertices

Two proper integer segments leaving the same vertex in the same cardinal direction overlap
at a nonintegral real point. Thus incidence routes whose contacts are graph vertices must
have distinct directions at any common initial vertex, including parallel listed incidences.

## Main results

* `nonGrid_contact_of_direction_eq`: a common direction forces a nonintegral intersection.
* `direction_ne_of_grid_contacts`: endpoint-only geometric contacts imply distinct exits.

## References

The elementary cardinal-ray separation and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


private theorem cutPoint_two_one_ne_even (a b v : Point) : cutPoint 2 1 a b ≠ 2 • v := by
  have hd := direction_unit a b
  rcases a with ⟨ax, ay⟩
  rcases v with ⟨vx, vy⟩
  intro h
  rcases hd with hd | hd | hd | hd
  all_goals
    simp only [cutPoint, hd, one_smul, Prod.smul_mk, Int.nsmul_eq_mul,
      Prod.mk_add_mk, Prod.mk.injEq] at h
    omega

/-- Equal cardinal directions force a common point that is not an integer grid point. -/
theorem nonGrid_contact_of_direction_eq {a b c : Point}
    (hab : AxisAligned a b) (hac : AxisAligned a c) (hd : direction a b = direction a c) :
    ∃ p ∈ segment a b, p ∈ segment a c ∧ ∀ v : Point, p ≠ realPoint v := by
  let q := cutPoint 2 1 a b
  let p : ℝ × ℝ := (1 / 2 : ℝ) • realPoint q
  have he : (2 : ℝ) • p = realPoint q := by
    dsimp only [p]
    rw [smul_smul]
    norm_num
  have hq₁ : realPoint q ∈ segment (2 • a) (2 • b) :=
    cutPoint_mem_segment hab (by decide)
  have hq₂ : realPoint q ∈ segment (2 • a) (2 • c) := by
    have heq : cutPoint 2 1 a b = cutPoint 2 1 a c := by simp only [cutPoint, hd]
    change realPoint (cutPoint 2 1 a b) ∈ segment (2 • a) (2 • c)
    rw [heq]
    exact cutPoint_mem_segment hac (by decide)
  have hp₁ : p ∈ segment a b := (mem_segment_nsmul_iff (by decide : 2 ≠ 0) a b p).1
    (by simpa only [Nat.cast_ofNat, he] using hq₁)
  have hp₂ : p ∈ segment a c := (mem_segment_nsmul_iff (by decide : 2 ≠ 0) a c p).1
    (by simpa only [Nat.cast_ofNat, he] using hq₂)
  refine ⟨p, hp₁, hp₂, ?_⟩
  intro v hv
  have hv' : realPoint q = realPoint (2 • v) := by
    rw [← he, hv, realPoint_nsmul]
    norm_num
  exact cutPoint_two_one_ne_even a b v (realPoint_injective hv')

/-- If common segment points must be integer graph vertices, two incidences cannot leave
their shared initial vertex in the same direction. -/
theorem direction_ne_of_grid_contacts {a b c : Point}
    (hab : AxisAligned a b) (hac : AxisAligned a c)
    (hc : ∀ p ∈ segment a b, p ∈ segment a c → ∃ v : Point, p = realPoint v) :
    direction a b ≠ direction a c := by
  intro hd
  obtain ⟨p, hp, hq, hng⟩ := nonGrid_contact_of_direction_eq hab hac hd
  obtain ⟨v, hv⟩ := hc p hp hq
  exact hng v hv

end Cslib.Orthogonal
