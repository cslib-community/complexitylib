/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent.Incidence
import Mathlib.Tactic.Linarith

/-!
# Collision moments suffice for balanced incidence labels

The incidence potential only uses collisions of two edges. Consequently a finite family of
labelings has the same expected potential as independent uniform vertex labels whenever it
has the same two-edge collision averages. This gives a good member of the family without a
sequential conditional-expectation pass over all vertices.

A four-wise independent labeling of the disjoint union of the two vertex sets satisfies the
collision hypothesis: each test uses at most four distinct vertices. This module proves the
transfer from the collision hypothesis, not the construction of such a family, its seed length,
or a machine for finding or verifying a seed. Repeated endpoints must use the same label.
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

variable {E R C L S : Type*} [Fintype E] [Finite R] [DecidableEq R]
  [Finite C] [DecidableEq C] [Fintype L] [DecidableEq L] [Nonempty L]
  [Fintype S] [Nonempty S]

omit [Finite R] [Finite C] in
/-- Matching the collision averages of independent vertex labels preserves the entire expected
incidence potential, including collisions between edges with shared endpoints. -/
theorem expect_incidence_potential_eq_of_collision [Fintype R] [Fintype C]
    (rowOf : E → R) (colOf : E → C) (rowLabel : S → R → L) (colLabel : S → C → L)
    (hcollision : ∀ e e',
      (𝔼 s, if incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e =
          incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e' then (1 : ℚ) else 0) =
        (if rowOf e = rowOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
          (if colOf e = colOf e' then 1 else 1 / (Fintype.card L : ℚ))) :
    (𝔼 s, potential (incidenceLabel rowOf colOf (rowLabel s) (colLabel s))) =
      𝔼 ρ : R → L, 𝔼 κ : C → L, potential (incidenceLabel rowOf colOf ρ κ) := by
  simp_rw [potential_eq_collisions_sub]
  simp only [Finset.expect_sub_distrib, Fintype.expect_const]
  simp_rw [Finset.expect_sum_comm, hcollision, expect_incidenceLabel_collision]

/-- The degree-based expected-potential bound needs only the two-edge collision moments. -/
theorem expect_incidence_potential_le_of_collision
    (rowOf : E → R) (colOf : E → C) (rowLabel : S → R → L) (colLabel : S → C → L)
    (hcollision : ∀ e e',
      (𝔼 s, if incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e =
          incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e' then (1 : ℚ) else 0) =
        (if rowOf e = rowOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
          (if colOf e = colOf e' then 1 else 1 / (Fintype.card L : ℚ)))
    {b w : ℕ} (hrow : ∀ e, #{e' | rowOf e' = rowOf e} ≤ b)
    (hcol : ∀ e, #{e' | colOf e' = colOf e} ≤ w) :
    (𝔼 s, potential (incidenceLabel rowOf colOf (rowLabel s) (colLabel s))) ≤
      (Fintype.card E : ℚ) * (b + w) := by
  let := Fintype.ofFinite R
  let := Fintype.ofFinite C
  rw [expect_incidence_potential_eq_of_collision rowOf colOf rowLabel colLabel hcollision]
  exact expect_incidence_potential_le rowOf colOf hrow hcol

/-- One seed simultaneously bounds every label-pair occupancy. This is an existence result:
the seed family and its collision moments are supplied, and no selection cost is claimed. -/
theorem exists_occupancy_le_of_collision
    (rowOf : E → R) (colOf : E → C) (rowLabel : S → R → L) (colLabel : S → C → L)
    (hcollision : ∀ e e',
      (𝔼 s, if incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e =
          incidenceLabel rowOf colOf (rowLabel s) (colLabel s) e' then (1 : ℚ) else 0) =
        (if rowOf e = rowOf e' then 1 else 1 / (Fintype.card L : ℚ)) *
          (if colOf e = colOf e' then 1 else 1 / (Fintype.card L : ℚ)))
    {Δ : ℕ} (hrow : ∀ e, #{e' | rowOf e' = rowOf e} ≤ Δ)
    (hcol : ∀ e, #{e' | colOf e' = colOf e} ≤ Δ)
    (hsize : 2 * Δ * Fintype.card (L × L) ^ 2 ≤ Fintype.card E) :
    ∃ s, ∀ γ, occupancy (incidenceLabel rowOf colOf (rowLabel s) (colLabel s)) γ *
      Fintype.card (L × L) ≤ 2 * Fintype.card E := by
  obtain ⟨s, hs⟩ := exists_le_expect fun s =>
    potential (incidenceLabel rowOf colOf (rowLabel s) (colLabel s))
  have hbound := hs.trans
    (expect_incidence_potential_le_of_collision rowOf colOf rowLabel colLabel hcollision hrow hcol)
  refine ⟨s, fun γ => occupancy_mul_card_le_of_variance_bound _ Δ ?_ hsize γ⟩
  nlinarith

omit [Nonempty S] in
/-- Four-wise independent labels on tagged vertices admit one simultaneously balanced seed.
The entire seed is shared by every incidence query; this theorem does not resample labels
when an edge or endpoint is queried again. -/
theorem exists_occupancy_le_of_fourWise
    (rowOf : E → R) (colOf : E → C) {label : S → R ⊕ C → L}
    (hlabel : Cslib.Probability.IsKWiseIndependentHash 4 label)
    {Δ : ℕ} (hrow : ∀ e, #{e' | rowOf e' = rowOf e} ≤ Δ)
    (hcol : ∀ e, #{e' | colOf e' = colOf e} ≤ Δ)
    (hsize : 2 * Δ * Fintype.card (L × L) ^ 2 ≤ Fintype.card E) :
    ∃ s, ∀ γ, occupancy (incidenceLabel rowOf colOf
      (fun r => label s (.inl r)) (fun c => label s (.inr c))) γ *
        Fintype.card (L × L) ≤ 2 * Fintype.card E := by
  let := Fintype.ofFinite R
  let := Fintype.ofFinite C
  have := hlabel.nonempty
  exact exists_occupancy_le_of_collision rowOf colOf
    (fun s r => label s (.inl r)) (fun s c => label s (.inr c))
    (hlabel.expect_incidence_collision rowOf colOf) hrow hcol hsize

end Cslib.BalancedSchedules
