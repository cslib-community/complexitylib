/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Local dual certification of partial oracle responses

[Wang2027], Section 5, Lemma 1 (PDF p. 9), proof in Appendix A.3
(PDF p. 15). `retain` processes the actual returned subfamilies in order,
accepting exactly those with nonempty new coverage whose weight passes the
local dual test. Repeated sets are billed only once in the assembled cover.
The dual vector is nonnegative and feasible for every original set; the
comparison is with every integral cover, without assuming an LP optimizer.

This deterministic certification lemma applies pathwise to arbitrary response
laws. It does not establish Theorem 4's probability, greedy approximation,
runtime or hardness claims.

## Main results

* `retain_bound`: accumulated weight is bounded by the dual charge of covered elements.
* `retain_cover_bound`: every completed retained cover has the advertised weight guarantee.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover
open Finset
variable {E J : Type*} [DecidableEq E] [DecidableEq J]

/-- A weighted set system on a finite universe, together with a feasible set-cover dual. -/
structure Instance (E J : Type*) [DecidableEq E] where
  /-- Elements that must be covered. -/
  ground : Finset E
  /-- Original sets, restricted to the universe. -/
  sets : J → Finset E
  /-- Every original set is a subset of the universe. -/
  sets_subset : ∀ j, sets j ⊆ ground
  /-- Nonnegative original set weights. -/
  weight : J → ℝ
  /-- Nonnegativity permits repeated responses without repeated billing. -/
  weight_nonneg : ∀ j, 0 ≤ weight j
  /-- Nonnegative dual element prices. -/
  dual : E → ℝ
  /-- Dual prices are nonnegative, including on uncovered elements. -/
  dual_nonneg : ∀ e, 0 ≤ dual e
  /-- Dual feasibility for every original set. -/
  dual_feasible : ∀ j, ∑ e ∈ sets j, dual e ≤ weight j

namespace Instance

variable (I : Instance E J)

/-- Elements covered by a returned or retained subfamily. -/
@[expose] def covered (C : Finset J) : Finset E := C.biUnion I.sets

/-- Weight of a subfamily, counting each original set once. -/
@[expose] def cost (C : Finset J) : ℝ := ∑ j ∈ C, I.weight j

/-- Local dual test at the current retained family. -/
@[expose] def Certified (ρ : ℝ) (C P : Finset J) : Prop :=
  (I.covered P \ I.covered C).Nonempty ∧
    I.cost P ≤ ρ * ∑ e ∈ I.covered P \ I.covered C, I.dual e

open scoped Classical in
/-- Process responses in order, retaining a response exactly when it passes the local test. -/
@[expose] noncomputable def retain (I : Instance E J) (ρ : ℝ) :
    Finset J → List (Finset J) → Finset J
  | C, [] => C
  | C, P :: ps => I.retain ρ (if I.Certified ρ C P then C ∪ P else C) ps

/-- Coverage respects unions of original subfamilies. -/
theorem covered_union (C P : Finset J) :
    I.covered (C ∪ P) = I.covered C ∪ I.covered P := by
  ext e
  simp only [covered, mem_biUnion, mem_union]
  aesop

omit [DecidableEq J] in
/-- All covered elements belong to the original universe. -/
theorem covered_subset (C : Finset J) : I.covered C ⊆ I.ground := by
  intro e he
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp he
  exact I.sets_subset j hj

omit [DecidableEq J] in
/-- Weak set-cover duality, allowing arbitrary overlap and repeated responses. -/
theorem dual_le_cost (C : Finset J) :
    (∑ e ∈ I.covered C, I.dual e) ≤ I.cost C := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [covered, cost]
  | @insert j C hj ih =>
    have hsum := sum_union_inter (s₁ := I.sets j) (s₂ := I.covered C) (f := I.dual)
    have hn : 0 ≤ ∑ e ∈ I.sets j ∩ I.covered C, I.dual e :=
      sum_nonneg fun e _ => I.dual_nonneg e
    have hcov : I.covered (insert j C) = I.sets j ∪ I.covered C := by
      ext e
      simp [covered]
    rw [hcov, cost, sum_insert hj]
    have hd := I.dual_feasible j
    change (∑ e ∈ I.covered C, I.dual e) ≤ ∑ k ∈ C, I.weight k at ih
    linarith

/-- A successful local test preserves the accumulated dual-charge invariant. -/
theorem certified_union_bound {ρ : ℝ} {C P : Finset J}
    (hC : I.cost C ≤ ρ * ∑ e ∈ I.covered C, I.dual e)
    (hP : I.Certified ρ C P) :
    I.cost (C ∪ P) ≤ ρ * ∑ e ∈ I.covered (C ∪ P), I.dual e := by
  have hcost := sum_union_inter (s₁ := C) (s₂ := P) (f := I.weight)
  have hn : 0 ≤ ∑ j ∈ C ∩ P, I.weight j :=
    sum_nonneg fun j _ => I.weight_nonneg j
  have hcharge := sum_sdiff (f := I.dual) (subset_union_left : I.covered C ⊆
    I.covered C ∪ I.covered P)
  have hd : (I.covered C ∪ I.covered P) \ I.covered C =
      I.covered P \ I.covered C := by ext e; simp; tauto
  rw [hd] at hcharge
  rw [covered_union]
  have hp := hP.2
  unfold cost at *
  rw [← hcharge, mul_add]
  linarith

/-- Local retention never introduces a candidate absent from the starting family
and the actually proposed families. Extracted from the selection-policy client. -/
theorem retain_subset (ρ : ℝ) (C : Finset J) (ps : List (Finset J)) :
    I.retain ρ C ps ⊆ C ∪ ps.foldr (· ∪ ·) ∅ := by
  classical
  induction ps generalizing C with
  | nil => simp [Instance.retain]
  | cons P ps ih =>
    simp only [Instance.retain]
    split_ifs
    · simpa only [List.foldr_cons, union_assoc] using ih (C ∪ P)
    · exact (ih C).trans (by intro j hj; simp only [mem_union, List.foldr_cons] at *; tauto)

/-- Any starting invariant is preserved by the actual accept/reject processing loop. -/
theorem retain_bound {ρ : ℝ} (ps : List (Finset J)) (C : Finset J)
    (hC : I.cost C ≤ ρ * ∑ e ∈ I.covered C, I.dual e) :
    I.cost (I.retain ρ C ps) ≤ ρ * ∑ e ∈ I.covered (I.retain ρ C ps), I.dual e := by
  classical
  induction ps generalizing C with
  | nil => exact hC
  | cons P ps ih =>
    simp only [retain]
    split_ifs with hP
    · exact ih _ (I.certified_union_bound hC hP)
    · exact ih _ hC

/-- Lemma 1: if retained responses cover the universe, their union costs at most
`ρ` times the feasible dual objective and hence at most `ρ` times every integral cover.
No assertion about the probability of completion is assumed or concluded here. -/
theorem retain_cover_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (ps : List (Finset J))
    (hcomplete : I.covered (I.retain ρ ∅ ps) = I.ground)
    (C : Finset J) (hC : I.covered C = I.ground) :
    I.cost (I.retain ρ ∅ ps) ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
      ρ * (∑ e ∈ I.ground, I.dual e) ≤ ρ * I.cost C := by
  have h := I.retain_bound ps ∅ (ρ := ρ) (by simp [cost, covered])
  rw [hcomplete] at h
  refine ⟨h, mul_le_mul_of_nonneg_left ?_ hρ⟩
  rw [← hC]
  exact I.dual_le_cost C

end Instance

end Cslib.Probability.StochasticOracle.PartialCover
