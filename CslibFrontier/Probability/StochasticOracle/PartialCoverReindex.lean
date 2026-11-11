/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverRisk
import Mathlib.Tactic

/-!
# Injective labels for partial-cover candidates

Retain the original ground, weights and dual prices when restricting candidate
labels along an embedding. This connects actual finite native masks to the
natural indices of the original runtime WSC system.

## Main results

* `reindex_covered`, `reindex_cost`: coverage and cost preserve original meaning.
* `reindex_retain`: all local decisions and the complete retained family commute with labeling.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover.Instance
variable {E J K : Type} [DecidableEq E] [DecidableEq J] [DecidableEq K]

/-- The same original instance restricted to the injectively labeled candidates. -/
@[expose] def reindex (I : Instance E J) (f : K ↪ J) : Instance E K where
  ground := I.ground
  sets k := I.sets (f k)
  sets_subset k := I.sets_subset (f k)
  weight k := I.weight (f k)
  weight_nonneg k := I.weight_nonneg (f k)
  dual := I.dual
  dual_nonneg := I.dual_nonneg
  dual_feasible k := I.dual_feasible (f k)

omit [DecidableEq K] in
/-- Candidate relabeling preserves coverage of the original elements. -/
theorem reindex_covered (I : Instance E J) (f : K ↪ J) (C : Finset K) :
    (I.reindex f).covered C = I.covered (C.image f) := by
  exact (Finset.image_biUnion (f := f) (s := C) (t := I.sets)).symm

omit [DecidableEq K] in
/-- Injective labels count every retained original candidate's weight exactly once. -/
theorem reindex_cost (I : Instance E J) (f : K ↪ J) (C : Finset K) :
    (I.reindex f).cost C = I.cost (C.image f) := by
  simp only [cost, reindex]
  exact (Finset.sum_image (fun _ _ _ _ h => f.injective h)).symm

omit [DecidableEq K] in
/-- The local certification decision has exactly the original meaning. -/
theorem reindex_certified (I : Instance E J) (f : K ↪ J) (ρ : ℝ) (C P : Finset K) :
    (I.reindex f).Certified ρ C P ↔ I.Certified ρ (C.image f) (P.image f) := by
  unfold Certified
  rw [reindex_covered, reindex_covered, reindex_cost]
  rfl

/-- Complete chronological local retention is preserved, not merely final coverage. -/
theorem reindex_retain (I : Instance E J) (f : K ↪ J) (ρ : ℝ)
    (C : Finset K) (ps : List (Finset K)) :
    ((I.reindex f).retain ρ C ps).image f =
      I.retain ρ (C.image f) (ps.map fun P => P.image f) := by
  classical
  induction ps generalizing C with
  | nil => rfl
  | cons P ps ih =>
    simp only [retain, List.map_cons]
    by_cases hc : (I.reindex f).Certified ρ C P
    · rw [ite_eq_left hc, ih, Finset.image_union,
        ite_eq_left ((reindex_certified I f ρ C P).mp hc)]
    · rw [ite_eq_right hc, ih,
        ite_eq_right (fun h => hc ((reindex_certified I f ρ C P).mpr h))]

/-- Canceled or malformed reports contribute the empty family; processing these
empty entries is exactly the same as omitting absent proposals. -/
theorem retain_options (I : Instance E J) (ρ : ℝ) (C : Finset J)
    (ps : List (Option (Finset J))) :
    I.retain ρ C (ps.map fun P => P.getD ∅) = I.retain ρ C (ps.filterMap id) := by
  classical
  induction ps generalizing C with
  | nil => rfl
  | cons P ps ih =>
    cases P with
    | none => simp [retain, Certified, covered, ih]
    | some P => simpa only [List.map_cons, List.filterMap_cons, Option.getD_some,
        id_eq, retain] using ih (if I.Certified ρ C P then C ∪ P else C)

omit [DecidableEq K] in
/-- Injective element relabeling preserves each element's eligible-call count. -/
theorem chances_image (f : E ↪ J) (e : E) (vs : List (Finset E)) :
    chances (f e) (vs.map fun V => V.image f) = chances e vs := by
  induction vs with
  | nil => rfl
  | cons V vs ih =>
    simp only [chances] at ih
    by_cases he : e ∈ V <;>
      simp [chances, he, Finset.mem_image, f.injective.eq_iff, ih]

end Cslib.Probability.StochasticOracle.PartialCover.Instance
