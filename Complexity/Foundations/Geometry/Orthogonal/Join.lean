/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Isolation
import Mathlib.Data.List.Nodup

/-!
# Gluing local and exterior incidence routes

Two simple orthogonal routes can be joined at a common endpoint when their full real supports
intersect only there. The joined route is again simple and orthogonal; existing subdivision
lemmas identify its support, final endpoint, segment list, and Manhattan wire length.

## Main results

* `head_mem_segment_endpoint`, `last_mem_segment_endpoint`: an endpoint of a simple route
  can occur on a segment only as a segment endpoint.
* `isOrthogonal_join`, `isSimple_join`: geometric correctness of endpoint gluing.

## References

These finite polygonal-route gluing lemmas and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


/-- A simple route's initial listed vertex can lie on one of its segments only as an endpoint.
-/
theorem head_mem_segment_endpoint {r : Route} (hs : IsSimple r) {p : Point}
    (hp : r.head? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hm : realPoint p ∈ segment e.1 e.2) : p = e.1 ∨ p = e.2 := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hp
  cases tail with
  | nil => simp [List.consecutivePairs] at he
  | cons b tail =>
    have heq := segment_eq_first_of_head_mem hs he hm
    exact Or.inl (congrArg (fun e : Point × Point => e.1) heq).symm

/-- A simple route's final listed vertex can lie on one of its segments only as an endpoint.
-/
theorem last_mem_segment_endpoint {r : Route} (hs : IsSimple r) {p : Point}
    (hp : r.getLast? = some p) {e : Point × Point} (he : e ∈ r.consecutivePairs)
    (hm : realPoint p ∈ segment e.1 e.2) : p = e.1 ∨ p = e.2 := by
  induction r with
  | nil => simp at hp
  | cons a r ih =>
    cases r with
    | nil => simp [List.consecutivePairs] at he
    | cons b r =>
      have hp' : (b :: r).getLast? = some p := by
        simpa only [List.getLast?_cons_cons] using hp
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · have ht : realPoint p ∈ support (b :: r) :=
          Or.inl ⟨p, List.mem_of_getLast? hp', rfl⟩
        exact Or.inr (realPoint_injective (first_segment_tail_contact hs hm ht))
      · exact ih hs.of_cons hp' he

/-- Joining properly orthogonal routes at their common listed endpoint remains orthogonal. -/
theorem isOrthogonal_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p)
    (hoq : IsOrthogonal q) (hor : IsOrthogonal r) : IsOrthogonal (q ++ r.tail) := by
  intro e he
  rw [consecutivePairs_join hq hr, List.mem_append] at he
  exact he.elim (hoq e) (hor e)

/-- Joining simple routes whose only continuous intersection is their common endpoint
introduces neither repeated listed points nor forbidden segment contacts. -/
theorem isSimple_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p)
    (hsq : IsSimple q) (hsr : IsSimple r)
    (hc : ∀ z ∈ support q, z ∈ support r → z = realPoint p) :
    IsSimple (q ++ r.tail) := by
  have hrnot : p ∉ r.tail := by
    obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hr
    exact (List.nodup_cons.mp hsr.1).1
  have hnd : (q ++ r.tail).Nodup := by
    refine List.nodup_append.mpr ⟨hsq.1, hsr.1.tail, ?_⟩
    intro x hx y hy heq
    subst y
    have hz := hc (realPoint x) (Or.inl ⟨x, hx, rfl⟩)
      (Or.inl ⟨x, List.mem_of_mem_tail hy, rfl⟩)
    exact hrnot (realPoint_injective hz ▸ hy)
  have hcross (e : Point × Point) (he : e ∈ q.consecutivePairs)
      (f : Point × Point) (hf : f ∈ r.consecutivePairs) :
      EndpointContacts e.1 e.2 f.1 f.2 := by
    intro z hz hz'
    have hzp := hc z (Or.inr ⟨e, he, hz⟩) (Or.inr ⟨f, hf, hz'⟩)
    have hep := last_mem_segment_endpoint hsq hq he (hzp ▸ hz)
    have hfp := head_mem_segment_endpoint hsr hr hf (hzp ▸ hz')
    constructor
    · rcases hep with hep | hep
      · exact Or.inl (hzp.trans (congrArg realPoint hep))
      · exact Or.inr (hzp.trans (congrArg realPoint hep))
    · rcases hfp with hfp | hfp
      · exact Or.inl (hzp.trans (congrArg realPoint hfp))
      · exact Or.inr (hzp.trans (congrArg realPoint hfp))
  refine ⟨hnd, ?_⟩
  intro e he f hf hne
  rw [consecutivePairs_join hq hr, List.mem_append] at he hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact hsq.2 e he f hf hne
  · exact hcross e he f hf
  · exact (hcross f hf e he).symm
  · exact hsr.2 e he f hf hne

end Cslib.Orthogonal
