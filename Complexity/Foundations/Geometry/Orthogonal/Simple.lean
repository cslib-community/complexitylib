/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal

/-!
# Continuous simplicity certificates for finite polygonal routes

## Main definitions

* `Cslib.Orthogonal.EndpointContacts`: every continuous segment intersection is a common endpoint.
* `Cslib.Orthogonal.IsSimple`: no repeated listed points, and distinct consecutive segments have
  only common endpoint contacts. In conjunction with proper segments, this excludes retracing,
  self-crossings, and contacts between nonadjacent segments.

## References

The finite-route simplicity certificate and elementary proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- Two continuous closed segments contact only at common endpoints. -/
def EndpointContacts (a b c d : Point) : Prop :=
  ∀ p ∈ segment a b, p ∈ segment c d →
    (p = realPoint a ∨ p = realPoint b) ∧ (p = realPoint c ∨ p = realPoint d)

/-- Interchanging the two segments preserves the contact certificate. -/
theorem EndpointContacts.symm {a b c d : Point} (h : EndpointContacts a b c d) :
    EndpointContacts c d a b := fun p hp hq => (h p hq hp).symm

/-- Reversing one segment preserves the contact certificate. -/
theorem EndpointContacts.reverse_left {a b c d : Point} (h : EndpointContacts a b c d) :
    EndpointContacts b a c d := by
  intro p hp hq
  rw [segment, segment_symm] at hp
  exact ⟨(h p hp hq).1.symm, (h p hp hq).2⟩

/-- Reversing one segment preserves the contact certificate. -/
theorem EndpointContacts.reverse_right {a b c d : Point} (h : EndpointContacts a b c d) :
    EndpointContacts a b d c := h.symm.reverse_left.symm

/-- Disjoint segments have no non-endpoint contacts. -/
theorem endpointContacts_of_disjoint {a b c d : Point}
    (h : Disjoint (segment a b) (segment c d)) : EndpointContacts a b c d :=
  fun _ hp hq => False.elim (Set.disjoint_left.1 h hp hq)

/-- A finite polygonal route with no repeated listed points and only common-endpoint contacts
between distinct segments. All contacts are tested in the real plane. -/
def IsSimple (r : Route) : Prop :=
  r.Nodup ∧ ∀ e ∈ r.consecutivePairs, ∀ f ∈ r.consecutivePairs,
    e ≠ f → EndpointContacts e.1 e.2 f.1 f.2

/-- Removing the initial listed point preserves continuous simplicity. -/
theorem IsSimple.of_cons {a : Point} {r : Route} (h : IsSimple (a :: r)) : IsSimple r := by
  cases r with
  | nil => simp [IsSimple, List.consecutivePairs]
  | cons b r =>
    refine ⟨h.1.tail, ?_⟩
    intro e he f hf hne
    exact h.2 e (List.mem_cons_of_mem (a, b) he) f (List.mem_cons_of_mem (a, b) hf) hne

end Cslib.Orthogonal
