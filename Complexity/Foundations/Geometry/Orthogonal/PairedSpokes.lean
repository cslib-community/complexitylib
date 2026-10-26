/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.PairedPorts
import Mathlib.Tactic.FinCases

/-!
# Four disjoint offset spokes

A rotational choice of one of the paired ports on each side gives four proper orthogonal
spokes from the center of the square. Distinct spokes meet only at that center. These are
finite certificates about entire real route supports.

## Main definitions

* `Cslib.Orthogonal.PairedPorts.spokeLane`, `.spokeRoute`: selected ports and two-segment spokes.

## Main results

* `Cslib.Orthogonal.PairedPorts.spoke_isSimple`, `.spokes_contact`: simplicity and center-only
  contacts.

## References

The finite offset star is original.
-/

@[expose] public section

namespace Cslib.Orthogonal.PairedPorts

/-- One selected lane on each side, in rotational order around the center. -/
def spokeLane (s : Fin 4) : Fin 2 := if s = 1 ∨ s = 2 then 1 else 0

/-- A spoke first travels toward its bend and then toward its selected boundary point. -/
def spokeElbow (s : Fin 4) : Point :=
  match s with
  | 0 => (120, 110)
  | 1 => (120, 130)
  | 2 => (130, 120)
  | _ => (110, 120)

/-- A two-segment route from the center to the selected side port. -/
def spokeRoute (s : Fin 4) : Route :=
  [(120, 120), spokeElbow s, boundaryPort s (spokeLane s)]

/-- Every spoke is proper and orthogonal with its prescribed endpoints. -/
theorem spoke_endpoints : ∀ s, IsOrthogonal (spokeRoute s) ∧
    (spokeRoute s).head? = some (120, 120) ∧
      (spokeRoute s).getLast? = some (boundaryPort s (spokeLane s)) := by decide +kernel

/-- The two segments of a spoke meet only at their shared bend. -/
theorem spoke_bend_check : ∀ s,
    segmentContactCheck [spokeElbow s] (120, 120) (spokeElbow s)
      (spokeElbow s) (boundaryPort s (spokeLane s)) = true := by decide +kernel

/-- Each spoke is simple over its full real support. -/
theorem spoke_isSimple (s : Fin 4) : IsSimple (spokeRoute s) := by
  have hcontact : EndpointContacts (120, 120) (spokeElbow s) (spokeElbow s)
      (boundaryPort s (spokeLane s)) := by
    intro p hp hq
    obtain ⟨q, hq, heq⟩ := segmentContactCheck_sound (spoke_bend_check s) hp hq
    have hqb := List.mem_singleton.mp hq
    exact ⟨Or.inr (hqb ▸ heq), Or.inl (hqb ▸ heq)⟩
  refine ⟨?_, ?_⟩
  · fin_cases s <;> decide
  · intro e he f hf hne
    simp only [spokeRoute, List.consecutivePairs, List.tail_cons, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · exact False.elim (hne rfl)
    · exact hcontact
    · exact hcontact.symm
    · exact False.elim (hne rfl)

/-- Distinct spokes have only the center as an allowed continuous contact. -/
theorem spokes_contact_check : ∀ s t : Fin 4, s ≠ t →
    routeContactCheck [(120, 120)] (spokeRoute s) (spokeRoute t) = true := by decide +kernel

/-- Every real intersection of distinct spokes is their common center. -/
theorem spokes_contact {s t : Fin 4} (hst : s ≠ t) {p : ℝ × ℝ}
    (hp : p ∈ support (spokeRoute s)) (hq : p ∈ support (spokeRoute t)) :
    p = realPoint (120, 120) := by
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound (spokes_contact_check s t hst) hp hq
  exact (List.mem_singleton.mp hq) ▸ hpq

end Cslib.Orthogonal.PairedPorts
