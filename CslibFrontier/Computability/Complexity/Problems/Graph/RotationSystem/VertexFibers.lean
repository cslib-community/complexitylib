/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Dual
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constructing vertex-fiber rotations by complete orbit counts

A vertex-preserving dart permutation maps its full orbit quotient onto the actual incident
vertices. Equality of these finite cardinalities proves that every nonempty vertex fiber is
one cycle. Singleton cycles are included; declared points receive no invented darts. Surgery
clients must prove the count from their literal permutations and actual endpoint maps.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv

private theorem sameCycle_vertex_of_step {G : Graph} (f : Perm (Dart G))
    (hs : ∀ d, (f d).vertex = d.vertex) {a b : Dart G} (h : f.SameCycle a b) :
    a.vertex = b.vertex :=
  Perm.sameCycle_one.mp (h.map_of_semiconj (show Function.Semiconj (fun d => d.vertex) f
    (1 : Perm ℕ) from hs))

private def vertexMap {G : Graph} (f : Perm (Dart G))
    (hs : ∀ d, (f d).vertex = d.vertex) :
    Quotient (Perm.SameCycle.setoid f) → IncidentVertex G :=
  Quotient.lift (fun d => ⟨d.vertex, d, rfl⟩)
    (fun _ _ h => Subtype.ext (sameCycle_vertex_of_step f hs h))

private theorem vertexMap_surjective {G : Graph} (f : Perm (Dart G))
    (hs : ∀ d, (f d).vertex = d.vertex) : Function.Surjective (vertexMap f hs) := by
  rintro ⟨v, d, hd⟩
  exact ⟨Quotient.mk _ d, Subtype.ext hd⟩

/-- Every actual vertex rotation has one complete orbit per incident vertex. -/
noncomputable def rotateOrbitEquiv {G : Graph} (r : RotationSystem G) :
    Quotient (Perm.SameCycle.setoid r.rotate) ≃ IncidentVertex G :=
  Equiv.ofBijective (vertexMap r.rotate r.vertex_rotate) ⟨by
    intro q s hqs
    induction q using Quotient.inductionOn with
    | h a =>
      induction s using Quotient.inductionOn with
      | h b => exact Quotient.sound ((r.sameCycle_iff _ _).mpr (congrArg Subtype.val hqs)),
    vertexMap_surjective _ _⟩

/-- Complete orbit counts suffice for the one-cycle-per-incident-vertex contract, provided
that the actual successor preserves endpoints. Neither property is taken as an unchecked flag. -/
@[expose] def ofOrbitCount {G : Graph} (f : Perm (Dart G)) (hs : ∀ d, (f d).vertex = d.vertex)
    (hc : Nat.card (Quotient (Perm.SameCycle.setoid f)) = Nat.card (IncidentVertex G)) :
    RotationSystem G where
  rotate := f
  sameCycle_iff a b := by
    constructor
    · exact sameCycle_vertex_of_step f hs
    · intro hab
      have hi := ((vertexMap_surjective f hs).bijective_of_nat_card_le hc.le).1
      exact Quotient.exact (hi (show vertexMap f hs (Quotient.mk _ a) =
        vertexMap f hs (Quotient.mk _ b) from Subtype.ext hab))

/-- The certified constructor retains the exact supplied successor permutation. -/
@[simp] theorem ofOrbitCount_rotate {G : Graph} (f : Perm (Dart G))
    (hs : ∀ d, (f d).vertex = d.vertex)
    (hc : Nat.card (Quotient (Perm.SameCycle.setoid f)) = Nat.card (IncidentVertex G)) :
    (ofOrbitCount f hs hc).rotate = f := rfl

end Cslib.Complexity.Graph.RotationSystem
