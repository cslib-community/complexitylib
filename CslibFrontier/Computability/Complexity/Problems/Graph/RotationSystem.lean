/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Ports
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Rotation systems of listed multigraphs

A dart is an edge-list position and one of its two ends. Loops retain two different darts;
parallel edges retain their different list positions. A rotation permutes darts in one cycle
at each incident vertex. This extra structure retains argument order when the graph comes
from CSP incidences. It does not impose a degree bound.

The face successor reverses an edge and then takes the inverse vertex rotation. Faces are
all its orbits, including singleton orbits. Isolated declared vertices have no darts and are
not represented by this face quotient. No genus-zero condition, geometric realization or
planarity recognition theorem is asserted here.

## Main definitions

* `Cslib.Complexity.Graph.Dart`: indexed ends of listed edges.
* `Cslib.Complexity.Graph.RotationSystem`: one rotation cycle per nonempty vertex fiber.
* `Cslib.Complexity.Graph.RotationSystem.faceNext`: the face successor permutation.
* `Cslib.Complexity.Graph.RotationSystem.Face`: face orbits, including fixed points.
-/

public section

namespace Cslib.Complexity.Graph

/-- A listed edge occurrence together with a choice of endpoint. -/
abbrev Dart (G : Graph) := Fin G.2.length × Bool

namespace Dart

/-- The endpoint of an indexed edge end; `false` selects the first endpoint. -/
@[expose] def vertex {G : Graph} (d : Dart G) : ℕ := G.edgeEndpoint d.1 d.2

/-- Reverse an edge while retaining its edge-list occurrence. -/
@[expose] def reverse {G : Graph} (d : Dart G) : Dart G := (d.1, !d.2)

/-- Reversing twice returns the same indexed end. -/
@[simp] theorem reverse_reverse {G : Graph} (d : Dart G) : d.reverse.reverse = d := by
  rcases d with ⟨i, b⟩
  simp [reverse]

/-- Even a loop has two distinct indexed ends. -/
theorem reverse_ne {G : Graph} (d : Dart G) : d.reverse ≠ d := by
  intro h
  have hb := congrArg Prod.snd h
  exact Bool.not_ne_self _ hb

/-- Edge reversal as a permutation of all indexed ends. -/
@[expose] def reversal (G : Graph) : Equiv.Perm (Dart G) where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

/-- There are two darts per listed edge, counting loops and parallel occurrences. -/
theorem card (G : Graph) : Fintype.card (Dart G) = 2 * G.2.length := by
  simp [Dart, Nat.mul_comm]

end Dart

/-- A cyclic order of the darts at each incident vertex. No cyclic start point is chosen. -/
structure RotationSystem (G : Graph) where
  /-- One successor permutation on all darts. -/
  rotate : Equiv.Perm (Dart G)
  /-- Its orbits are exactly the nonempty endpoint fibers. -/
  sameCycle_iff : ∀ d e, rotate.SameCycle d e ↔ d.vertex = e.vertex

namespace RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- Rotating around a vertex keeps that endpoint. -/
theorem vertex_rotate (d : Dart G) : (r.rotate d).vertex = d.vertex := by
  exact (r.sameCycle_iff _ _).mp (Equiv.Perm.sameCycle_apply_left.mpr .rfl)

/-- Reverse an edge, then turn backwards around its new endpoint. -/
@[expose] def faceNext : Equiv.Perm (Dart G) :=
  (Dart.reversal G).trans r.rotate.symm

/-- All face orbits, including the singleton orbits omitted by nontrivial cycle factors. -/
abbrev Face := Quotient (Equiv.Perm.SameCycle.setoid r.faceNext)

/-- A dart and its face successor lie in the same face orbit. -/
theorem face_eq_next (d : Dart G) :
    (Quotient.mk _ (r.faceNext d) : r.Face) = Quotient.mk _ d :=
  Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr .rfl)

/-- Reverse every vertex rotation, corresponding to reversal of the global orientation. -/
@[expose] def mirror : RotationSystem G where
  rotate := r.rotate.symm
  sameCycle_iff := by
    intro d e
    change (r.rotate⁻¹).SameCycle d e ↔ _
    rw [Equiv.Perm.sameCycle_inv]
    exact r.sameCycle_iff d e

end RotationSystem
end Cslib.Complexity.Graph
