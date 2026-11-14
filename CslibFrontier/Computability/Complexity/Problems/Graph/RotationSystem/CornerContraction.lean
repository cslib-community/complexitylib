/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContraction
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CornerFaces
import CslibFrontier.Foundations.GroupTheory.Perm.InsertTwo

/-!
# Contracting an edge inserted at two corners

The inserted connector contracts to the outgoing splice of the two original corner
successors. Deleting it instead recovers the original rotation. Both statements concern
the actual listed graphs and retain all old indexed edge ends.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv Perm.Insertion

/-- Deleting a connector inserted at two old corners recovers the exact original rotation. -/
theorem deleteLastEdge_insertEdge {G : Graph} (r : RotationSystem G) (h k : Dart G) :
    (r.insertEdge h k).deleteLastEdge = r := by
  apply ext_rotate
  change removeNone (removeNone ((cornerDartEquiv h k).permCongr
    (r.insertEdge h k).rotate)) = r.rotate
  rw [cornerDartEquiv_rotate, removeNone_insertAfter, removeNone_insertAfter]

/-- Contraction of the new nonloop connector is exactly an outgoing splice on the original
dart positions, followed by the existing pointwise endpoint-name update. -/
theorem rotate_contractLastEdge_insertEdge {G : Graph} (r : RotationSystem G)
    (h k : Dart G) (hk : h.vertex ≠ k.vertex) :
    ((r.insertEdge h k).contractLastEdge hk).rotate =
      (Dart.relabelEquiv G (Function.update id h.vertex k.vertex)).permCongr
        (r.rotate * swap h k) := by
  erw [rotate_contractLastEdge, contractLastEdge_coordinates]
  change removeNone (removeNone
    ((Dart.relabelEquiv G (Function.update id h.vertex k.vertex)).optionCongr.optionCongr.permCongr
      ((cornerDartEquiv h k).permCongr ((r.insertEdge h k).rotate *
        swap (newCornerDart h k true) (newCornerDart h k false))))) = _
  rw [Equiv.permCongr_mul]
  rw [cornerDartEquiv_rotate]
  have hs : (cornerDartEquiv h k).permCongr
      (swap (newCornerDart h k true) (newCornerDart h k false)) =
        swap (some none) none := by
    apply Equiv.ext
    intro z
    rw [Equiv.permCongr_apply, (cornerDartEquiv h k).injective.map_swap,
      Equiv.apply_symm_apply]
    simp only [newCornerDart, Equiv.apply_symm_apply, ↓reduceIte]
    exact congrArg (fun f : Perm (Option (Option (Dart G))) => f z) (swap_comm _ _)
  rw [hs, removeNone_permCongr_option, removeNone_permCongr_option,
    removeNone_twice_insertAfter_mul_swap r.rotate h k
      (fun he => hk (congrArg Dart.vertex he))]

/-- The contracted connector gives exactly the existing directed vertex-merge rotation. -/
theorem contractLastEdge_insertEdge {G : Graph} (r : RotationSystem G)
    (h k : Dart G) (hk : h.vertex ≠ k.vertex) :
    (r.insertEdge h k).contractLastEdge hk = r.mergeVertices k h hk.symm := by
  apply ext_rotate
  rw [rotate_contractLastEdge_insertEdge, rotate_mergeVertices, swap_comm h k]
  rfl

end Cslib.Complexity.Graph.RotationSystem
