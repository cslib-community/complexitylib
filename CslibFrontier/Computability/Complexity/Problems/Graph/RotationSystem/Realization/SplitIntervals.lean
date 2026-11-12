/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitUnchanged

/-!
# Directed intervals inside the two retained contraction blocks

Each retained source block preserves its strict cyclic triples. Source first-hit ranks
are compared only after their explicit deletion offset; raw distances across the deleted
ends are never identified.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- All distinct retained triples in either original endpoint cycle retain literal
cyclic order after the outgoing swap and two deletions. -/
theorem mem_rotationInterval_contractionLift_active {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    (a b c : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) (side : Bool)
    (ha : (contractionLift G u v a.val).vertex = (lastEdgeDart G u v side).vertex)
    (hb : (contractionLift G u v b.val).vertex = (lastEdgeDart G u v side).vertex)
    (hc : (contractionLift G u v c.val).vertex = (lastEdgeDart G u v side).vertex)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b.val ∈ (r.contractLastEdge huv).rotationInterval a.val c.val ↔
      contractionLift G u v b.val ∈ r.rotationInterval (contractionLift G u v a.val)
        (contractionLift G u v c.val) := by
  have hne (x y : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) (hxy : x ≠ y) :
      contractionLift G u v x.val ≠ contractionLift G u v y.val :=
    fun h => hxy (Subtype.ext (contractionLift_injective G u v h))
  rw [r.mem_rotationInterval_contractLastEdge_iff_ranks huv a b c hab hbc hac,
    r.mem_rotationInterval_iff_ranks (lastEdgeDart G u v side) _ _ _ ha.symm hb.symm hc.symm
      (hne a b hab) (hne b c hbc) (hne a c hac),
    r.contractionRank_lt_iff_sourceDistance_lt huv a b side ha hb,
    r.contractionRank_lt_iff_sourceDistance_lt huv b c side hb hc,
    r.contractionRank_lt_iff_sourceDistance_lt huv c a side hc ha]

end Cslib.Complexity.Graph.RotationSystem
