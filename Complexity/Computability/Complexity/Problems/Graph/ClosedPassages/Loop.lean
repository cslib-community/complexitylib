/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity

/-!
# Closed passages through a single indexed loop

`ClosedPassages.loop` is the single-loop constructor extracted from
`ComplexityTests/RotationIntersection.lean`, with its original proof and source credit.
Numerical genus zero then excludes interlacing ends of any two distinct indexed loops,
including in arbitrary-degree, disconnected graphs with sparse or repeated declarations.
This is a combinatorial prerequisite for polygonal realization, not a geometric theorem.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.not_alternates_loops`: distinct loops do not interlace
  in a numerically genus-zero rotation with declared endpoints.
-/

public section

namespace Cslib.Complexity.Graph

namespace ClosedPassages

/-- One passage using the two actual ends of a single listed loop. -/
@[expose] def loop {G : Graph} (e : Fin G.2.length)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) :
    ClosedPassages G (fun i => decide (i = e)) where
  count := 1
  ports :=
    { toFun := fun p => ⟨(e, p.2), by simp⟩
      invFun := fun d => (0, d.val.2)
      left_inv := by
        rintro ⟨i, b⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := by
        rintro ⟨⟨i, b⟩, hi⟩
        have hei : i = e := of_decide_eq_true hi
        subst i
        rfl }
  vertex_eq := fun _ => he

/-- The single-loop passage keeps the original edge occurrence and both endpoint tags. -/
@[simp] theorem dart_loop {G : Graph} (e : Fin G.2.length)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true))
    (i : Fin (loop e he).count) (b : Bool) : (loop e he).dart i b = (e, b) := rfl

end ClosedPassages

namespace RotationSystem

/-- Two distinct listed loops cannot have alternating ends in a numerically genus-zero
rotation. No connectedness, degree bound, drawing or Jordan-curve premise is used. -/
theorem not_alternates_loops {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (e f : Fin G.2.length) (hef : e ≠ f)
    (he : (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true))
    (hf : (Dart.vertex (G := G) (f, false)) = Dart.vertex (f, true)) :
    ¬r.Alternates (e, false) (e, true) (f, false) (f, true) := by
  classical
  have h := r.intersectionParity_eq_false hG hr (ClosedPassages.loop e he)
    (ClosedPassages.loop f hf) (by
      intro i hi hj
      exact hef ((of_decide_eq_true hi).symm.trans (of_decide_eq_true hj)))
  change (∑ _ : Fin 1, ∑ _ : Fin 1,
    decide (r.Alternates (e, false) (e, true) (f, false) (f, true))) = false at h
  simpa only [Fin.sum_univ_one, decide_eq_false_iff_not] using h

end RotationSystem
end Cslib.Complexity.Graph
