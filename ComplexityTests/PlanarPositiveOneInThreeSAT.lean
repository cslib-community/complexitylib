/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.PlanarPositiveOneInThreeSAT

/-! Nonempty, signed and rejected source instances of the actual planar positive compiler. -/

namespace ComplexityTests.PlanarPositiveOneInThreeSAT

open Cslib.Logic.PL Cslib.Complexity

private def mixedSource : CNF ℕ :=
  [[(0, true), (1, false)], [(0, false), (2, true)]]

/-- Both source polarities are compiled away, while all four models are retained. -/
example : (toPlanarPositiveOneInExactThreeSATThree mixedSource).oneModelCount = 4 := by
  rw [oneModelCount_toPlanarPositiveOneInExactThreeSATThree _ (by decide)]
  decide

/-- The nonempty output has the actual emitted full-segment drawing. -/
example : Graph.IsPlanarOrthogonalDrawing
    (SAT.incidenceGraph (toPlanarPositiveOneInExactThreeSATThree mixedSource))
    (toDrawnPlanarPositiveOneInExactThreeSATThree mixedSource).2 :=
  isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree mixedSource

/-- The emitted drawing passes the planarity guard, so the guarded count keeps all four models. -/
example : SharpDrawnPlanarPositiveOneInExactThreeSATThree
    (toDrawnPlanarPositiveOneInExactThreeSATThree mixedSource) = 4 := by
  rw [SharpDrawnPlanarPositiveOneInExactThreeSATThree]
  split
  · rw [show (toDrawnPlanarPositiveOneInExactThreeSATThree mixedSource).1 =
        toPlanarPositiveOneInExactThreeSATThree mixedSource from rfl,
      sharpPositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree]
    decide
  · rename_i h
    exact
      (h (isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree mixedSource)).elim

example : toPlanarPositiveOneInExactThreeSATThree mixedSource ∈
    PlanarPositiveOneInExactThreeSATThree := by
  apply (mem_PlanarPositiveOneInExactThreeSATThree_toPlanar_iff mixedSource).mpr
  exact ⟨by decide, fun _ => true, by decide⟩

/-- Empty source formulas and empty source clauses retain their different counting meanings. -/
example : (toPlanarPositiveOneInExactThreeSATThree ([] : CNF ℕ)).oneModelCount = 1 := by
  rw [oneModelCount_toPlanarPositiveOneInExactThreeSATThree _ (by simp)]
  decide

example : (toPlanarPositiveOneInExactThreeSATThree ([[]] : CNF ℕ)).oneModelCount = 0 := by
  rw [oneModelCount_toPlanarPositiveOneInExactThreeSATThree _ (by decide)]
  decide

/-- Repeated source variables do not create repeated variables in an output clause. -/
example :
    (toPlanarPositiveOneInExactThreeSATThree [[(0, true), (0, false)]]).oneModelCount = 2 := by
  rw [oneModelCount_toPlanarPositiveOneInExactThreeSATThree _ (by decide)]
  decide

example : ∀ c ∈ toPlanarPositiveOneInExactThreeSATThree [[(0, true), (0, false)]],
    c.length = 3 ∧ (c.map Prod.fst).Nodup :=
  exactClauses_toPlanarPositiveOneInExactThreeSATThree _

/-- The total compiler rejects width-four source syntax even when its ordinary formula is true. -/
example : SharpPositiveOneInExactThreeSATThree
    (toPlanarPositiveOneInExactThreeSATThree
      [[(0, true), (0, false), (0, true), (0, false)]]) = 0 := by
  rw [sharpPositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree]
  decide

end ComplexityTests.PlanarPositiveOneInThreeSAT
