/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Design.ReedSolomon
public import Mathlib.Data.Fin.VecNotation

/-!
# Reed–Solomon designs

The graphs of the nine polynomials of degree less than two over `ZMod 3`, restricted to two
points, have two elements and pairwise meet in at most one.
-/

public section

namespace CslibFrontierTests.ReedSolomon

open Cslib Finset

/-- The lines over `ZMod 3` on two points form a design with intersections of size at most one. -/
theorem isDesign_rsDesign_three : IsDesign (rsDesign 3 2 2) 2 1 :=
  isDesign_rsDesign (by omega)

/-- The lines `y = x` and `y = 1` over `ZMod 3` meet in at most one of the first two points. -/
theorem card_inter_rsDesign_three_le : #(rsDesign 3 2 2 ![0, 1] ∩ rsDesign 3 2 2 ![1, 0]) ≤ 1 :=
  isDesign_rsDesign_three.2 _ _ (by decide)

end CslibFrontierTests.ReedSolomon
