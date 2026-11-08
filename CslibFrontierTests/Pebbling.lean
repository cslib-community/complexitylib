/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Pebbling.Pyramid
import CslibFrontier.Computability.Pebbling.BinaryTree

/-!
# Black pebbling of pyramids and complete binary trees

Concrete instances of the pebbling prices. The pyramid of height `2` and the complete binary tree
of height `3` meet their prices, and each fails with one pebble fewer, so the lower bounds are not
vacuous. A source has price `1`, and a run is written out explicitly as a sanity check on the
game itself.
-/

namespace ComplexityTests.Pebbling

open Cslib Cslib.Pebbling

/-- Cook's theorem at height `2`: four pebbles suffice for the sink of `Π_2`. -/
example : BlackPebblable (pyramid 2) 4 (PyramidVertex.top 2) :=
  blackPebblable_pyramid (PyramidVertex.top 2)

/-- Three pebbles do not suffice for the sink of `Π_2`. -/
example : ¬ BlackPebblable (pyramid 2) 3 (PyramidVertex.top 2) := fun h =>
  absurd (PyramidVertex.le_of_blackPebblable (by decide) h) (by decide)

example : blackPebblingPrice (pyramid 2) (PyramidVertex.top 2) = 4 :=
  blackPebblingPrice_pyramid_top (by decide)

/-- A middle vertex of `Π_5` at level `3` has price `5`. -/
example : blackPebblingPrice (pyramid 5) ⟨3, 1, by decide⟩ = 5 :=
  blackPebblingPrice_pyramid _ (by decide)

/-- The sources of a pyramid have price `1`. -/
example : blackPebblingPrice (pyramid 4) ⟨0, 2, by decide⟩ = 1 :=
  blackPebblingPrice_eq_one_of_source fun u hu => by
    simp only [pyramid_adj] at hu
    omega

/-- The complete binary tree of height `3` has price `5`. -/
example : blackPebblingPrice (completeBinaryTree 3) (BinaryTreeVertex.root 3) = 5 :=
  blackPebblingPrice_completeBinaryTree_root (by decide)

/-- Four pebbles do not suffice for the root of `T_3`. -/
example : ¬ BlackPebblable (completeBinaryTree 3) 4 (BinaryTreeVertex.root 3) := fun h =>
  absurd ((forcesPebbles_completeBinaryTree _ (by decide)).le_of_blackPebblable
    (unblocked_completeBinaryTree_empty _) h) (by decide)

/-- The right child of the root of `T_3` has price `4`. -/
example : blackPebblingPrice (completeBinaryTree 3) ⟨[true], by decide⟩ = 4 :=
  blackPebblingPrice_completeBinaryTree _ (by decide)

/-- The two sources of `Π_1`. -/
def left : PyramidVertex 1 := ⟨0, 0, by decide⟩

/-- The right source of `Π_1`. -/
def right : PyramidVertex 1 := ⟨0, 1, by decide⟩

/-- An explicit three-pebble run on `Π_1`: pebble both sources, then the sink. -/
example : (blackPebbleGame (pyramid 1) 3).MTr ∅
    [.place left, .place right, .place (PyramidVertex.top 1)]
    {PyramidVertex.top 1, right, left} := by
  refine .stepL ⟨.place fun u hu => ?_, by decide⟩ <|
    .stepL ⟨.place fun u hu => ?_, by decide⟩ <|
    .stepL ⟨.place fun u hu => ?_, by decide⟩ .refl
  all_goals simp only [pyramid_adj, left, right, PyramidVertex.top] at hu
  · omega
  · omega
  · simp only [Finset.mem_insert, PyramidVertex.ext_iff, left, right]
    omega

end ComplexityTests.Pebbling
