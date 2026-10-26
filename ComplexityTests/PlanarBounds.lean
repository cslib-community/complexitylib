/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedBounds

namespace ComplexityTests.PlanarBounds

open Cslib.Complexity Cslib.Complexity.SAT.ParsimoniousPlanar

-- The same linear grid bounds apply to an ordinary name and a succinct large binary name.
example : gridWidth [[(7, true)]] = 4080 := by decide +kernel
example : gridHeight [[(7, true)]] = 4560 := by decide +kernel
example : gridWidth [[(2 ^ 100, true)]] = 4080 := by decide +kernel
example : gridHeight [[(2 ^ 100, true)]] = 4560 := by decide +kernel

-- A concrete nonempty compiled incidence drawing inhabits the bounded-output predicate.
example : Graph.drawingFits (positions [[(7, true)]], routes [[(7, true)]]) 4080 4560 :=
  drawing_fits [[(7, true)]]

-- An isolated empty clause still has its actual declared clause vertex in the rectangle.
example : positions [[]] = [(1080, 1080)] := by decide +kernel
example : Graph.drawingFits (positions [[]], routes [[]]) 2160 2160 := drawing_fits [[]]

-- Exact costs for the actual nonempty unit-clause output, including its final three-segment route.
example : (routes [[(7, true)]]).length = 637 := by decide +kernel
example : Graph.drawingSegmentCount (positions [[(7, true)]], routes [[(7, true)]]) = 639 :=
  by decide +kernel
example : Graph.drawingWireLength (positions [[(7, true)]], routes [[(7, true)]]) = 28230 :=
  by decide +kernel
example : Graph.drawingWireLength (positions [[(7, false)]], routes [[(7, false)]]) = 28230 :=
  by decide +kernel

end ComplexityTests.PlanarBounds
