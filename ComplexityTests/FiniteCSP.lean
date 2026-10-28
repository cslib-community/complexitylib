/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.FiniteCSP
import Complexity.Computability.Complexity.FineGrained.CountingFiniteCSP

/-!
# Finite-domain CSP unit tests

This module tests the finite-domain CSP compilation pipeline and its exact model counting:
* Bit width computation and binary encoding retraction properties.
* Graph 3-coloring on the triangle graph K₃ (yielding chromatic polynomial P(K₃, 3) = 6).
* Graph 3-coloring on the path graph P₃ (yielding P(P₃, 3) = 12).
* Graph 2-coloring on K₃ (unsatisfiable, yielding 0 models).
* Exact agreement between finite-domain model count and compiled Boolean CSP model count.
* Width and variable bounds on the compiled Boolean CSP instance.
-/

open Cslib.Logic.PL
open Cslib.Logic.PL.FiniteCSP
open Cslib.Complexity.CountingFiniteCSP

namespace ComplexityTests.FiniteCSP

-- Bit width computation
example : bitWidth 1 = 1 := by decide
example : bitWidth 2 = 1 := by decide
example : bitWidth 3 = 2 := by decide
example : bitWidth 4 = 2 := by decide
example : bitWidth 5 = 3 := by decide
example : bitWidth 8 = 3 := by decide

-- Binary encoding round-trips
example : natToBits 2 0 = [false, false] := by decide
example : natToBits 2 1 = [true, false] := by decide
example : natToBits 2 2 = [false, true] := by decide
example : natToBits 2 3 = [true, true] := by decide
example : bitsToNat [true, false] = 1 := by decide
example : bitsToNat [false, true] = 2 := by decide
example : bitsToNat (natToBits 3 5) = 5 := by decide

/-- Disequality semantics over `Fin q`. -/
def semNeq (q : ℕ) : Unit → List (Fin q) → Bool
  | (), [c1, c2] => c1 != c2
  | (), _ => false

/-- Triangle graph K₃ 3-coloring CSP instance. -/
def triangleCSP : CSP Unit ℕ :=
  [((), [0, 1]), ((), [1, 2]), ((), [0, 2])]

/-- Path graph P₃ 3-coloring CSP instance. -/
def pathCSP : CSP Unit ℕ :=
  [((), [0, 1]), ((), [1, 2])]

-- Model counts directly on finite-domain CSP
example : triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) = 6 := by decide
example : pathCSP.modelCountOn (semNeq 3) (Finset.range 3) = 12 := by decide
example : triangleCSP.modelCountOn (semNeq 2) (Finset.range 3) = 0 := by decide

-- Model counts on compiled Boolean CSP
example :
    (toBooleanCSP 3 3 triangleCSP).modelCountOn (semBoolean 3 (semNeq 3)) (Finset.range 6) = 6 := by
  decide

example :
    (toBooleanCSP 3 3 pathCSP).modelCountOn (semBoolean 3 (semNeq 3)) (Finset.range 6) = 12 := by
  decide

example :
    (toBooleanCSP 2 3 triangleCSP).modelCountOn (semBoolean 2 (semNeq 2)) (Finset.range 3) = 0 := by
  decide

-- Model count equivalence theorem application
example :
    (toBooleanCSP 3 3 triangleCSP).modelCountOn (semBoolean 3 (semNeq 3)) (Finset.range 6) =
    triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) :=
  modelCountOn_toBooleanCSP 3 3 (by decide) (semNeq 3) triangleCSP (by decide)

-- Width and variable bounds
example : (toBooleanCSP 3 3 triangleCSP).all (fun c => c.2.length ≤ 4) = true := by decide
example : (toBooleanCSP 3 3 triangleCSP).vars.all (fun v => decide (v < 6)) = true := by decide
example : CSP.validDeclaredCSP 4 6 (toBooleanCSP 3 3 triangleCSP) = true := by decide

-- Satisfiability and unsatisfiability checks
example : 0 < triangleCSP.modelCountOn (semNeq 3) (Finset.range 3) := by decide
example : triangleCSP.modelCountOn (semNeq 2) (Finset.range 3) = 0 := by decide

end ComplexityTests.FiniteCSP
