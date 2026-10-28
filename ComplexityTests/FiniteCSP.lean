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
* Non-vacuity of `ValidFiniteKCSP` on concrete 3-coloring instances.
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

/-- Triangle graph K₃ 3-coloring CSP instance. -/
def triangleCSP : CSP ℕ :=
  [{ vars := [0, 1],
     forbidden := [[0, 0], [1, 1], [2, 2]],
     arity := 2,
     valid := by decide },
   { vars := [1, 2],
     forbidden := [[0, 0], [1, 1], [2, 2]],
     arity := 2,
     valid := by decide },
   { vars := [0, 2],
     forbidden := [[0, 0], [1, 1], [2, 2]],
     arity := 2,
     valid := by decide }]

/-- Path graph P₃ 3-coloring CSP instance. -/
def pathCSP : CSP ℕ :=
  [{ vars := [0, 1],
     forbidden := [[0, 0], [1, 1], [2, 2]],
     arity := 2,
     valid := by decide },
   { vars := [1, 2],
     forbidden := [[0, 0], [1, 1], [2, 2]],
     arity := 2,
     valid := by decide }]

/-- Triangle graph K₃ 2-coloring CSP instance. -/
def triangleCSP2 : CSP ℕ :=
  [{ vars := [0, 1],
     forbidden := [[0, 0], [1, 1]],
     arity := 2,
     valid := by decide },
   { vars := [1, 2],
     forbidden := [[0, 0], [1, 1]],
     arity := 2,
     valid := by decide },
   { vars := [0, 2],
     forbidden := [[0, 0], [1, 1]],
     arity := 2,
     valid := by decide }]

-- Model counts
theorem triangle_3coloring_count :
    (toCNF triangleCSP 3 3).modelCountOn (Finset.range 6) = 6 := by
  decide

theorem path_3coloring_count :
    (toCNF pathCSP 3 3).modelCountOn (Finset.range 6) = 12 := by
  decide

theorem triangle_2coloring_count :
    (toCNF triangleCSP2 2 3).modelCountOn (Finset.range 3) = 0 := by
  decide

-- Width and variable bounds
example : (toCNF triangleCSP 3 3).all (fun c => c.length ≤ 4) = true := by decide

example : (toCNF triangleCSP 3 3).all (fun c => c.all (fun l => l.1 < 6)) = true := by decide

-- Non-vacuity: triangle CSP has width 2 and is satisfiable by a proper 3-coloring
def triangleAssignment : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩

theorem triangle_hasWidth : triangleCSP.HasWidth 2 := by
  intro c hc
  simp only [triangleCSP, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [Constraint.HasWidth]

theorem triangle_valid : (3, triangleCSP) ∈ ValidFiniteKCSP 3 2 := by
  refine ⟨triangle_hasWidth, ?_, ?_, ?_⟩
  · intro c hc
    simp only [triangleCSP, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl
  · intro c hc v hv
    simp only [triangleCSP, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      rcases hv with rfl | rfl <;> decide
  · refine ⟨triangleAssignment, ?_⟩
    decide

end ComplexityTests.FiniteCSP
