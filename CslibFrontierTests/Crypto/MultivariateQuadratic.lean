/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.LinearAlgebra.MultivariateQuadratic

set_option linter.privateModule false

/-!
# Tests for vector-valued multivariate quadratic maps

These clients check the common Oil and Vinegar algebra in characteristic two and odd
characteristic.  They do not model a full signature scheme.
-/

public section

open Matrix

namespace Cslib.MultivariateQuadraticMap.Tests

/-- The quadratic polynomial `x₀² + x₀x₁`, presented by a deliberately nonsymmetric matrix. -/
private def oilVinegarMatrix (R : Type*) [CommRing R] : Unit → Matrix (Fin 2) (Fin 2) R :=
  fun _ ↦ !![1, 1; 0, 0]

/-- The second coordinate is the oil direction; equivalently, the first coordinate vanishes. -/
private def oilSpace (R : Type*) [CommRing R] : Submodule R (Fin 2 → R) :=
  LinearMap.ker (LinearMap.proj 0)

private theorem vanishesOn_oilSpace (R : Type*) [CommRing R] :
    VanishesOn (ofMatrices (oilVinegarMatrix R)) (oilSpace R) := by
  intro o ho
  have h0 : o 0 = 0 := by
    simpa only [oilSpace, LinearMap.mem_ker, LinearMap.proj_apply] using ho
  funext u
  fin_cases u
  rw [ofMatrices_apply]
  simp [oilVinegarMatrix, dotProduct, mulVec, h0]

example : (![0, 1] : Fin 2 → ZMod 2) ∈ oilSpace (ZMod 2) := by
  rfl

example : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by
  decide

example (R : Type*) [CommRing R] (v : Fin 2 → R) {o : Fin 2 → R} (ho : o ∈ oilSpace R) :
    ofMatrices (oilVinegarMatrix R) (v + o) =
      ofMatrices (oilVinegarMatrix R) v +
        linearization (ofMatrices (oilVinegarMatrix R)) v o :=
  map_add_of_mem (vanishesOn_oilSpace R) v ho

example (R : Type*) [CommRing R] :
    VanishesOn
      ((ofMatrices (oilVinegarMatrix R)).comp (LinearMap.id (R := R) (M := Fin 2 → R)))
      ((oilSpace R).comap (LinearMap.id (R := R) (M := Fin 2 → R))) :=
  (vanishesOn_oilSpace R).comp_comap _

example : ofMatrices (oilVinegarMatrix (ZMod 2)) ![1, 1] () = 0 := by decide

example :
    QuadraticMap.polar (ofMatrices (oilVinegarMatrix (ZMod 2))) ![1, 0] ![0, 1] () = 1 := by
  decide

example : ofMatrices (oilVinegarMatrix (ZMod 5)) ![2, 1] () = 1 := by decide

example :
    QuadraticMap.polar (ofMatrices (oilVinegarMatrix (ZMod 5))) ![1, 0] ![0, 1] () = 1 := by
  decide

end Cslib.MultivariateQuadraticMap.Tests
