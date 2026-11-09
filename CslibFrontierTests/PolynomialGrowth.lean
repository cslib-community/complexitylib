/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.WordRAM.Time

/-! Ordinary-import regression tests for polynomial resource-growth automation. -/

open Turing.MultiTapeTM

section

variable {α : Type*} {size u v : α → ℕ}

example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => 7 * (u a + 1) ^ 3 + v a * (2 * size a + 5)) := by
  growth_poly

example (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log 2 (u a + 1) + Nat.sqrt (size a * u a)) := by
  growth_poly

example {β : Type*} {size' v : β → ℕ} {g : α → β}
    (hv : PolyBounded size' v) (hg : PolyBounded size (fun a => size' (g a))) :
    PolyBounded size (fun a => v (g a)) := by
  apply hv.comp
  growth_poly

example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) (hu : PolyBounded size u) :
    PolyBounded size (fun a => F (2 * u a + size a + 1)) := by
  apply (PolyBounded.of_polynomiallyBounded id hF).comp
  growth_poly

-- A variable exponent and an unknown function are deliberately unsupported.
example (_hu : PolyBounded size u) : True := by
  fail_if_success have : PolyBounded id (fun n : ℕ => 2 ^ n) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => u a ^ size a) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => Nat.factorial (u a)) := by growth_poly
  trivial

end

example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) :
    Cslib.PolynomiallyBounded (fun n => 3 * F n ^ 2 + Nat.log 2 (n + 1)) := by
  growth_poly

-- Polynomial growth does not establish an exact word-width admission condition.
example : PolyBounded id (fun n : ℕ => n + 1) ∧ Cslib.WordRAM.Fits 3 7 ∧
    ¬Cslib.WordRAM.Fits 3 8 := by
  refine ⟨?_, by decide, by decide⟩
  growth_poly

example : True := by
  fail_if_success have : Cslib.WordRAM.Fits 3 8 := by growth_poly
  trivial
