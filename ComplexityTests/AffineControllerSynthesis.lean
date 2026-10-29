/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.AffineControllerSynthesis

/-!
# Tests for synthesizing controller-dependent affine coefficients

The examples use a controller that complements its bits and selects between identity and a
non-symmetric affine shear. They check the resulting nontrivial fourth power, instantiated gate
budgets, and the zero-width payload case.
-/

namespace ComplexityTests.AffineControllerSynthesis

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration

private def flipController {q : ℕ} (u : BitString q) : BitString q := fun i => !u i

private def shear : BitString 2 →ᵃ[Bool] BitString 2 :=
  AffineMap.pi fun i =>
    if i = 0 then
      (AffineMap.proj (0 : Fin 2) : BitString 2 →ᵃ[Bool] Bool) + AffineMap.proj (1 : Fin 2)
    else AffineMap.proj (1 : Fin 2)

private def selectedPayload (u : BitString 16) : BitString 2 →ᵃ[Bool] BitString 2 :=
  if u 0 then AffineMap.const Bool (BitString 2) ![false, true] + shear
  else AffineMap.id Bool (BitString 2)

-- The matrix is not symmetric, and both translation and linear part depend on the controller.
example :
    shear ![false, true] = ![true, true] ∧
      selectedPayload (fun _ => false) ![false, true] = ![false, true] ∧
      selectedPayload (fun _ => true) ![false, true] = ![true, false] := by
  decide

private theorem fourth_power :
    (controlledBits flipController (fun u => selectedPayload u))^[4]
        (Fin.append (fun _ => false) ![false, false]) =
      Fin.append (fun _ => false) ![true, false] := by
  decide

-- The synthesized circuit realizes the nontrivial fourth power on this state.
example : ∃ c : Circuit signature (16 + 2) (16 + 2),
    c.Computes interpretation ((controlledBits flipController
      (fun u => selectedPayload u))^[4]) ∧
    c.eval interpretation (Fin.append (fun _ => false) ![false, false]) =
      Fin.append (fun _ => false) ![true, false] ∧
    c.size ≤ 2433056 := by
  obtain ⟨c, hc, hs⟩ := affine_controller_power_shannon (by decide : 16 ≤ 16)
    flipController selectedPayload 4
  refine ⟨c, hc, (hc _).trans fourth_power, ?_⟩
  simpa [affineControllerSynthesisBudget] using hs

private def translatedPayload (u : BitString 16) : BitString 16 →ᵃ[Bool] BitString 16 :=
  AffineMap.const Bool (BitString 16) u + AffineMap.id Bool (BitString 16)

-- A concrete family with controller-dependent translations satisfies the same bound for all T.
example (T : ℕ) : ∃ c : Circuit signature (16 + 16) (16 + 16),
    c.Computes interpretation ((controlledBits flipController
      (fun u => translatedPayload u))^[T]) ∧ c.size ≤ 31851872 := by
  simpa [affineControllerSynthesisBudget] using
    affine_controller_power_shannon (by decide : 16 ≤ 16) flipController translatedPayload T

-- At q = p = 16 the new budget is > 3× smaller, and at q = p = 32 the saving exceeds 6×.
example :
    (affineControllerSynthesisBudget 16 16 (27 * 2 ^ 16 / 16) = 31851872 ∧
      affineControllerBudget 16 16 = 100728834 ∧
      3 * affineControllerSynthesisBudget 16 16 (27 * 2 ^ 16 / 16) <
        affineControllerBudget 16 16) ∧
    (affineControllerSynthesisBudget 32 32 (27 * 2 ^ 32 / 32) = 3942779983040 ∧
      affineControllerBudget 32 32 = 24193550778370 ∧
      6 * affineControllerSynthesisBudget 32 32 (27 * 2 ^ 32 / 32) <
        affineControllerBudget 32 32) := by
  norm_num [affineControllerSynthesisBudget, affineControllerBudget]

-- An empty payload leaves a nontrivial controller transition, without phantom payload costs.
example : ∃ c : Circuit signature (16 + 0) (16 + 0),
    c.eval interpretation (fun _ => false) = (fun _ => true) ∧ c.size ≤ 1769472 := by
  obtain ⟨c, hc, hs⟩ := affine_controller_power_shannon (by decide : 16 ≤ 16)
    flipController (fun _ => AffineMap.id Bool (BitString 0)) 1
  refine ⟨c, (hc _).trans ?_, ?_⟩
  · decide
  · simpa [affineControllerSynthesisBudget] using hs

-- Input time is little endian: 001 selects the same fourth power, not the first power.
example : ∃ c : Circuit signature ((16 + 2) + 3) (16 + 2),
    c.eval interpretation
        (Fin.append (Fin.append (fun _ => false) ![false, false]) ![false, false, true]) =
      Fin.append (fun _ => false) ![true, false] ∧ c.size ≤ 7299384 := by
  obtain ⟨c, hc, hs⟩ := affine_controller_variable_time_shannon (by decide : 16 ≤ 16)
    flipController selectedPayload 3
  refine ⟨c, (hc _).trans ?_, ?_⟩
  · decide
  · simpa [affineControllerSynthesisBudget] using hs

end ComplexityTests.AffineControllerSynthesis
