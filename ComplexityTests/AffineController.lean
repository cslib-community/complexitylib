/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Iteration.AffineController

/-!
# Tests for autonomous controllers and affine-payload iteration bounds

Exercises `controlledMap_iterate`, `controlledBits_iterate`, `controlled_circuit`,
`affineHash_circuit`, `affineHash_affineMapSeed`, `affine_payload_circuit`,
`affine_controller_power` (for zero-width and positive-width controllers and payloads),
`affine_controller_polynomial`, and `affine_controller_variable_time`, together with `#print axioms`
guards for the headline theorems.
-/

namespace ComplexityTests.AffineController

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Iteration
open Cslib.BitString.LinearHash

/-! ### Autonomous controllers and composite payloads -/

-- Iterating a controlled map on `Bool × Bool`, flat Boolean encoding of controller + payload,
-- iterating `controlledBits`, and selecting identity payload circuits for a 1-bit controller.
example (u : BitString 1) (v : BitString 2) (T : ℕ) (x : BitString (1 + 2))
    (g : BitString 1 → BitString 1) :
    (controlledMap Bool.not (fun u v => u ^^ v))^[3] (false, true) = (true, false) ∧
      controlledBits id (fun _ w => w) (Fin.append u v) = Fin.append u v ∧
      (controlledBits (q := 1) (p := 2) id (fun _ v => v))^[T] x =
        controlledBits (id^[T]) (controlledPayload id (fun _ v => v) T) x ∧
      ∃ c : Circuit signature (1 + 2) (1 + 2),
        c.Computes interpretation (controlledBits g (fun _ v => v)) ∧
        c.size ≤ 2 + 2 ^ 1 * (0 + 6 * 1 + 4 * 2 + 1) :=
  ⟨by rw [controlledMap_iterate]; decide,
    by simp,
    controlledBits_iterate id (fun _ v => v) T x,
    controlled_circuit g (fun _ v => v) 0 fun _ => ⟨Circuit.id signature 2, fun _ => rfl, by simp⟩⟩

/-! ### Affine hashes and affine payloads -/

-- Every 2×2 affine hash and 2-bit affine payload has a De Morgan circuit of size at most 32, and
-- evaluating `affineHash` on `affineMapSeed` of an affine translation recovers the translation.
example (seed : (Fin 2 → BitString 2) × BitString 2) (b v : BitString 2) :
    (∃ c : Circuit signature 2 2,
      c.Computes interpretation (affineHash seed) ∧ c.size ≤ 32) ∧
    affineHash (affineMapSeed (AffineMap.const Bool (BitString 2) b +
      AffineMap.id Bool (BitString 2))) v = b + v ∧
    ∃ c : Circuit signature 2 2,
      c.Computes interpretation (AffineMap.id Bool (BitString 2)) ∧ c.size ≤ 32 :=
  ⟨by simpa using affineHash_circuit seed,
    affineHash_affineMapSeed _ v,
    by simpa using affine_payload_circuit (AffineMap.id Bool (BitString 2))⟩

/-! ### Affine-controller iteration bounds -/

-- Fixed-power, polynomial-budget, and variable-time iteration bounds for affine-payload
-- controlled maps across zero-width and positive-width controllers and payloads.
example (a₀ : BitString 0 → (BitString 2 →ᵃ[Bool] BitString 2))
    (g : BitString 1 → BitString 1)
    (a₁ : BitString 1 → (BitString 0 →ᵃ[Bool] BitString 0))
    (a₂ : BitString 1 → (BitString 1 →ᵃ[Bool] BitString 1))
    (a : BitString 1 → (BitString 2 →ᵃ[Bool] BitString 2)) (T : ℕ) :
    (∃ c : Circuit signature (0 + 2) (0 + 2),
      c.Computes interpretation ((controlledBits id (fun u => a₀ u))^[T]) ∧ c.size ≤ 43) ∧
    (∃ c : Circuit signature (1 + 0) (1 + 0),
      c.Computes interpretation ((controlledBits g (fun u => a₁ u))^[0]) ∧ c.size ≤ 16) ∧
    (∃ c : Circuit signature (1 + 1) (1 + 1),
      c.Computes interpretation ((controlledBits g (fun u => a₂ u))^[T]) ∧
      c.size ≤ affineControllerBudget 1 1) ∧
    (∃ c : Circuit signature (1 + 2) (1 + 2),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ 32 * 1 * (1 + 2 + 1) ^ (1 + 2)) ∧
    (∃ c : Circuit signature ((1 + 2) + 0) (1 + 2),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) 0) ∧
      c.size ≤ 0) ∧
    ∃ c : Circuit signature ((1 + 2) + 3) (1 + 2),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) 3) ∧
      c.size ≤ 3 * (affineControllerBudget 1 2 + 4 * (1 + 2)) :=
  ⟨by simpa [affineControllerBudget] using affine_controller_power id a₀ T,
    by simpa [affineControllerBudget] using affine_controller_power g a₁ 0,
    affine_controller_power g a₂ T,
    affine_controller_polynomial g a 1 1 (by decide) T,
    by simpa using affine_controller_variable_time g a 0,
    affine_controller_variable_time g a 3⟩

/-! ### Axiom guards -/

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledMap_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledMap_iterate

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledPayload_mem' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledPayload_mem

/--
info: 'Cslib.Circuits.Boolean.Iteration.controlledBits_iterate' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms controlledBits_iterate

end ComplexityTests.AffineController
