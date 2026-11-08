/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Primitives.Garbling.Privacy
import Cslib.Computability.Circuit.Boolean.Basic

/-! # Garbled circuits: checked instances

A one-gate AND circuit garbled with one-bit keys, evaluated on every input; the size of its
garbled table; a topology that is not ordered; the identity PRF with zero advantage; and the
privacy bound instantiated with injective tweaks. -/

namespace ComplexityTests.Garbling

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling

/-- `x₀ ∧ x₁`. -/
def andC : Circuit Boolean.signature 2 1 :=
  ⟨Program.empty.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩

/-- A toy keyed function on one-bit keys: the mask is the key, with the tweak ignored. -/
def toyF (k : Bool) (_ : Slot andC.topology) : Bool × Bool := (k, k)

/-- Fixed wire keys. -/
def toyKey : Wire 2 andC.size × Bool → Bool := fun p => p.2 || decide (p.1 = Wire.input 1)

/-- Fixed permutation bits. -/
def toyPerm : Wire 2 andC.size → Bool := fun w => decide (w = Wire.input 0)

-- One gate of arity two: four rows of two argument slots each.
example : Fintype.card (Row andC.topology) = 4 ∧ Fintype.card (Slot andC.topology) = 8 := by
  decide

-- The garbled circuit evaluates to `x₀ ∧ x₁` on every input, by computation.
example : ∀ x : Fin 2 → Bool,
    (garbleWith andC Boolean.interpretation toyF id toyKey toyPerm).run toyF id x =
      ![x 0 && x 1] := by
  decide

-- The general correctness theorem specializes to the same statement.
example (key : Wire 2 andC.size × Bool → Bool) (perm : Wire 2 andC.size → Bool)
    (x : Fin 2 → Bool) :
    (garbleWith andC Boolean.interpretation toyF id key perm).run toyF id x =
      andC.eval Boolean.interpretation x :=
  Garbled.run_garbleWith andC Boolean.interpretation toyF id key perm x

-- Simulated views decode to the requested output.
example (A : Wire 2 andC.size → Bool × Bool) (R : Row andC.topology → Bool × Bool)
    (y : Fin 1 → Bool) : (simulateWith andC.topology toyF id y A R).run toyF id = y :=
  View.run_simulateWith andC.isOrdered_topology toyF id y A R

/-- A topology whose only gate reads itself. -/
def loopTopology : Circuit.Topology 0 1 1 where
  arity _ := 1
  wires _ _ := Wire.gate 0
  outputs _ := Wire.gate 0

example : ¬ loopTopology.IsOrdered := fun h => (Nat.lt_irrefl _) (h 0 (0 : Fin 1))

-- Each reduction for the AND circuit queries its oracle exactly once per argument slot.
example (D : View andC.topology Bool → ProbComp Bool) (j : ℕ) :
    (reduction andC Boolean.interpretation toyF id 0 D j).IsQueryBounded 8 := by
  have h := isQueryBounded_reduction andC Boolean.interpretation toyF id 0 D j
  rwa [show Fintype.card (Slot andC.topology) = 8 by decide] at h

-- The identity PRF, keyed by the whole function, has advantage zero.
example (A : PRF.Adversary (Fin 2) Bool) : PRF.advantage (fun (f : Fin 2 → Bool) x => f x) A = 0 :=
  Game.advantage_self _

-- The privacy bound applies to the AND circuit with injective tweaks, for every distinguisher.
example (D : View andC.topology Bool → ProbComp Bool) (x : Fin 2 → Bool) :
    Game.advantage (realGame andC Boolean.interpretation toyF id x D)
        (simGame andC Boolean.interpretation toyF id x D) ≤
      ∑ j ∈ Finset.range 3,
        PRF.advantage toyF (reduction andC Boolean.interpretation toyF id x D j) :=
  advantage_realGame_simGame_le andC Boolean.interpretation toyF id Function.injective_id x D

end ComplexityTests.Garbling
