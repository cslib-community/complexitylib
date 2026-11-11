/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Privacy

/-! # Half-gates garbling: checked instances

A two-gate circuit `(x₀ ∧ x₁) ⊕ x₀` garbled with labels in `ZMod 2 × Bool`: its garbled table has
two ciphertexts, for its AND gate only; the garbled circuit evaluates correctly on every input, by
computation; an XOR-only circuit has an empty table; and the correctness, simulator and privacy
theorems instantiated with the identity tweak map. -/

namespace CslibFrontierTests.HalfGates

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling.HalfGates

/-- `(x₀ ∧ x₁) ⊕ x₀`, that is `x₀ ∧ ¬x₁`. -/
def andXor : Circuit signature 2 1 :=
  ⟨(Program.empty.gate ⟨Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Op.xor, ![Wire.gate 0, Wire.input 0]⟩, fun _ => Wire.gate 1⟩

/-- `x₀ ⊕ x₁`. -/
def xorC : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨Op.xor, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩

/-- A toy tweakable hash on `ZMod 2 × Bool`. It is not correlation robust; it only makes the
correctness and privacy statements concrete. -/
def toyH (a : ZMod 2 × Bool) (t : Slot andXor) : ZMod 2 × Bool := (a.1 + 1, a.2 && t.2)

/-- Fixed input zero labels. -/
def toyZ : Fin 2 → ZMod 2 × Bool := fun i => (0, decide (i = 0))

theorem add_self_zmod2 : ∀ k : ZMod 2, k + k = 0 := by decide

-- The circuit computes `x₀ ∧ ¬x₁`.
example : ∀ x : Fin 2 → Bool, andXor.eval interpretation x = ![x 0 && !x 1] := by
  decide

-- One AND gate and one XOR gate: two ciphertexts.
example : Fintype.card (Slot andXor) = 2 := by
  decide

-- XOR gates are free: an XOR-only circuit has an empty garbled table.
example : Fintype.card (Slot xorC) = 0 := by
  decide

-- The garbled circuit evaluates to `x₀ ∧ ¬x₁` on every input, by computation.
example : ∀ x : Fin 2 → Bool,
    (garbleWith andXor toyH id 1 toyZ).run toyH id x = ![x 0 && !x 1] := by
  decide

-- The general correctness theorem specializes to the same statement.
example (R : ZMod 2) (Z : Fin 2 → ZMod 2 × Bool) (x : Fin 2 → Bool) :
    (garbleWith andXor toyH id R Z).run toyH id x = andXor.eval interpretation x :=
  Garbled.run_garbleWith andXor add_self_zmod2 toyH id R Z x

-- Simulated views decode to the requested output.
example (y : Fin 1 → Bool) (X : Fin 2 → ZMod 2 × Bool) (ct : Slot andXor → ZMod 2 × Bool) :
    (simulateWith andXor toyH id y X ct).run toyH id = y :=
  View.run_simulateWith andXor toyH id y X ct

-- Privacy with the identity tweak map: the distinguishing advantage is the CCR advantage of the
-- reduction.
example (x : Fin 2 → Bool) (D : View andXor (ZMod 2) → ProbComp Bool) :
    Game.advantage (realGame andXor toyH id x D) (simGame andXor toyH id x D) =
      Garbling.CorrelationRobust.advantageLabel toyH (reduction andXor toyH id x D) :=
  advantage_realGame_simGame andXor toyH id x add_self_zmod2 Function.injective_id D

end CslibFrontierTests.HalfGates
