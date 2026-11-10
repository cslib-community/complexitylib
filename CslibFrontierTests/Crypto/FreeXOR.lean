/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR

/-! # Free-XOR garbling: checked instances

A circuit with one XOR and one AND gate, garbled with one-bit keys and a toy hash: garbling is
correct on every input, only the AND gate has rows, and the privacy hypotheses are satisfiable. -/

@[expose] public section

namespace CslibFrontierTests.FreeXOR

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Garbling.FreeXOR

/-- Binary XOR and AND. -/
inductive Op | xor | and

/-- Both operations are binary. -/
abbrev signature : Signature := ⟨Op, fun _ => 2⟩

/-- XOR is addition in `Bool`. -/
def interpretation : Interpretation signature Bool
  | .xor, v => v 0 + v 1
  | .and, v => v 0 && v 1

/-- Outputs `(x₀ + x₁) ∧ x₀` and `x₀ + x₁`. -/
def xorAndC : Circuit signature 2 2 :=
  ⟨(Program.empty.gate ⟨Op.xor, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Op.and, ![Wire.gate 0, Wire.input 0]⟩, ![Wire.gate 1, Wire.gate 0]⟩

/-- Only the XOR gate is free. -/
def free : Fin xorAndC.size → Bool := ![true, false]

/-- A toy hash on one-bit keys, not correlation robust: it makes the statements concrete. -/
def toyH (k : Bool) (_ : GarbledSlot xorAndC.topology free) : Bool × Bool := (k, k)

theorem hfree : ∀ g, free g = true →
    ∀ v, interpretation (xorAndC.program.lines g).op v = ∑ k, v k := by
  intro g hg v
  fin_cases g
  exacts [(Fin.sum_univ_two v).symm, absurd hg (by decide)]

-- Garbling is correct on every input, by computation.
example : ∀ x, (garbleWith xorAndC interpretation toyH id true
    fun w => (decide (w = .input 1), decide (w = .gate (1 : Fin 2)))).run toyH id x =
      ![x 0 + x 1 && x 0, x 0 + x 1] := by
  decide

variable (D : View xorAndC.topology free Bool → ProbComp Bool) (x : Fin 2 → Bool)

-- Eight slots (four AND rows of two; the XOR gate has none): at most eight queries.
example : (reduction xorAndC interpretation toyH id x D).IsQueryBounded 8 := by
  have h := isQueryBounded_reduction xorAndC interpretation toyH id x D
  rwa [show Fintype.card (GarbledSlot xorAndC.topology free) = 8 by decide] at h

-- Privacy applies with injective tweaks; with the toy hash the right side is not small.
example : Game.advantage (realGame xorAndC interpretation toyH id x D)
      (simGame xorAndC interpretation toyH id x D) =
    Garbling.CorrelationRobust.advantage toyH (reduction xorAndC interpretation toyH id x D) :=
  advantage_realGame_simGame xorAndC interpretation toyH id x D hfree (by decide)
    Function.injective_id

end CslibFrontierTests.FreeXOR
