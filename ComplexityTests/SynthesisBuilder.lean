/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Word
import Complexity.Tactic.Synthesis
import Mathlib.Tactic.FinCases

/-!
# Synthesis builder clients

Sharing, zero-cost reuse, fixed gate budgets, indexed bundles, and failed availability queries.
-/

namespace ComplexityTests.SynthesisBuilder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

-- Build the negated input once and use it in two distinct outputs: three gates total.
example : ∃ c : Circuit signature 3 2,
    c.Computes interpretation (fun x => ![!x 0 && x 1, !x 0 || x 2]) ∧ c.size ≤ 3 := by
  let b := Synthesis.Builder.start interpretation (inputs 3)
  let shared : BooleanFunction 3 := fun x => !x 0
  let b := b.add (Synthesis.of_mem (f := fun x => x 0) (by synthesis_available) |>.not)
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).and
    (Synthesis.of_mem (f := fun x => x 1) (by synthesis_available)))
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).or
    (Synthesis.of_mem (f := fun x => x 2) (by synthesis_available)))
  synthesis_step b using Synthesis.of_mem (f := shared)
  have hcost : b.cost = 3 := rfl
  fail_if_success
    have := b.finish (t := {shared}) (k := 2) (by synthesis_available) (by omega)
  have h := b.finish (k := 3)
    (t := Set.range fun i x => (![!x 0 && x 1, !x 0 || x 2] : BitString 2) i)
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> synthesis_available) (by omega)
  exact h.exists_circuit_outputs

-- An earlier indexed family remains available after an unrelated gate is appended.
example {n k w : ℕ} (records : Fin k → BitString n → BitVec w) (j : Fin k) :
    let b := (Synthesis.Builder.start interpretation (⋃ i, wordWires (records i))).add
      (Synthesis.const false)
    wordWires (records j) ⊆ b.wires := by
  intro b
  synthesis_available

-- Finding wires cannot synthesize a negation or choose an element of an empty bundle.
example : True := by
  fail_if_success
    have : (fun x : BitString 1 => !x 0) ∈ inputs 1 := by synthesis_available
  fail_if_success
    have : (fun _ : BitString 0 => false) ∈ inputs 0 := by synthesis_available
  trivial

-- `Synthesis.extend` keeps everything built so far and names each new family explicitly. Starting
-- from the sources, a negation and a conjunction that reuses it cost two gates.
example : Synthesis interpretation (inputs 2)
    ((inputs 2 ∪ {fun x : BitString 2 => !x 0}) ∪ {fun x => !x 0 && x 1}) 2 := by
  have S0 : Synthesis interpretation (inputs 2) (inputs 2) 0 := Synthesis.of_subset le_rfl
  have S1 := S0.extend {fun x : BitString 2 => !x 0}
    (Synthesis.of_mem (f := fun x => x 0) (by synthesis_available)).not
  have S2 := S1.extend {fun x : BitString 2 => !x 0 && x 1}
    ((Synthesis.of_mem (f := fun x : BitString 2 => !x 0) (by synthesis_available)).and
      (Synthesis.of_mem (f := fun x => x 1) (by synthesis_available)))
  exact S2

end ComplexityTests.SynthesisBuilder
