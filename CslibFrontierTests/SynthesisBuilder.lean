/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Word
import CslibFrontier.Tactic.Synthesis
import Mathlib.Tactic.FinCases

/-!
# Synthesis builder clients

Sharing, zero-cost reuse, fixed gate budgets, indexed bundles, and failed availability queries.
-/

namespace CslibFrontierTests.SynthesisBuilder

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

-- Finding wires cannot synthesize a negation or choose an element of an empty bundle. The
-- failure says what the tactic follows and how to add the missing wires.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : (fun x : BitString 1 => !x 0) ∈ inputs 1 := by synthesis_available

/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : (fun _ : BitString 0 => false) ∈ inputs 0 := by synthesis_available

-- `synthesis_step` reports the same failure when a premise of the rule is not available.
/-- error: synthesis_available could not find these wires among the available ones. -/
#guard_msgs (substring := true) in
example : True := by
  let b := Synthesis.Builder.start interpretation (inputs 1)
  synthesis_step b using Synthesis.of_mem (f := fun x : BitString 1 => !x 0)
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

-- A chain of `Synthesis.extend` steps over words accumulates a union of equal-width word families.
-- `synthesis_available` finds the sources by matching union members syntactically. Comparing the
-- members' bits at default transparency instead unfolds the word operations, which costs about
-- ten thousand heartbeats here and exhausts the default budget on Karatsuba's fifteen-step chain.
set_option maxHeartbeats 3000 in
-- A small budget: the syntactic search must not fall back to comparing the families' bits.
example {n w : ℕ} (a b : BitString n → BitVec w) (s : Set (BooleanFunction n))
    (ha : wordWires a ⊆ s) (i : ℕ) (hi : (fun x => (b x).getLsbD i) ∈ s) :
    wordWires a ⊆ s ∪
      wordWires (fun x => a x + b x) ∪
      wordWires (fun x => a x - b x) ∪
      wordWires (fun x => a x &&& b x) ∪
      wordWires (fun x => a x ||| b x) ∪
      wordWires (fun x => a x ^^^ b x) ∪
      wordWires (fun x => a x <<< 1) ∪
      wordWires (fun x => a x >>> 1) ∪
      wordWires (fun x => b x + a x) ∪
      wordWires (fun x => a x * b x) ∪
      wordWires (fun x => ~~~a x) ∪
      wordWires (fun x => (a x).setWidth w + b x) ∪
      wordWires (fun x => b x - a x) ∧
    (fun x => (b x).getLsbD i) ∈ s ∪
      wordWires (fun x => a x + b x) ∪
      wordWires (fun x => a x - b x) ∪
      wordWires (fun x => a x &&& b x) ∪
      wordWires (fun x => a x ||| b x) ∪
      wordWires (fun x => a x ^^^ b x) ∪
      wordWires (fun x => a x <<< 1) ∪
      wordWires (fun x => a x >>> 1) ∪
      wordWires (fun x => b x + a x) ∪
      wordWires (fun x => a x * b x) ∪
      wordWires (fun x => ~~~a x) ∪
      wordWires (fun x => (a x).setWidth w + b x) ∪
      wordWires (fun x => b x - a x) :=
  ⟨by synthesis_available, by synthesis_available⟩

-- `synthesis_union` alone does not unfold `Builder.add`, so it cannot see the sources inside a
-- builder's `wires`; `synthesis_available` falls back to the general search.
example {n k w : ℕ} (records : Fin k → BitString n → BitVec w) (j : Fin k) :
    let b := (Synthesis.Builder.start interpretation (⋃ i, wordWires (records i))).add
      (Synthesis.const false)
    wordWires (records j) ⊆ b.wires := by
  intro b
  fail_if_success synthesis_union
  synthesis_available

end CslibFrontierTests.SynthesisBuilder
