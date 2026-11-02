/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Extending efficient programs to all words

An `IsPPTOn input output program` certificate fixes a machine on encoded inputs only. Running the
same machine, with the same clock, on an arbitrary word gives a program on all words that agrees
with `program` on every codeword `input a`. Its outputs on other words need not be codewords, so
a polynomial-time left inverse of the output encoding turns them into typed results.

This is the step that lets a reduction receive data it cannot decode efficiently, such as an
advice word holding an `input`-encoded value for an arbitrary encoding: the reduction passes the
word to the extension, which reads it exactly as the original machine would.

## Main results

* `Cslib.Probability.IsPPTOn.exists_extension`: a uniform PPT program on all words agreeing with
  the original program on its codewords.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- **Extension to all words.** A uniform strict PPT program on encoded inputs extends to a
uniform strict PPT program on all words that agrees with it on every codeword, given a
polynomial-time left inverse `decode` of the output encoding. The extension runs the original
machine; on words outside the range of `input` its results are whatever `decode` makes of the
machine's output. -/
theorem IsPPTOn.exists_extension {program : α → ProbComp β} (h : IsPPTOn input output program)
    {decode : List Bool → β} (hdecode : ComputableInPolyTime decode encBits output)
    (hleft : ∀ b, decode (output b) = b) :
    ∃ extension : List Bool → ProbComp β, IsPPTOn encBits output extension ∧
      ∀ a, ProbComp.eval (extension (input a)) = ProbComp.eval (program a) := by
  obtain ⟨k, State, hfinite, machine, c, d, hmachine⟩ := isPPTOn_iff_encoded.mp h
  have hrun : IsPPTOn encBits encBits
      (fun word => machine.runClosed (c * (word.length + 1) ^ d) word) :=
    ⟨k, State, hfinite, machine, c, d, fun word => by
      simp only [encBits, Function.Embedding.coe_refl, PMF.map_id, id]⟩
  refine ⟨fun word => decode <$> machine.runClosed (c * (word.length + 1) ^ d) word,
    hrun.map hdecode, fun a => ?_⟩
  have hencoded := hmachine a
  simp only [encBits, Function.Embedding.coe_refl, PMF.map_id] at hencoded
  rw [ProbComp.eval_map, ← hencoded, ProbComp.eval_map, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id (ProbComp.eval (program a))]
  congr 1
  funext b
  exact hleft b

end Cslib.Probability
