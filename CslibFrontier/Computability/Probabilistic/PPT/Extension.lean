/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Extending efficient programs to all words

An `IsPPTOn input output program` certificate fixes a machine on encoded inputs only. Running the
same machine, with the same clock, on an arbitrary word gives a program on all words that agrees
with `program` on every codeword `input a`. Its outputs on other words need not be codewords, so
a polynomial-time left inverse of the output encoding turns them into typed results.

This is the step that lets a reduction receive data it cannot decode efficiently, such as an
advice word holding an `input`-encoded value for an arbitrary encoding: the reduction passes the
word to the extension, which reads it exactly as the original machine would. In the same way, a
typed adversary whose input encoding is a layout of words, such as the tuple of field words
`enc_structure` gives a record, is literally a PPT adversary on that layout run on its input's
words. A word-level assumption then applies to it directly, with no congruence argument for the
game it plays.

## Main results

* `Cslib.Probability.IsPPTOn.exists_extension`: a uniform PPT program on all words agreeing with
  the original program on its codewords.
* `Cslib.Probability.IsPPTOn.exists_bool_extension`: the same for a Boolean program, which needs
  no decoder.
* `Cslib.Probability.IsPPTOn.exists_factor`, `Cslib.Probability.IsPPTOn.exists_bool_factor`: a
  program whose codewords are those of a word layout factors through that layout.
-/

public section

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
  congr 1 with b : 1
  exact hleft b

/-- **Extension of a Boolean program to all words.** A uniform strict PPT program with a Boolean
answer extends to a uniform strict PPT program on all words that agrees with it on every codeword.
The extension tests whether the original machine outputs `[true]`. This is how a typed
distinguisher is compared with one quantified over words. -/
theorem IsPPTOn.exists_bool_extension {program : α → ProbComp Bool}
    (h : IsPPTOn input encBool program) :
    ∃ extension : List Bool → ProbComp Bool, IsPPTOn encBits encBool extension ∧
      ∀ a, ProbComp.eval (extension (input a)) = ProbComp.eval (program a) :=
  h.exists_extension (ComputableInPolyTime.beq ComputableInPolyTime.id'
    (ComputableInPolyTime.const [true])) fun b => by cases b <;> rfl

/-- **Factoring through a word layout.** Suppose every input's codeword `input a` is the codeword
`words (toWords a)` of a value of a coarser type `γ`, such as the tuple of words of a structure
whose fields are encoded words. Then a uniform strict PPT program on `α` is a uniform strict PPT
program `W` on `γ` precomposed with `toWords`, given a polynomial-time left inverse of the output
encoding. Off the range of `toWords`, `W` runs the extension (`exists_extension`).

The equation `program a = W (toWords a)` is literal, not distributional, so a client can replace a
typed adversary by `W` in any game without a congruence argument for that game. -/
theorem IsPPTOn.exists_factor {γ : Type} {words : γ ↪ List Bool} {toWords : α → γ}
    (hinput : ∀ a, input a = words (toWords a)) {program : α → ProbComp β}
    (h : IsPPTOn input output program) {decode : List Bool → β}
    (hdecode : ComputableInPolyTime decode encBits output) (hleft : ∀ b, decode (output b) = b) :
    ∃ W : γ → ProbComp β, IsPPTOn words output W ∧ ∀ a, program a = W (toWords a) := by
  obtain ⟨extension, hextension, heq⟩ := h.exists_extension hdecode hleft
  have hinj : Function.Injective toWords := fun a a' haa' =>
    input.injective (by rw [hinput, hinput, haa'])
  refine ⟨Function.extend toWords program fun g => extension (words g),
    (hextension.preprocess ComputableInPolyTime.id'.encoding_comp).congr fun g => ?_,
    fun a => (hinj.extend_apply _ _ a).symm⟩
  by_cases hg : ∃ a, toWords a = g
  · obtain ⟨a, rfl⟩ := hg
    rw [hinj.extend_apply, ← hinput, heq]
  · rw [Function.extend_apply' _ _ _ hg]

/-- **Factoring a Boolean program through a word layout.** `exists_factor` for a Boolean program,
which needs no decoder. This is how a typed distinguisher becomes a distinguisher on words: the
word distinguisher `W` run on `toWords a` *is* the typed one at `a`. -/
theorem IsPPTOn.exists_bool_factor {γ : Type} {words : γ ↪ List Bool} {toWords : α → γ}
    (hinput : ∀ a, input a = words (toWords a)) {program : α → ProbComp Bool}
    (h : IsPPTOn input encBool program) :
    ∃ W : γ → ProbComp Bool, IsPPTOn words encBool W ∧ ∀ a, program a = W (toWords a) :=
  h.exists_factor hinput (ComputableInPolyTime.beq ComputableInPolyTime.id'
    (ComputableInPolyTime.const [true])) fun b => by cases b <;> rfl

end Cslib.Probability
