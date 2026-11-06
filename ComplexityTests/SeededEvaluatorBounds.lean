/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.CoinTape.Bounds
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PPT

/-!
# Joint seed and output envelopes

The sampler returns a fresh random word of the input's length. The common envelope gives exact
replay on longer tapes and valid length even on an empty tape; zero-length input always returns
the empty word. Both Boolean outcomes remain possible at length one.
-/

namespace ComplexityTests.SeededEvaluatorBounds

open Cslib Cslib.Probability Turing.MultiTapeTM

private noncomputable def program (word : List Bool) : ProbComp (List Bool) :=
  BitString.sampleList word.length

private theorem program_ppt : IsPPTOn encBits encBits program := by
  unfold program
  ppt

private theorem supported_length (word result : List Bool)
    (hresult : result ∈ (ProbComp.eval (program word)).support) : result.length = word.length := by
  rw [program, BitString.eval_sampleList] at hresult
  exact BitString.length_of_mem_support_uniformList hresult

example : [false] ∈ (ProbComp.eval (program [true])).support ∧
    [true] ∈ (ProbComp.eval (program [true])).support := by
  simp only [program, BitString.eval_sampleList, BitString.mem_support_uniformList_iff]
  decide

example : [false, true] ∉ (ProbComp.eval (program [true])).support := by
  intro h
  have hlength := supported_length [true] [false, true] h
  contradiction

-- One native evaluator works for all lengths. Short tapes retain support, and doubling the
-- common envelope preserves the exact original distribution without consuming all the padding.
example : ∃ (c d : ℕ) (evaluate : List Bool → List Bool → List Bool),
    ComputableInPolyTime (fun (word, tape) => evaluate word tape)
      (encPair encBits encBits) encBits ∧
    (∀ word tape, (evaluate word tape).length = word.length) ∧
    (∀ tape, evaluate [] tape = []) ∧
    (∀ word, BitString.uniformList word.length =
      (BitString.uniformList (2 * (c * (word.length + 1) ^ d))).map (evaluate word)) ∧
    ∀ word : List Bool, word.length ≤ c * (word.length + 1) ^ d := by
  obtain ⟨c, d, evaluate, hevaluate, hsupport, hlaw, hlength⟩ :=
    program_ppt.exists_total_seeded_evaluator_with_length
  refine ⟨c, d, evaluate, hevaluate, ?_, ?_, ?_, ?_⟩
  · intro word tape
    exact supported_length word _ (hsupport word tape)
  · intro tape
    exact List.eq_nil_of_length_eq_zero (supported_length [] _ (hsupport [] tape))
  · intro word
    simpa only [program, BitString.eval_sampleList, encBits_apply] using
      hlaw word (2 * (c * (word.length + 1) ^ d)) (by simp only [encBits_apply]; omega)
  · intro word
    apply hlength word word
    simp only [program, BitString.eval_sampleList, BitString.mem_support_uniformList_iff]

end ComplexityTests.SeededEvaluatorBounds
