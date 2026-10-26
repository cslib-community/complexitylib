/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.WordExtraction
import Complexity.Crypto.Computational.Pseudoentropy.WordSeedExtraction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PPT

/-! Extraction clients: computed dimensions, encodings, missing callbacks and malformed inputs. -/

namespace ComplexityTests.PseudoentropyExtraction

open Cslib Cslib.Probability Cslib.Crypto.Pseudoentropy Cslib.BitString Turing.MultiTapeTM

example : ComputableTidilyInPolyTime (List.flatten : List (List Bool) → List Bool)
    (encList encBits) encBits := by fun_prop

example : ComputableTidilyInPolyTime
    (fun input : Bool × List (List Bool) =>
      let words := input.2.map (fun word => padWord word.length word)
      words.flatten)
    (encPair encBool (encList encBits)) encBits := by polytime

-- Dimensions and the preparation function may capture the complete encoded input.
example : IsPPTOn (encPair encUnary (encList (encPair encBool encBits)))
    (encPair (encList encBool) (encPair encBits encBits))
    (fun input : ℕ × List (Bool × List Bool) =>
      extractMatrixLabels input.1 (input.1 + 1)
        (fun words => (words.map (padWord input.1)).flatten) input.2) := by ppt

example : IsPPTOn (encPair encUnary (encList (encPair encBits encBool)))
    (encPair (encList encBits) (encPair encBits encBits))
    (fun input : ℕ × List (List Bool × Bool) =>
      let samples := input.2
      let count := samples.length
      extractWordLabels count (input.1 + 1) samples) := by ppt

-- The same program spelled with an explicit seed bind has the same compositional certificate.
set_option maxHeartbeats 12000 in
-- A tighter budget guards against duplicated fun_prop entries exhausting the default 200000.
example : IsPPTOn (encPair encUnary (encList (encPair encBits encBool)))
    (encPair (encList encBits) (encPair encBits encBits))
    (fun input : ℕ × List (List Bool × Bool) => do
      let seed ← sampleList ((input.1 + 1) * input.2.length)
      return (input.2.map Prod.fst, seed,
        LinearHash.wordHash (input.1 + 1) seed
          (listRow input.2.length 0 (input.2.map Prod.snd)))) := by ppt

example : IsPPTOn (encPair encBool (encPair encUnary (encList encBits))) encBits
    (fun input : Bool × ℕ × List (List Bool) =>
      extractWordObservations input.2.1 (input.2.1 + 1) input.2.2) := by ppt

example : IsPPTOn
    (encPair encUnary (encList (encPair (encPair encBits encBool) encBits)))
    (encPair (encList (encPair encBits encBool)) (encPair encBits encBits))
    (fun input : ℕ × List ((List Bool × Bool) × List Bool) =>
      extractWordSeeds input.2.length input.1 (input.1 + 1) input.2) := by ppt

-- An arbitrary preparation callback is not silently certified.
example (prepare : List Bool → List Bool)
    (hprepare : ComputableTidilyInPolyTime prepare encBits encBits) :
    IsPPTOn (encList (encPair encBits encBool))
      (encPair (encList encBits) (encPair encBits encBits))
      (fun samples => extractMatrixLabels samples.length 1 prepare samples) := by
  fail_if_success (clear hprepare; ppt)
  ppt

-- Normalization includes short inputs, truncation and zero-width matrices.
example : listRow 3 0 [true] = [true, false, false] := by decide
example : listRow 1 0 [true, false] = [true] := by decide
example : LinearHash.wordHash 2 [] [] = [false, false] := by decide

-- Seed length depends on the declared width, even when the sample list is malformed.
example {output : List (List Bool) × List Bool × List Bool}
    (h : output ∈ (ProbComp.eval (extractWordLabels 3 2 [([true], false)])).support) :
    output.1 = [[true]] ∧ output.2.1.length = 6 ∧ output.2.2.length = 2 :=
  extractMatrixLabels_result 3 2 id [([true], false)] h

-- Variable-length observations remain distinct after padding; the full matrix is public.
example {output : List Bool}
    (h : output ∈ (ProbComp.eval
      (extractWordObservations 2 3 [[], [true], [false, true]])).support) :
    output.length = 48 := by
  exact length_extractWordObservations 2 3 [[], [true], [false, true]] (by simp) h

example {output : List Bool}
    (h : output ∈ (ProbComp.eval (extractWordObservations 2 0 [[], [true]])).support) :
    output = [] := by
  apply List.eq_nil_of_length_eq_zero
  exact length_extractWordObservations 2 0 [[], [true]] (by simp) h

end ComplexityTests.PseudoentropyExtraction
