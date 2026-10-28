/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Crypto.Computational.GGM.Evaluation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Functional pipelines use the ordinary monadic interface and existing deterministic proofs. -/

namespace ComplexityTests.PPTComposition

open Cslib Cslib.Probability Turing.MultiTapeTM

-- The result length can depend on randomness, and can be zero.
example : IsPPTOn encBits encBits (fun _ => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then [true, false, true] else [])) := by
  fun_prop

example : IsPPTOn encBits encBool (fun _ => do
    let bit ← ProbComp.uniform Bool
    pure (!bit)) := by
  fun_prop

example :
    IsPPTOn encUnary encBits (fun n => do
      let b ← BitString.sampleList n
      let bit ← ProbComp.uniform Bool
      pure (bit :: b)) := by
  fun_prop

-- GGM's existing evaluator proof works after a certified seed/path sampler.
example {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    IsPPTOn encUnary encBits (fun n => do
      let seed ← BitString.sampleList n
      let path ← BitString.sampleList n
      pure (Crypto.GGM.eval generator seed path)) := by
  fun_prop

-- Preprocessing can traverse unbounded encoded inputs before invoking a certified sampler.
example :
    IsPPTOn encBits encBits (fun word => BitString.sampleList word.reverse.length) := by
  fun_prop

-- Composition does not turn arbitrary finite-uniform sampling into strict fair-coin PPT.
example : True := by
  let encFin3 : Fin 3 ↪ List Bool := Fin.valEmbedding.trans encNat
  fail_if_success have : IsPPTOn encBits encFin3 (fun _ => ProbComp.uniform (Fin 3)) := by fun_prop
  trivial

-- The callback uses an unbounded original word after sampling.
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  fun_prop

-- Both samples depend on input data retained across earlier effects.
example {sample : List Bool → ProbComp Bool} (hsample : IsPPTOn encBits encBool sample) :
    IsPPTOn encBits encBits (fun word => do
      let first ← sample word
      let second ← sample word.reverse
      pure (first :: second :: word)) := by
  fun_prop

-- GGM consumes the original query path after a seed has been sampled.
example {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    IsPPTOn encBits encBits (fun path => do
      let seed ← BitString.sampleList path.length
      pure (Crypto.GGM.eval generator seed path)) := by
  fun_prop

-- Branch selection depends on the unbounded input, and both branches are probabilistic.
example :
    IsPPTOn encBits encBits (fun word =>
      if word = [] then BitString.sampleList 1 else BitString.sampleList word.reverse.length) := by
  fun_prop

end ComplexityTests.PPTComposition

-- Plain deterministic postprocessing retains the full arbitrary encoded contract.
example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} {sample : α → Cslib.ProbComp β} {finish : β → γ}
    (hs : Cslib.Probability.IsPPTOn input middle sample)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime finish middle output) :
    Cslib.Probability.IsPPTOn input output (fun a => finish <$> sample a) := by
  fail_if_success (clear hf; fun_prop)
  fun_prop
