/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT
import Complexity.Crypto.Computational.GGM.Evaluation


import Diag1155.Measure
/-! Uniform runtime-length sampling, its raw machine, and captured GGM evaluation. -/


diag1155_install
namespace ComplexityTests.ProbabilisticSampling

open Cslib Cslib.Probability Turing Turing.MultiTapeTM Turing.MultiTapePTM

example : ProbComp.eval (BitString.sampleList 0) = PMF.pure [] := by simp

-- Both symbol values count: the machine samples by raw input length.
example : ProbComp.eval (uniformListMachine.runClosed 3 [false, true]) =
    BitString.uniformList 2 := eval_uniformListMachine _

example : ∀ final ∈ (ProbComp.eval (uniformListMachine.runClosedConfigFrom 1
    (uniformListMachine.initialConfig []))).support, final.tapes.state = none :=
  uniformListMachine_halted []

example : ∀ final ∈ (ProbComp.eval (uniformListMachine.runClosedConfigFrom 3
    (uniformListMachine.initialConfig [false, true]))).support, final.tapes.state = none :=
  uniformListMachine_halted [false, true]

-- Writing the two bits has not yet consumed the final halting transition.
example : (ProbComp.eval (uniformListMachine.runClosedConfigFrom 2
    (uniformListMachine.initialConfig [false, true]))).map (fun final => final.tapes.state) =
    PMF.pure (some ()) := by
  simp [runClosedConfigFrom, runConfigFrom, MultiTapeMachine.runConfigFrom,
    MultiTapeMachine.initialConfig, uniformListMachine, Cfg.inputSymbol,
    MultiTapeMachine.Config.step, Action.apply, moveInputPos, Function.comp_def,
    PMF.map, PMF.bind_const]

example : IsPPTOn encUnary encBits BitString.sampleList := by ppt

-- The requested number of random bits may depend on the input.
example : IsPPTOn encBits encBits (fun word => BitString.sampleList (word.length + 2)) := by
  ppt

example : IsPPTOn encBits encBits (fun word => BitString.sampleList (word.length ^ 2)) := by
  ppt

-- Sampling exposes the count obligation to polytime's bounded-growth fold rule.
example : IsPPTOn encBits encBits (fun word =>
    BitString.sampleList (word.foldl (fun n bit => if bit then n + 1 else n) 0)) := by
  ppt

example : IsPPTOn encBits encBits (fun word => do
    let seed ← BitString.sampleList word.length
    pure (seed ++ word)) := by
  ppt

-- A standard cryptographic client: generate a key, then follow the original GGM path.
example (generator : List Bool → List Bool)
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    IsPPTOn encBits encBits (fun path => do
      let seed ← BitString.sampleList path.length
      pure (Crypto.GGM.eval generator seed path)) := by
  ppt

-- A binary count certificate alone cannot pay for writing that many random bits.
example (count : List Bool → ℕ)
    (_hcount : ComputableTidilyInPolyTime count encBits encNat) : True := by
  fail_if_success
    have : IsPPTOn encBits encBits (fun word => BitString.sampleList (count word)) := by ppt
  fail_if_success have : IsPPTOn encNat encBits BitString.sampleList := by ppt
  trivial

-- A computed count remains an ordinary plain certificate under arbitrary encoded inputs.
example {α : Type} {input : α ↪ List Bool} {count : α → ℕ}
    (hcount : ComputableInPolyTime count input encUnary) :
    IsPPTOn input encBits (fun a => BitString.sampleList (count a)) := by
  fail_if_success (clear hcount; ppt)
  ppt

end ComplexityTests.ProbabilisticSampling
