/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-! # Direct plain loops without a tidy polynomial-time calculus -/

open Turing.MultiTapeTM

run_elab do
  let env ← Lean.getEnv
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.exists_onWords,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterateWhile,
      `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains name then throwError "unexpected high-level tidy predicate: {name}"

-- Direct plain loops: varying list foldl, captured-parameter foldlWith, unary-count iterateWith,
-- invariant-verified foldl_spec, zero-growth iterateWithInput_of_bounded_growth, and exponential
-- state-growth counterexample.
example :
    ComputableInPolyTime (fun word : List Bool => word.foldl Bool.xor false) encBits encBool ∧
    ComputableInPolyTime
      (fun p : Bool × List Bool => p.2.foldl (fun state bit => state ^^ (p.1 && bit)) false)
      (encPair encBool encBits) encBool ∧
    ComputableInPolyTime
      (fun p : ℕ × Bool => (fun state => state ^^ p.2)^[p.1] false)
      (encPair encUnary encBool) encBool ∧
    (ComputableInPolyTime (fun word : List Bool => word.foldl Bool.and true) encBits encBool ∧
      ∀ word : List Bool, word.foldl Bool.and true = word.all id) ∧
    ComputableInPolyTime (fun n : ℕ => Bool.not^[n] true) encUnary encBool ∧
    ¬ (∀ word : List Bool, ∀ i ≤ word.length,
      (((word.take i).foldl (fun state _ => state ++ state) [true]).length ≤ 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ComputableInPolyTime.foldl' (encA := encBool) (B := fun _ => 1)
      ComputableInPolyTime.id' (ComputableInPolyTime.const false)
      (ComputableInPolyTime.of_finite (fun p : Bool × Bool => Bool.xor p.1 p.2))
    · exact PolyBounded.const 1
    · simp
  · apply ComputableInPolyTime.foldlWith (encA := encBool) (encL := encBits)
      (encIn := encPair encBool encBits) (encB := encBool) (encP := encBool)
      (par := fun p : Bool × List Bool => p.1) (list := fun p => p.2)
      (init := fun _ => false) (step := fun par state bit => state ^^ (par && bit))
      (B := fun _ => 1)
      (ComputableInPolyTime.fst encBool encBits)
      (ComputableInPolyTime.snd encBool encBits) (ComputableInPolyTime.const false)
      (ComputableInPolyTime.of_finite
        (fun q : (Bool × Bool) × Bool => q.1.2 ^^ (q.1.1 && q.2)))
    · exact PolyBounded.const 1
    · simp
  · apply ComputableInPolyTime.iterateWith (encIn := encPair encUnary encBool)
      (encPar := encBool) (encState := encBool) (par := fun p : ℕ × Bool => p.2)
      (count := fun p => p.1) (init := fun _ => false) (step := fun par state => state ^^ par)
      (bound := fun _ => 1)
      (ComputableInPolyTime.snd encUnary encBool)
      (ComputableInPolyTime.fst encUnary encBool) (ComputableInPolyTime.const false)
      (ComputableInPolyTime.of_finite (fun q : Bool × Bool => q.2 ^^ q.1))
    · exact PolyBounded.const 1
    · simp
  · apply ComputableInPolyTime.foldl_spec (encA := encBool) (encL := encBits)
      (encIn := encBits) (encB := encBool) (list := id) (init := fun _ => true)
      (step := Bool.and) (size := fun _ => 1)
      ComputableInPolyTime.id' (ComputableInPolyTime.const true)
      (ComputableInPolyTime.of_finite (fun p : Bool × Bool => p.1 && p.2))
      (fun _ consumed state => state = consumed.all id)
    · simp
    · intro word consumed state value _ hs
      simp [List.all_append, hs]
    · exact PolyBounded.const 1
    · simp
  · apply ComputableInPolyTime.iterateWithInput_of_bounded_growth
      (count := id) (init := fun _ => true) (step := fun (_ : ℕ) state => !state)
      ComputableInPolyTime.id' (ComputableInPolyTime.const true)
      (ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.snd encUnary encBool))
      (growth := fun _ => 0)
    exact ⟨PolyBounded.const 0, by simp⟩
  · intro h
    have := h [false] 1 (by decide)
    simp at this
