/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PPT
import Complexity.Crypto.Computational.GGM.Evaluation

/-! Ordinary probabilistic programs use `ppt`; deterministic callbacks reuse `polytime`. -/

namespace ComplexityTests.PPTTactic

open Cslib Cslib.Probability Turing.MultiTapeTM

example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt

-- The deterministic callback needs a bounded-growth fold rule after sampling.
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure ((bit :: word).foldl (fun reversed next => next :: reversed) [])) := by
  ppt

-- Deterministic captured folds also resolve abstract encoding instances through `ppt`.
example {γ α β : Type} (input : γ ↪ List Bool) (element : α ↪ List Bool)
    (stateEncoding : β ↪ List Bool) (listEncoding : List α ↪ List Bool)
    [ListEncoding element listEncoding] [SizedListEncoding element listEncoding]
    (list : γ → List α) (initial : γ → β) (step : γ → β → α → β)
    (hlist : ComputableTidilyInPolyTime list input listEncoding)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair input stateEncoding) element) stateEncoding)
    (growth : γ → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (stateEncoding (step x state value)).length ≤ (stateEncoding state).length + growth x) :
    IsPPTOn input stateEncoding
      (fun x => pure ((list x).foldl (fun state value => step x state value) (initial x))) := by
  ppt

-- Scans capture a sampled bit and reuse certificates at either fixed or runtime indices.
example (rounds : ℕ) (test : List Bool × Bool × ℕ → Bool)
    (htest : ComputableTidilyInPolyTime test
      (encPair encBits (encPair encBool encUnary)) encBool) :
    IsPPTOn encBits encBool (fun word => do
      let bit ← ProbComp.uniform Bool
      pure ((List.range rounds).all fun i => test (word, bit, i))) := by
  ppt

example (test : List Bool × Bool × ℕ → Bool)
    (htest : ComputableTidilyInPolyTime test
      (encPair encBits (encPair encBool encUnary)) encBool) :
    IsPPTOn encBits encBool (fun word => do
      let bit ← ProbComp.uniform Bool
      pure ((List.range word.length).any fun i => test (word, bit, i))) := by
  fail_if_success (clear htest; ppt)
  ppt

-- A local routine can take a tuple assembled from captured data.
example (sample : (List Bool × ℕ) × List Bool → ProbComp Bool)
    (hsample : IsPPTOn (encPair (encPair encBits encUnary) encBits) encBool sample) :
    IsPPTOn encBits encBool
      (fun word => sample ((word.reverse, word.length), word ++ word)) := by
  ppt

-- Curried callbacks leave a single argument-preparation goal after composition.
-- Sampling twice tests the captured caller through nested monadic continuations.
example (test : ℕ → ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary) encBits) encBool
      (fun input => test input.1.1 input.1.2 input.2)) :
    IsPPTOn (encPair encUnary encUnary) encBool (fun input : ℕ × ℕ => do
      let first ← BitString.sampleList input.1
      let second ← BitString.sampleList input.2
      test input.1 input.2 (first ++ second)) := by
  fail_if_success (clear htest; ppt)
  ppt

-- The same callback composes with a computed argument in ordinary let notation.
example (test : ℕ → ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary) encBits) encBool
      (fun input => test input.1.1 input.1.2 input.2)) :
    IsPPTOn (encPair encUnary encBits) encBool (fun input : ℕ × List Bool =>
      let word := input.2 ++ input.2
      test input.1 word.length word) := by
  ppt

-- The callback's first argument may use binary encoding; the sampled count remains unary.
example (test : ℕ → ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encNat encUnary) encBits) encBool
      (fun input => test input.1.1 input.1.2 input.2)) :
    IsPPTOn (encPair encNat encUnary) encBool (fun input : ℕ × ℕ => do
      let word ← BitString.sampleList input.2
      test input.1 input.2 word) := by
  ppt

-- Failure of the first encoding must leave the second local certificate usable.
example (sample : ℕ → ProbComp Bool)
    (_hUnary : IsPPTOn encUnary encBool sample) (hBinary : IsPPTOn encNat encBool sample) :
    IsPPTOn (encPair encNat encBool) encBool (fun pair => sample pair.1) := by
  ppt

-- The continuation needs unary iteration: an additional binary-output certificate must not
-- force that encoding onto the sampled value. This is the opposite side of a routine call.
set_option maxHeartbeats 12000 in
-- A reduced budget guards against exploring captured folds before a growth contract is available
-- on a rejected encoding branch.
example (sample : List Bool → ProbComp ℕ)
    (hUnary : IsPPTOn encBits encUnary sample) (_hBinary : IsPPTOn encBits encNat sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (_hBinary : IsPPTOn encBits encNat sample) (hUnary : IsPPTOn encBits encUnary sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (hUnary : IsPPTOn encBits encUnary sample) (_hBinary : IsPPTOn encBits encNat sample) :
    IsPPTOn encBits encBool (fun word =>
      (fun n => (List.range n).foldl (fun parity _ => !parity) true) <$> sample word) := by
  ppt

example (sample : List Bool → ProbComp ℕ)
    (_hBinary : IsPPTOn encBits encNat sample) (hUnary : IsPPTOn encBits encUnary sample) :
    IsPPTOn encBits encBool (fun word =>
      (fun n => (List.range n).foldl (fun parity _ => !parity) true) <$> sample word) := by
  ppt

-- Both sides have competing certificates; changing premise order alone cannot find the shared one.
example (shared samplerOnly continuationOnly : ℕ ↪ List Bool)
    (sample : List Bool → ProbComp ℕ) (next : List Bool → ℕ → ProbComp Bool)
    (hsShared : IsPPTOn encBits shared sample) (_hsOther : IsPPTOn encBits samplerOnly sample)
    (hnShared : IsPPTOn (encPair encBits shared) encBool (fun pair => next pair.1 pair.2))
    (_hnOther : IsPPTOn (encPair encBits continuationOnly) encBool
      (fun pair => next pair.1 pair.2)) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      next word n) := by
  ppt

example (shared samplerOnly continuationOnly : ℕ ↪ List Bool)
    (sample : List Bool → ProbComp ℕ) (next : List Bool → ℕ → Bool)
    (hsShared : IsPPTOn encBits shared sample) (_hsOther : IsPPTOn encBits samplerOnly sample)
    (hnShared : ComputableTidilyInPolyTime (fun pair => next pair.1 pair.2)
      (encPair encBits shared) encBool)
    (_hnOther : ComputableTidilyInPolyTime (fun pair => next pair.1 pair.2)
      (encPair encBits continuationOnly) encBool) :
    IsPPTOn encBits encBool (fun word => next word <$> sample word) := by
  ppt

-- Conditional fallback lets the deterministic fold rules prove the guard.
example : IsPPTOn encBits encBool (fun word =>
    if word.foldl (fun parity _ => !parity) true then ProbComp.uniform Bool else pure false) := by
  ppt

example : IsPPTOn encBits encBool (fun word =>
    if word.foldl (fun parity _ => !parity) true = false then
      ProbComp.uniform Bool else pure false) := by
  ppt

-- GGM keeps the original path available after a certified seed sampler.
example (sample : List Bool → ProbComp (List Bool)) (generator : List Bool → List Bool)
    (hsample : IsPPTOn encBits encBits sample)
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    IsPPTOn encBits encBits (fun path => do
      let seed ← sample path
      pure (Crypto.GGM.eval generator seed path)) := by
  ppt

private noncomputable def sampleTagged (word : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  pure (bit :: word)

@[program_certificate]
private theorem sampleTagged_ppt : IsPPTOn encBits encBits sampleTagged := by
  unfold sampleTagged
  ppt

attribute [irreducible] sampleTagged

example : IsPPTOn encBits encBits sampleTagged := by ppt

-- The named implementation stays folded inside a captured continuation and a conditional.
example : IsPPTOn encBits encBits (fun word => do
    let tagged ← sampleTagged word
    if word = [] then sampleTagged tagged else sampleTagged (tagged ++ word)) := by
  ppt

-- The same registered probabilistic certificate is compositional under fun_prop.
example : IsPPTOn encBits encBits (fun word => sampleTagged (word ++ word)) := by
  fun_prop

private noncomputable def sampleFixed (n : ℕ) (word : List Bool) : ProbComp (List Bool) :=
  sampleTagged (List.replicate n false ++ word)

@[program_certificate]
private theorem sampleFixed_zero (n : ℕ) (h : n = 0) :
    IsPPTOn encBits encBits (sampleFixed n) := by
  subst n
  fun_prop [sampleFixed]

@[program_certificate]
private theorem sampleFixed_ppt (n : ℕ) : IsPPTOn encBits encBits (sampleFixed n) := by
  fun_prop [sampleFixed]

attribute [irreducible] sampleFixed

-- An inapplicable registered side condition must not hide the next certificate.
example : IsPPTOn encBits encBits (sampleFixed 1) := by ppt

private def namedSample (_c _a : ℕ ↪ List Bool) (sample : List Bool → ProbComp ℕ) :
    List Bool → ProbComp ℕ := sample

private def namedNext (_c _b : ℕ ↪ List Bool) (next : List Bool → ℕ → ProbComp Bool) :
    List Bool → ℕ → ProbComp Bool := next

-- The side condition makes these exercise named-certificate lookup rather than fun_prop alone.
@[program_certificate]
private theorem namedSample_other (c a : ℕ ↪ List Bool) (sample : List Bool → ProbComp ℕ)
    (_t : True) (h : IsPPTOn encBits a sample) :
    IsPPTOn encBits a (namedSample c a sample) := h

@[program_certificate]
private theorem namedSample_shared (c a : ℕ ↪ List Bool) (sample : List Bool → ProbComp ℕ)
    (_t : True) (h : IsPPTOn encBits c sample) :
    IsPPTOn encBits c (namedSample c a sample) := h

@[program_certificate]
private theorem namedNext_other (c b : ℕ ↪ List Bool) (next : List Bool → ℕ → ProbComp Bool)
    (_t : True) (h : IsPPTOn (encPair encBits b) encBool (fun p => next p.1 p.2)) :
    IsPPTOn (encPair encBits b) encBool (fun p => namedNext c b next p.1 p.2) := h

@[program_certificate]
private theorem namedNext_shared (c b : ℕ ↪ List Bool) (next : List Bool → ℕ → ProbComp Bool)
    (_t : True) (h : IsPPTOn (encPair encBits c) encBool (fun p => next p.1 p.2)) :
    IsPPTOn (encPair encBits c) encBool (fun p => namedNext c b next p.1 p.2) := h

attribute [irreducible] namedSample namedNext

-- Neither routine's first registered certificate is compatible with the other routine.
example (c a b : ℕ ↪ List Bool) (sample : List Bool → ProbComp ℕ)
    (next : List Bool → ℕ → ProbComp Bool)
    (hsC : IsPPTOn encBits c sample) (_hsA : IsPPTOn encBits a sample)
    (hnC : IsPPTOn (encPair encBits c) encBool (fun p => next p.1 p.2))
    (_hnB : IsPPTOn (encPair encBits b) encBool (fun p => next p.1 p.2)) :
    IsPPTOn encBits encBool (fun word => do
      let n ← namedSample c a sample word
      namedNext c b next word n) := by
  ppt

-- Deterministic captured iteration composes with probabilistic code through the shared rules.
example {α β : Type} (input : α ↪ List Bool) (stateEncoding : β ↪ List Bool)
    (count : α → ℕ) (initial : α → β) (step : α → β → β)
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime (fun p : α × β => step p.1 p.2)
      (encPair input stateEncoding) stateEncoding)
    (growth : α → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state, (stateEncoding (step x state)).length ≤
      (stateEncoding state).length + growth x) :
    IsPPTOn input stateEncoding (fun x => pure ((step x)^[count x] (initial x))) := by
  ppt

-- Neither an unknown sampler nor a non-dyadic finite uniform law is a free operation.
example (_sample : List Bool → ProbComp Bool) : True := by
  fail_if_success have : IsPPTOn encBits encBool _sample := by ppt
  let encFin3 : Fin 3 ↪ List Bool := Fin.valEmbedding.trans encNat
  fail_if_success have : IsPPTOn encBits encFin3 (fun _ => ProbComp.uniform (Fin 3)) := by ppt
  trivial

end ComplexityTests.PPTTactic
