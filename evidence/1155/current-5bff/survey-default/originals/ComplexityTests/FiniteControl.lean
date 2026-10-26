/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Probabilistic.Finite
import Complexity.Tactic.PPT

/-! Finite dispatch retains captured data and charges every table entry and selected result. -/

namespace ComplexityTests.FiniteControl

open Turing.MultiTapeTM Cslib Cslib.Probability

-- Stored table/index pairs use ordinary function application.
example : ComputableTidilyInPolyTime
    (fun pair : (Bool → List Bool) × Bool => pair.1 pair.2)
    (encPair (encPi encBits) encBool) encBits := by fun_prop

-- Computed tables and indices use the general application rule without a default value.
example {α Index Value : Type} [Fintype Index] {input : α ↪ List Bool}
    {enc : Value ↪ List Bool} {indexEnc : Index ↪ List Bool}
    (values : α → Index → Value) (index : α → Index)
    (hv : ComputableTidilyInPolyTime values input (encPi enc))
    (hi : ComputableTidilyInPolyTime index input indexEnc) :
    ComputableTidilyInPolyTime (fun a => values a (index a)) input enc := by
  fail_if_success (clear hv; polytime)
  fail_if_success (clear hi; polytime)
  polytime

-- Naming either computed component retains the same inference, including arbitrary encodings.
example {α Index Value : Type} [Fintype Index] {input : α ↪ List Bool}
    {enc : Value ↪ List Bool} {indexEnc : Index ↪ List Bool}
    (values : α → Index → Value) (index : α → Index)
    (hv : ComputableTidilyInPolyTime values input (encPi enc))
    (hi : ComputableTidilyInPolyTime index input indexEnc) :
    ComputableTidilyInPolyTime
      (fun a => let table := values a; let i := index a; table i) input enc := by polytime

-- The same application rule is available inside a deterministic return in a PPT program.
example {α Index Value : Type} [Fintype Index] {input : α ↪ List Bool}
    {enc : Value ↪ List Bool} {indexEnc : Index ↪ List Bool}
    (values : α → Index → Value) (index : α → Index)
    (hv : ComputableTidilyInPolyTime values input (encPi enc))
    (hi : ComputableTidilyInPolyTime index input indexEnc) :
    IsPPTOn input enc (fun a => pure (values a (index a))) := by ppt

-- A different encoding of the same index type uses the same lookup rule.
example : ComputableTidilyInPolyTime
    (fun pair : (Bool → List Bool) × Bool => pair.1 pair.2)
    (encPair (encPi encBits) (encFinEnum Bool)) encBits := by polytime

/-- info: [true, true] -/
#guard_msgs in
#eval encFinEnum (Fin 3) 2

/-- info: [true] -/
#guard_msgs in
#eval encFinEnum (Option Bool) (some true)

-- Computed update and lookup preserve unbounded words in all unselected entries.
example : ComputableTidilyInPolyTime
    (fun pair : (Bool → List Bool) × Bool =>
      Function.update pair.1 pair.2 (pair.1 pair.2).reverse)
    (encPair (encPi encBits) encBool) (encPi encBits) := by fun_prop

-- Naming the shared tuple gives the same program certificate.
example : ComputableTidilyInPolyTime
    (fun pair : (Bool → List Bool) × Bool =>
      let data := pair
      Function.update data.1 data.2 (data.1 data.2).reverse)
    (encPair (encPi encBits) encBool) (encPi encBits) := by polytime

-- Update and reversal expose their inner computed lookup to the same application rule.
example : ComputableTidilyInPolyTime
    (fun pair : (Bool → List Bool) × Bool =>
      let data := (pair.1, !pair.2)
      Function.update data.1 data.2 (data.1 data.2).reverse)
    (encPair (encPi encBits) encBool) (encPi encBits) := by
  polytime

-- The same nested update works with arbitrary framed element and index encodings.
example {α Index Value : Type} [Fintype Index] [DecidableEq Index]
    (input : α ↪ List Bool) (element : Value ↪ List Bool) (indexEnc : Index ↪ List Bool)
    (values : α → Index → List Value) (index : α → Index)
    (_replacement : α → List Value)
    (hv : ComputableTidilyInPolyTime values input (encPi (encList element)))
    (hi : ComputableTidilyInPolyTime index input indexEnc) :
    ComputableTidilyInPolyTime (fun a =>
      Function.update (values a) (index a) ((values a) (index a)).reverse)
      input (encPi (encList element)) := by
  fail_if_success (clear hv; polytime)
  fail_if_success (clear hi; polytime)
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun a => Function.update (values a) (index a) (_replacement a))
        input (encPi (encList element)) := by polytime
  polytime

-- Finite dispatch retains the original unbounded input in every branch.
example {α β Tag : Type} [Finite Tag] (input : α ↪ List Bool) (output : β ↪ List Bool)
    (tagEncoding : Tag ↪ List Bool) (tag : α → Tag) (branch : Tag → α → β)
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableTidilyInPolyTime (branch choice) input output) :
    ComputableTidilyInPolyTime (fun a => branch (tag a) a) input output :=
  htag.finite_cases hbranch

-- Probabilistic branches may return both output and private state.
example {α β State Tag : Type} [Finite Tag] (input : α ↪ List Bool)
    (output : β ↪ List Bool) (stateEncoding : State ↪ List Bool)
    (tagEncoding : Tag ↪ List Bool) (tag : α → Tag)
    (branch : Tag → α → ProbComp (β × State))
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, IsPPTOn input (encPair output stateEncoding) (branch choice)) :
    IsPPTOn input (encPair output stateEncoding) (fun a => branch (tag a) a) :=
  IsPPTOn.finite_cases htag hbranch

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

-- Empty finite control requires no fallback program or inhabited result type.
example : ComputableTidilyInPolyTime
    (fun a : Empty => (a.elim : Empty → Empty) a) encEmpty encEmpty :=
  ComputableTidilyInPolyTime.finite_cases
    (ComputableTidilyInPolyTime.id' (encIn := encEmpty)) (fun tag => tag.elim)

example : IsPPTOn encEmpty encEmpty
    (fun a : Empty => (a.elim : Empty → ProbComp Empty) a) :=
  IsPPTOn.finite_cases (ComputableTidilyInPolyTime.id' (encIn := encEmpty)) (fun tag => tag.elim)

-- A concrete branch selector combines finite control, unbounded state and independent sampling.
private noncomputable def choose (tag : Bool) (word : List Bool) :
    ProbComp (List Bool × List Bool) :=
  if tag then do
    let bit ← ProbComp.uniform Bool
    return (bit :: word, word)
  else pure (word.reverse, word)

example : IsPPTOn encBits (encPair encBits encBits) (fun word => choose word.isEmpty word) := by
  apply IsPPTOn.finite_cases (tagEncoding := encBool)
  · fun_prop
  · intro tag
    unfold choose
    ppt

end ComplexityTests.FiniteControl
