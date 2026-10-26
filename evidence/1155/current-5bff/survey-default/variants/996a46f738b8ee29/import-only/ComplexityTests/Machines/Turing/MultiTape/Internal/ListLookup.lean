/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup


import Diag1155.Measure
/-! # Generic unary lookup and first-occurrence clients -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α : Type} {encA : α ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [SizedListEncoding encA encL] (fallback : α) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.getD p.2 fallback)
      (encPair encL encUnary) encA := ComputableInPolyTime.listGetD fallback

example {α γ : Type} {encA : α ↪ List Bool} {input : γ ↪ List Bool}
    {values : γ → List α} {index : γ → ℕ} (fallback : α)
    (hv : ComputableInPolyTime values input (encList encA))
    (hi : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun x => (values x).getD (index x) fallback) input encA := by
  fail_if_success (clear hi; fun_prop)
  exact (ComputableInPolyTime.listGetD fallback).comp (hv.prod hi)

example {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by fun_prop

example {α γ : Type} [DecidableEq α] {encA : α ↪ List Bool} {input : γ ↪ List Bool}
    {values : γ → List α} {value : γ → α}
    (hl : ComputableInPolyTime values input (encList encA))
    (hv : ComputableInPolyTime value input encA) :
    ComputableInPolyTime (fun x => (values x).idxOf (value x)) input encUnary :=
  (ComputableInPolyTime.idxOf encA).comp (hl.prod hv)

example : ([3, 4, 3] : List ℕ).idxOf 3 = 0 := by decide
example : ([3, 4, 3] : List ℕ).idxOf 7 = 3 := by decide
example : ([] : List ℕ).idxOf 7 = 0 := by decide
example : ([] : List ℕ).getD 100 7 = 7 := by decide
example : ([3, 4] : List ℕ).getD 100 7 = 7 := by decide
example : ([3, 4] : List ℕ).getD 1 7 = 4 := by decide

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.listGetD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.listGetD
/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.idxOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.idxOf

-- Optional lookup retains the complete arbitrary codec and captured-input telescope.
example {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool} {list : γ → List α} {index : γ → ℕ}
    (hl : ComputableInPolyTime list encIn encL)
    (hi : ComputableInPolyTime index encIn encUnary)
    [ListEncoding encA encL] [SizedListEncoding encA encL] :
    ComputableInPolyTime (fun x => (list x)[index x]?) encIn (encOption encA) := by
  fail_if_success (clear hl; fun_prop)
  fail_if_success (clear hi; fun_prop)
  fun_prop

-- No element inhabitant is required, including for an unbounded runtime index.
example (enc : Empty ↪ List Bool) :
    ComputableInPolyTime (fun n : ℕ => ([] : List Empty)[n]?) encUnary (encOption enc) := by
  exact ComputableInPolyTime.getElem? (encL := encList enc)
    (ComputableInPolyTime.const []) ComputableInPolyTime.id'

example : ([] : List Bool)[100]? = none := by decide
example : ([true, false] : List Bool)[100]? = none := by decide
example : ([true, false] : List Bool)[1]? = some false := by decide

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.getElem?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.getElem?
