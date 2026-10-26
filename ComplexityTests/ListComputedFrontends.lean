/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Computed counting and unary lookup clients

The callback sees both the original input and the element. Lookup defaults are fixed,
and framed element encodings remain distinct from raw bit strings.
-/

open Turing.MultiTapeTM

example {α γ : Type} {encA : α ↪ List Bool} {input : γ ↪ List Bool}
    {values : γ → List α} {test : γ → α → Bool}
    (hl : ComputableInPolyTime values input (encList encA))
    (ht : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair input encA) encBool) :
    ComputableInPolyTime (fun x => (values x).countP (test x)) input encUnary := by
  fail_if_success (clear ht; fun_prop)
  fun_prop

example {α γ : Type} {encA : α ↪ List Bool} {input : γ ↪ List Bool}
    {values : γ → List α} {index : γ → ℕ} (fallback : α)
    (hl : ComputableInPolyTime values input (encList encA))
    (hi : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun x => (values x).getD (index x) fallback) input encA := by
  fail_if_success (clear hi; fun_prop)
  fun_prop

example {γ : Type} {input : γ ↪ List Bool}
    {word : γ → List Bool} {index : γ → ℕ} (fallback : Bool)
    (hw : ComputableInPolyTime word input encBits)
    (hi : ComputableInPolyTime index input encUnary) :
    ComputableInPolyTime (fun x => (word x).getD (index x) fallback) input encBool := by
  fail_if_success (clear hi; fun_prop)
  fun_prop
