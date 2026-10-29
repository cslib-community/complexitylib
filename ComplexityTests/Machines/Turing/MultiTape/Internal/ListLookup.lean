/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-! # Generic unary lookup and first-occurrence clients -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α γ : Type} [DecidableEq α] {encA : α ↪ List Bool} {encL : List α ↪ List Bool}
    [ListEncoding encA encL] [SizedListEncoding encA encL]
    {input : γ ↪ List Bool} {values list : γ → List α} {index : γ → ℕ} {value : γ → α}
    (fallback : α)
    (hvals : ComputableInPolyTime values input (encList encA))
    (hlist : ComputableInPolyTime list input encL)
    (hi : ComputableInPolyTime index input encUnary)
    (hv : ComputableInPolyTime value input encA)
    (encEmpty : Empty ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.getD p.2 fallback)
      (encPair encL encUnary) encA ∧
    ComputableInPolyTime (fun x => (values x).getD (index x) fallback) input encA ∧
    ComputableInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList encA) encA) encUnary ∧
    ComputableInPolyTime (fun x => (values x).idxOf (value x)) input encUnary ∧
    ([3, 4, 3] : List ℕ).idxOf 3 = 0 ∧
    ([3, 4, 3] : List ℕ).idxOf 7 = 3 ∧
    ([] : List ℕ).idxOf 7 = 0 ∧
    ([] : List ℕ).getD 100 7 = 7 ∧
    ([3, 4] : List ℕ).getD 100 7 = 7 ∧
    ([3, 4] : List ℕ).getD 1 7 = 4 ∧
    ComputableInPolyTime (fun x => (list x)[index x]?) input (encOption encA) ∧
    ComputableInPolyTime (fun n : ℕ => ([] : List Empty)[n]?) encUnary (encOption encEmpty) ∧
    ([] : List Bool)[100]? = none ∧
    ([true, false] : List Bool)[100]? = none ∧
    ([true, false] : List Bool)[1]? = some false := by
  refine ⟨ComputableInPolyTime.listGetD fallback, ?_, by fun_prop,
    (ComputableInPolyTime.idxOf encA).comp (hvals.prod hv),
    by decide, by decide, by decide, by decide, by decide, by decide,
    ?_,
    ComputableInPolyTime.getElem? (encL := encList encEmpty)
      (ComputableInPolyTime.const []) ComputableInPolyTime.id',
    by decide, by decide, by decide⟩
  · fail_if_success (clear hi; fun_prop)
    exact (ComputableInPolyTime.listGetD fallback).comp (hvals.prod hi)
  · clear hvals
    fail_if_success (clear hlist; fun_prop)
    fail_if_success (clear hi; fun_prop)
    fun_prop
