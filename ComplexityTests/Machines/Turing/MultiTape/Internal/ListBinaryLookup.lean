/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-! # Generic, framed and raw-bit lookup at a binary index -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

-- The complete telescope: arbitrary element and input encodings, any sized list encoding,
-- a fixed default, a computed list and a computed binary or unary index, plus missing-instance
-- failure checks.
example {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL encLUnsized : List α ↪ List Bool}
    [ListEncoding encA encL] [SizedListEncoding encA encL] [ListEncoding encA encLUnsized]
    {l lUnsized : γ → List α} {iBin iUn : γ → ℕ} (d : α)
    (hl : ComputableInPolyTime l encIn encL)
    (_hlUnsized : ComputableInPolyTime lUnsized encIn encLUnsized)
    (hiBin : ComputableInPolyTime iBin encIn encNat)
    (hiUn : ComputableInPolyTime iUn encIn encUnary) :
    ComputableInPolyTime (fun x => (l x).getD (iBin x) d) encIn encA ∧
    ComputableInPolyTime (fun x => (l x).getD (iUn x) d) encIn encA := by
  fail_if_success
    have := ComputableInPolyTime.listGetD_binary
      (encA := encA) (encL := encLUnsized) d _hlUnsized hiBin
  refine ⟨?_, ?_⟩
  · fail_if_success exact (ComputableInPolyTime.listGetD d).comp (hl.prod hiBin)
    fail_if_success fun_prop
    exact ComputableInPolyTime.listGetD_binary d hl hiBin
  · fail_if_success exact ComputableInPolyTime.listGetD_binary d hl hiUn
    exact (ComputableInPolyTime.listGetD d).comp (hl.prod hiUn)

-- Raw bit strings, framed lists of binary naturals, indirect pointer lookup, and out-of-bounds
-- binary indices.
example :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
      (encPair encBits encNat) encBool ∧
    ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.getD p.2 0)
      (encPair (encList encNat) encNat) encNat ∧
    ComputableInPolyTime (fun l : List ℕ => l.getD (l.getD 0 0) 0) (encList encNat) encNat ∧
    ([true, false] : List Bool).getD 1 true = false ∧
    ([true, false] : List Bool).getD (2 ^ 64) true = true ∧
    ([] : List ℕ).getD (2 ^ 64) 7 = 7 :=
  ⟨ComputableInPolyTime.listGetD_binary (encA := encBool) false
      (ComputableInPolyTime.fst encBits encNat) (ComputableInPolyTime.snd encBits encNat),
    ComputableInPolyTime.listGetD_binary 0
      (ComputableInPolyTime.fst (encList encNat) encNat) (ComputableInPolyTime.snd _ encNat),
    ComputableInPolyTime.listGetD_binary 0 ComputableInPolyTime.id'
      ((ComputableInPolyTime.listGetD 0).comp
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 0))),
    by decide, by decide, by decide⟩
