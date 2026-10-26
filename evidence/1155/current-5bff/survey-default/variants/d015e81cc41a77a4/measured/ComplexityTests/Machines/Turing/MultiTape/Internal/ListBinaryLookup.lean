/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup


import Diag1155.Measure
/-! # Generic, framed and raw-bit lookup at a binary index -/


diag1155_install
open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

-- The complete telescope: arbitrary element and input encodings, any sized list encoding,
-- a fixed default, a computed list and a computed binary index.
example {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {l : γ → List α} {i : γ → ℕ} (d : α)
    (hl : ComputableInPolyTime l encIn encL) (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun x => (l x).getD (i x) d) encIn encA := by
  -- Neither the unary lookup rule nor automation accepts a binary index certificate.
  fail_if_success exact (ComputableInPolyTime.listGetD d).comp (hl.prod hi)
  fail_if_success fun_prop
  exact ComputableInPolyTime.listGetD_binary d hl hi

-- A unary index certificate does not match the binary premise.
example {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {l : γ → List α} {i : γ → ℕ} (d : α)
    (hl : ComputableInPolyTime l encIn encL) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => (l x).getD (i x) d) encIn encA := by
  fail_if_success exact ComputableInPolyTime.listGetD_binary d hl hi
  exact (ComputableInPolyTime.listGetD d).comp (hl.prod hi)

-- Without the size premise on the list encoding the rule does not apply.
example {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool} [ListEncoding encA encL]
    {l : γ → List α} {i : γ → ℕ} (_d : α)
    (_hl : ComputableInPolyTime l encIn encL) (_hi : ComputableInPolyTime i encIn encNat) :
    True := by
  fail_if_success
    have := ComputableInPolyTime.listGetD_binary (encA := encA) (encL := encL) _d _hl _hi
  trivial

-- Raw bit strings: read a bit at a binary position.
example : ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
    (encPair encBits encNat) encBool :=
  ComputableInPolyTime.listGetD_binary (encA := encBool) false
    (ComputableInPolyTime.fst encBits encNat) (ComputableInPolyTime.snd encBits encNat)

-- Framed lists of binary naturals.
example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.getD p.2 0)
    (encPair (encList encNat) encNat) encNat :=
  ComputableInPolyTime.listGetD_binary 0
    (ComputableInPolyTime.fst (encList encNat) encNat) (ComputableInPolyTime.snd _ encNat)

-- A binary index computed from the input: follow the pointer stored in the first entry.
example : ComputableInPolyTime (fun l : List ℕ => l.getD (l.getD 0 0) 0) (encList encNat) encNat :=
  ComputableInPolyTime.listGetD_binary 0 ComputableInPolyTime.id'
    ((ComputableInPolyTime.listGetD 0).comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 0)))

-- Beyond the list every lookup returns the default, however large the binary index.
example : ([true, false] : List Bool).getD 1 true = false := by decide
example : ([true, false] : List Bool).getD (2 ^ 64) true = true := by decide
example : ([] : List ℕ).getD (2 ^ 64) 7 = 7 := by decide
