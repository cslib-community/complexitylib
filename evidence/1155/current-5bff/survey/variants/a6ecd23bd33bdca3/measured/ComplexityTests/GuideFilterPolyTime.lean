/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Tactic.PolyTime


import Diag1155.Measure
/-! # The guide's captured binary-comparison filter, at its original budget

This goal failed by exhaustive search before the ordinary binary non-strict comparison rule.
The captured callback needs both computed operands in the same full input encoding.
-/

diag1155_install
open Turing.MultiTapeTM

-- Exact original guide goal and tactic; no pre-supplied view or named proof.
set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.filter (· ≤ p.2))
    (encPair (encList encNat) encNat) (encList encNat) := by
  polytime

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : ComputableInPolyTime (fun p : (List ℕ × ℕ) × ℕ => decide (p.2 ≤ p.1.2))
    (encPair (encPair (encList encNat) encNat) encNat) encBool := by
  polytime

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool := by fun_prop

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool := by polytime

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool := by polytime

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool := by
  polytime

-- Neither callback premise may be manufactured by global raw search.
set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example {α : Type} {input : α ↪ List Bool} {left _right : α → ℕ}
    (_hl : ComputableInPolyTime left input encNat) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => decide (left a ≤ _right a)) input encBool := by
      polytime
  trivial

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example {α : Type} {input : α ↪ List Bool} {_left right : α → ℕ}
    (_hr : ComputableInPolyTime right input encNat) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => decide (_left a ≤ right a)) input encBool := by
      polytime
  trivial

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example : decide ((0 : ℕ) ≤ 0) = true ∧ decide ((2 : ℕ) ≤ 1) = false := by decide
