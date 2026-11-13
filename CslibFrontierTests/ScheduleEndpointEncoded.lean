/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointComplexity
import Mathlib.Tactic.FinCases

open Turing Turing.MultiTapeTM ScheduleEndpointQuery ScheduleEndpointInput ScheduleEndpointAnswer

private def raw : List Bool :=
  [false, false, false, true, false, false, false, false, false, false, false, false]

private structure Case where
  /-- Runtime record supplied through the complete external encoding. -/
  request : Input
  /-- Expected output, including validity and found tags. -/
  answer : List Bool
  /-- Complete external encoding length plus one. -/
  clockFactor : ℕ

-- Different heads, the final port, exhaustion, invalid pairs and incomplete rows, rejected
-- selectors, a much larger interval, and the empty schedule all use the same native machine.
private def cases : Fin 10 → Case := ![
  ⟨⟨raw, 0, 0⟩, [true, false], 27⟩,
  ⟨⟨raw, 3, 0⟩, [true, true, true], 31⟩,
  ⟨⟨raw, 5, 0⟩, [true, true, true], 33⟩,
  ⟨⟨raw, 3, 1⟩, [true, false], 32⟩,
  ⟨⟨[true, true, false, false, false, false], 3, 0⟩, [false], 19⟩,
  ⟨⟨[false], 3, 0⟩, [false], 9⟩,
  ⟨⟨raw, 6, 0⟩, [false], 33⟩,
  ⟨⟨raw, 1024, 0⟩, [false], 49⟩,
  ⟨⟨raw, 3, 1024⟩, [false], 42⟩,
  ⟨⟨[], 3, 0⟩, [false], 7⟩]

private theorem cases_spec (i : Fin 10) :
    (encInput (cases i).request).length + 1 = (cases i).clockFactor ∧
      encAnswer (query 2 (cases i).request) = (cases i).answer := by
  fin_cases i <;> decide

-- This starts from blank tapes on the external record, so field extraction, validation,
-- selector preparation, dispatch, bounded positioning, scanning and output are all charged.
example : ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q) (c : ℕ),
    ∀ (i : Fin 10) (out : List Bool), ∃ final,
      RunsBetween tm (tapesCfg (encInput (cases i).request) (fun _ => []) 0 0 out)
        final (c * (cases i).clockFactor) (K * (c * (cases i).clockFactor + 1)) ∧
      final.output = out ++ (cases i).answer := by
  obtain ⟨K, Q, hQ, tm, c, htm⟩ := ScheduleEndpointEncoded.exists_machine 2
  refine ⟨K, Q, hQ, tm, c, ?_⟩
  intro i out
  obtain ⟨final, hr, hout⟩ := htm (cases i).request out
  obtain ⟨hsize, hanswer⟩ := cases_spec i
  rw [hsize] at hr
  exact ⟨final, hr, by simpa only [hanswer] using hout⟩

-- A zero-head machine rejects a valid raw row at selector zero, preserving old output.
example : ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q) (c : ℕ),
    ∀ out, ∃ final,
      RunsBetween tm (tapesCfg (encInput ⟨[false, false], 0, 0⟩) (fun _ => []) 0 0 out)
        final (c * 7) (K * (c * 7 + 1)) ∧ final.output = out ++ [false] := by
  obtain ⟨K, Q, hQ, tm, c, htm⟩ := ScheduleEndpointEncoded.exists_machine 0
  refine ⟨K, Q, hQ, tm, c, ?_⟩
  intro out
  obtain ⟨final, hr, hout⟩ := htm ⟨[false, false], 0, 0⟩ out
  have hsize : (encInput ⟨[false, false], 0, 0⟩).length + 1 = 7 := by decide
  have hanswer : encAnswer (query 0 ⟨[false, false], 0, 0⟩) = [false] := by decide
  rw [hsize] at hr
  exact ⟨final, hr, by simpa only [hanswer] using hout⟩

-- The native theorem also yields ordinary independent resource bounds and the composable
-- linear certificate, using the named input framing and validity/found-tag answer encoding.
example : ∃ cTime cSpace, ComputableInTimeAndSpaceOfLength (query 2) encInput encAnswer
    (fun n => cTime * (n + 1)) (fun n => cSpace * (n + 1)) :=
  ScheduleEndpointEncoded.computableInTimeAndSpace_linear 2

example : ComputableInO (query 2) encInput encAnswer
    (fun a => (encInput a).length) (fun a => (encInput a).length) := by fun_prop
