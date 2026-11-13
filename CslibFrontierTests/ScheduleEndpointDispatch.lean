/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointDispatch

open Turing Turing.MultiTapeTM ScheduleEndpointDispatch

private def mixed : MultiTapePTM.Schedule 2 2 :=
  fun i h => if i = 0 ∧ h = some 0 then 1 else 0

private def raw : List Bool :=
  [false, false, false, true, false, false, false, false, false, false, false, false]

private theorem raw_mixed : RawScheduleEndpoint.word mixed = raw := by decide

-- The same finite native controller handles different runtime work heads. Head zero moves
-- right, so its left port is exhausted; the stationary second head's left port finds row one.
example (out : List Bool) : ∃ c, RunsBetween (machine 2)
    (initialConfig [] raw [] [true] out) c 157 1106 ∧ c.output = out ++ [true, false] := by
  refine ⟨finalConfig [] out mixed 0 0, ?_, ?_⟩
  · simpa [raw_mixed, ScheduleEndpointSelector.word, ScheduleEndpointSelector.decode,
      UnaryDispatch.code] using runsBetween [] out mixed 0 0
  · rw [finalConfig_output_query, raw_mixed]
    rfl

example (out : List Bool) : ∃ c, RunsBetween (machine 2)
    (initialConfig [] raw [] [true, true, true, true] out) c 157 1106 ∧
    c.output = out ++ [true, true, true] ∧
    c.workTapes 6 = tapeOfList [true, true, true, true] ∧ c.workTapePos 6 = 0 := by
  refine ⟨finalConfig [] out mixed 3 0, ?_, ?_, ?_, ?_⟩
  · simpa [raw_mixed, ScheduleEndpointSelector.word, ScheduleEndpointSelector.decode,
      UnaryDispatch.code] using runsBetween [] out mixed 3 0
  · rw [finalConfig_output_query, raw_mixed]
    rfl
  · simp only [finalConfig, show ScheduleEndpointSelector.decode 2 3 = some 3 by decide,
      embed_castAdd]
    exact Fin.append_right _ _ 0
  · simp only [finalConfig, show ScheduleEndpointSelector.decode 2 3 = some 3 by decide,
      embed_castAdd]
    exact Fin.append_right _ _ 0

-- The last family member is reached through its full six-symbol tag.
example (out : List Bool) : ∃ c, RunsBetween (machine 2)
    (initialConfig [] raw [] (List.replicate 6 true) out) c 157 1106 ∧
    c.output = out ++ [true, true, true] := by
  refine ⟨finalConfig [] out mixed 5 0, ?_, ?_⟩
  · simpa [raw_mixed, ScheduleEndpointSelector.word, ScheduleEndpointSelector.decode,
      UnaryDispatch.code] using runsBetween [] out mixed 5 0
  · rw [finalConfig_output_query, raw_mixed]
    rfl

-- The first invalid selector and a huge selector both preserve all seven input words.
example (out : List Bool) : RunsBetween (machine 2)
    (initialConfig [] raw [] [] out)
    (initialConfig [] raw [] [] (out ++ [false])) 157 1106 := by
  simpa [finalConfig, raw_mixed, ScheduleEndpointSelector.word, ScheduleEndpointSelector.decode,
    UnaryDispatch.code] using runsBetween [] out mixed 6 0

example (out : List Bool) : RunsBetween (machine 2)
    (initialConfig [] raw [] [] out)
    (initialConfig [] raw [] [] (out ++ [false])) 157 1106 := by
  have rejected (selector : ℕ) (hs : 6 ≤ selector) : RunsBetween (machine 2)
      (initialConfig [] raw [] [] out)
      (initialConfig [] raw [] [] (out ++ [false])) 157 1106 := by
    have hd := (ScheduleEndpointSelector.decode_eq_none_iff 2 selector).mpr hs
    have hw : ScheduleEndpointSelector.word 2 selector = [] := by
      rw [ScheduleEndpointSelector.word, hd]
      rfl
    have hz : Nat.bits 0 = [] := by decide
    simpa only [finalConfig, hd, raw_mixed, hw, hz, List.length_nil]
      using runsBetween [] out mixed selector 0
  exact rejected (2 ^ 128) (by norm_num)

-- A valid selector with a much larger invalid interval is rejected within its 11-bit clock.
example (out : List Bool) : ∃ c, RunsBetween (machine 2)
    (initialConfig [] raw (Nat.bits 1024) (List.replicate 4 true) out) c 212 1491 ∧
    c.output = out ++ [false] := by
  refine ⟨finalConfig [] out mixed 3 1024, ?_, ?_⟩
  · have hl : (Nat.bits 1024).length = 11 := by decide
    have hw : ScheduleEndpointSelector.word 2 3 = List.replicate 4 true := by decide
    simpa only [raw_mixed, hw, hl] using runsBetween [] out mixed 3 1024
  · rw [finalConfig_output_query, raw_mixed]
    have hq : ScheduleEndpointQuery.query 2 ⟨raw, 3, 1024⟩ = none := by decide
    rw [hq]
    rfl

-- With zero work heads even selector zero uses the rejecting continuation.
example (out : List Bool) : RunsBetween (machine 0)
    (initialConfig [] [false, false] [] [] out)
    (initialConfig [] [false, false] [] [] (out ++ [false])) 81 574 := by
  let σ : MultiTapePTM.Schedule 0 1 := fun _ _ => 0
  have hw : RawScheduleEndpoint.word σ = [false, false] := by decide
  simpa [finalConfig, hw, ScheduleEndpointSelector.word, ScheduleEndpointSelector.decode,
    UnaryDispatch.code] using runsBetween [] out σ 0 0

-- The reusable rejection machine also preserves arbitrary nonzero heads and ambient words.
example : RunsBetween (reject 2)
    (tapesCfg [true] ![[true, false], [false, true]] ![-2, 3] ![4, -1] [true])
    (tapesCfg [true] ![[true, false], [false, true]] ![-2, 3] ![4, -1] [true, false]) 1 4 :=
  runsBetween_reject _

-- Neither horizon nor either runtime index occurs before the existential machine choice.
example : ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM 7 Bool S),
    ∀ (q : ℕ) (σ : MultiTapePTM.Schedule 2 q) (selector interval : ℕ),
      ∃ c, RunsBetween tm
        (initialConfig [] (RawScheduleEndpoint.word σ) interval.bits
          (ScheduleEndpointSelector.word 2 selector) []) c
        (48 * q + 5 * interval.bits.length + 61)
        (7 * (48 * q + 5 * interval.bits.length + 62)) ∧
        c.output = ScheduleEndpointAnswer.encAnswer (ScheduleEndpointQuery.query 2
          ⟨RawScheduleEndpoint.word σ, selector, interval⟩) := by
  refine ⟨_, inferInstance, machine 2, fun q σ selector interval =>
    ⟨finalConfig [] [] σ selector interval, ?_, ?_⟩⟩
  · simpa only [show 8 * 2 + 32 = 48 from rfl, show 6 * 2 = 12 from rfl, Nat.add_assoc]
      using runsBetween [] [] σ selector interval
  · exact finalConfig_output_query [] [] σ selector interval
