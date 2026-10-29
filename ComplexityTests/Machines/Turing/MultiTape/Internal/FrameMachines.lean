/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
import Lean.Elab.Command

/-! Shared frame-machine laws on encoded, empty and incomplete words. -/
open Turing.MultiTapeTM Internal.FrameMachines

example (w u v : List Bool) :
    (readFrameT true).toTM.ComputesInTimeAndSpace w (unframe w) (2 * w.length + 3) 0 ∧
    (readFrameT false).toTM.ComputesInTimeAndSpace w (dropFrame w) (2 * w.length + 3) 0 ∧
    (readFrameT true).run .marker (frame u ++ v) = u ∧
    (readFrameT false).run .marker (frame u ++ v) = v ∧
    (readFrameT true).run .marker [] = [] ∧
    (readFrameT true).run .marker [true] = [] ∧
    (readFrameT false).run .marker [true] = [] ∧
    (readFrameT true).run .marker [true, false, true] = [false] ∧
    (readFrameT false).run .marker [false, true] = [true] ∧
    Encodings.frameT.toTM.ComputesInTimeAndSpace w (frame w) (2 * w.length + 3) 0 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [show (readFrameT true).q₀ = .marker from rfl, readFrameT_run_true] using
      (readFrameT true).computesInTimeAndSpace_toTM w
  · simpa only [show (readFrameT false).q₀ = .marker from rfl, readFrameT_run_false] using
      (readFrameT false).computesInTimeAndSpace_toTM w
  · rw [readFrameT_run_true, unframe_frame_append]
  · rw [readFrameT_run_false, dropFrame_frame_append]
  · simpa only [show Encodings.frameT.q₀ = () from rfl, Encodings.frameT_run] using
      Encodings.frameT.computesInTimeAndSpace_toTM w

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
