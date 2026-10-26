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

example (w : List Bool) : (readFrameT true).toTM.ComputesInTimeAndSpace w (unframe w)
    (2 * w.length + 3) 0 := by
  simpa only [show (readFrameT true).q₀ = .marker from rfl, readFrameT_run_true] using
    (readFrameT true).computesInTimeAndSpace_toTM w

example (w : List Bool) : (readFrameT false).toTM.ComputesInTimeAndSpace w (dropFrame w)
    (2 * w.length + 3) 0 := by
  simpa only [show (readFrameT false).q₀ = .marker from rfl, readFrameT_run_false] using
    (readFrameT false).computesInTimeAndSpace_toTM w

example (u v : List Bool) : (readFrameT true).run .marker (frame u ++ v) = u := by
  rw [readFrameT_run_true, unframe_frame_append]
example (u v : List Bool) : (readFrameT false).run .marker (frame u ++ v) = v := by
  rw [readFrameT_run_false, dropFrame_frame_append]
example : (readFrameT true).run .marker [] = [] := rfl
example : (readFrameT true).run .marker [true] = [] := rfl
example : (readFrameT false).run .marker [true] = [] := rfl
example : (readFrameT true).run .marker [true, false, true] = [false] := rfl
example : (readFrameT false).run .marker [false, true] = [true] := rfl

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

example (w : List Bool) : Encodings.frameT.toTM.ComputesInTimeAndSpace w (frame w)
    (2 * w.length + 3) 0 := by
  simpa only [show Encodings.frameT.q₀ = () from rfl, Encodings.frameT_run] using
    Encodings.frameT.computesInTimeAndSpace_toTM w
