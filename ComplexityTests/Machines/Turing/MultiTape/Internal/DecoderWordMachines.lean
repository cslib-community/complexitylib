/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines
import Lean.Elab.Command

/-! Total decoder leaf machines, including malformed words and fixed default behavior. -/
open Turing.MultiTapeTM Internal.DecoderWords
example (w : List Bool) : unaryLengthT.toTM.ComputesInTimeAndSpace w
    (List.replicate w.length true) (2 * w.length + 3) 0 := by
  simpa only [show unaryLengthT.q₀ = () from rfl, unaryLengthT_run] using
    unaryLengthT.computesInTimeAndSpace_toTM w
example (w : List Bool) (d : Bool) : (headDefaultT d).toTM.ComputesInTimeAndSpace w
    [w.headD d] (2 * w.length + 3) 0 := by
  simpa only [show (headDefaultT d).q₀ = false from rfl, headDefaultT_run] using
    (headDefaultT d).computesInTimeAndSpace_toTM w
example : (headDefaultT false).run false [] = [false] := rfl
example : (headDefaultT true).run false [] = [true] := rfl
example (w : List Bool) : (headDefaultT false).run false (true :: w) = [true] := by
  simpa using headDefaultT_run false (true :: w)
example (n : ℕ) : unaryLengthT.run () (List.replicate n false) = List.replicate n true := by
  simp [unaryLengthT_run]

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
