/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-! # Streaming machines for total decoder leaves

Both transducers are total on malformed as well as encoded words. They use no work tapes and
the standard transducer clock includes every input symbol.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.DecoderWords

/-- Replace each input symbol by one unary symbol. -/
def unaryLengthT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [true])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The emitted unary word records the length of every input word. -/
theorem unaryLengthT_run (w : List Bool) :
    unaryLengthT.run () w = List.replicate w.length true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [true] ++ unaryLengthT.run () w = List.replicate (w.length + 1) true
    rw [ih, List.replicate_succ]
    rfl

/-- Read the first symbol, returning the fixed default on empty input. -/
def headDefaultT (default : Bool) : Transducer Bool Bool where
  q₀ := false
  step seen b := (true, if seen then [] else [b])
  final seen := if seen then [] else [default]
  length_step_le seen _ := by cases seen <;> simp
  length_final_le seen := by cases seen <;> simp

/-- After seeing the first symbol, this transducer emits nothing further. -/
theorem headDefaultT_run_true (default : Bool) (w : List Bool) :
    (headDefaultT default).run true w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change [] ++ (headDefaultT default).run true w = []
    simpa using ih

/-- The default applies exactly to empty input, with no resampling or partiality. -/
theorem headDefaultT_run (default : Bool) (w : List Bool) :
    (headDefaultT default).run false w = [w.headD default] := by
  cases w with
  | nil => rfl
  | cons b w =>
    change [b] ++ (headDefaultT default).run true w = [b]
    rw [headDefaultT_run_true, List.append_nil]

end Turing.MultiTapeTM.Internal.DecoderWords

namespace Turing.MultiTapeTM

/-- Drops the `false`s at the start of a word. -/
def dropFalsesT : Transducer Bool Bool where
  q₀ := false
  step
    | false, false => (false, [])
    | _, b => (true, [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

theorem dropFalsesT_run_true (w : List Bool) : dropFalsesT.run true w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => exact congrArg (b :: ·) ih

theorem dropFalsesT_run (w : List Bool) : dropFalsesT.run false w = w.dropWhile (!·) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · exact ih
    · exact congrArg (true :: ·) (dropFalsesT_run_true w)

end Turing.MultiTapeTM
