/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines

/-! # Shared codec word machines

The original head and emptiness transducers, moved unchanged from Encodings.Basic.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-! ### Transducers for the word operations -/

namespace Encodings

open Internal.FrameMachines

/-- Emits a word determined by its input's first symbol, if any, and by `drop`: `[true]` followed by
the input (`drop = none`), the input without its first symbol (`drop = some false`), or just the
first symbol (`drop = some true`). -/
@[simps -isSimp q₀ step final]
def headT (drop : Option Bool) : Transducer Bool Bool where
  q₀ := false
  step
    | false, b => (true, match drop with | none => [true, b] | some false => [] | some true => [b])
    | true, b => (true, match drop with | none => [b] | some false => [b] | some true => [])
  final
    | false => match drop with | none => [true] | _ => []
    | true => []
  length_step_le q b := by cases q <;> rcases drop with _ | _ | _ <;> simp
  length_final_le q := by cases q <;> rcases drop with _ | _ | _ <;> simp

lemma headT_run_true (drop : Option Bool) (v : List Bool) :
    (headT drop).run true v = if drop = some true then [] else v := by
  induction v <;> rcases drop with _ | _ | _ <;> simp_all [headT_step, headT_final]

-- vendored: the run equations `headT_none_run`, `headT_some_false_run` and
-- `headT_some_true_run` below are local additions, not in crei:crei/tidy-universal
/-- `headT none` prepends `true`. -/
lemma headT_none_run (v : List Bool) : (headT none).run (headT none).q₀ v = true :: v := by
  cases v <;> simp [headT_run_true, headT_q₀, headT_step, headT_final]

/-- `headT (some false)` drops the first symbol. -/
lemma headT_some_false_run (v : List Bool) :
    (headT (some false)).run (headT (some false)).q₀ v = v.tail := by
  cases v <;> simp [headT_run_true, headT_q₀, headT_step, headT_final]

/-- `headT (some true)` keeps just the first symbol. -/
lemma headT_some_true_run (v : List Bool) :
    (headT (some true)).run (headT (some true)).q₀ v = v.take 1 := by
  cases v <;> simp [headT_run_true, headT_q₀, headT_step, headT_final]

/-- Emits `[true]` on the empty word and `[false]` on every other word. -/
@[simps -isSimp q₀ step final]
def isEmptyT : Transducer Bool Bool where
  q₀ := false
  step q _ := (true, if q then [] else [false])
  final q := if q then [] else [true]
  length_step_le q _ := by cases q <;> simp
  length_final_le q := by cases q <;> simp

lemma isEmptyT_run_true (v : List Bool) : isEmptyT.run true v = [] := by
  induction v <;> simp [isEmptyT_step, isEmptyT_final, *]

-- vendored: `isEmptyT_run` below is a local addition, not in crei:crei/tidy-universal
/-- `isEmptyT` emits the emptiness test of its input. -/
lemma isEmptyT_run (v : List Bool) : isEmptyT.run isEmptyT.q₀ v = [v.isEmpty] := by
  cases v <;> simp [isEmptyT_run_true, isEmptyT_q₀, isEmptyT_step, isEmptyT_final]

end Encodings

end Turing.MultiTapeTM
