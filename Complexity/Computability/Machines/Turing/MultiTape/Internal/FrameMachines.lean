/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer

/-! # Shared machines for reading framed words

These original finite-state machines and run laws preserve all-word behavior, including empty
and incomplete frames. Their source is moved unchanged from Encodings.Basic.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.FrameMachines

/-- The states of a transducer reading a framed word: expecting a marker, expecting a symbol, or
past the frame. -/
inductive FrameState
  | marker
  | bit
  | done

instance : Finite FrameState :=
  Finite.of_surjective (fun b : Option Bool => b.elim .done fun b => if b then .marker else .bit)
    fun q => by cases q; exacts [⟨some true, rfl⟩, ⟨some false, rfl⟩, ⟨none, rfl⟩]

/-- Emits the word framed at the start of its input (`keep = true`), or what follows the frame
(`keep = false`). -/
@[simps q₀ step final]
def readFrameT (keep : Bool) : Transducer Bool FrameState where
  q₀ := .marker
  step
    | .marker, true => (.bit, [])
    | .marker, false => (.done, [])
    | .bit, b => (.marker, if keep then [b] else [])
    | .done, b => (.done, if keep then [] else [b])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> cases keep <;> simp
  length_final_le _ := by simp

lemma readFrameT_run_done (keep : Bool) (v : List Bool) :
    (readFrameT keep).run .done v = if keep then [] else v := by
  induction v <;> cases keep <;> simp_all

lemma readFrameT_run_true : ∀ v, (readFrameT true).run .marker v = unframe v
  | [] | [true] => rfl
  | false :: v => by simp [unframe, readFrameT_run_done]
  | true :: b :: v => by simp [unframe, readFrameT_run_true v]

lemma readFrameT_run_false : ∀ v, (readFrameT false).run .marker v = dropFrame v
  | [] | [true] => rfl
  | false :: v => by simp [dropFrame, readFrameT_run_done]
  | true :: b :: v => by simp [dropFrame, readFrameT_run_false v]

end Turing.MultiTapeTM.Internal.FrameMachines

namespace Turing.MultiTapeTM.Encodings

-- vendored: expose `frameT` and `frameT_run` for `computableInLogSpace_frame`; private upstream.
/-- Frames its input. -/
@[simps q₀ step final]
public def frameT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := [false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

public lemma frameT_run (v : List Bool) : frameT.run () v = frame v := by
  induction v <;> simp [*]

end Turing.MultiTapeTM.Encodings
