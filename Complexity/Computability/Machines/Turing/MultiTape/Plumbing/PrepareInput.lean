/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.MarkWork
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork

/-!
# Preparing a buffered word for use as input

A completed output buffer has its head just past the word. `prepareInput` marks the cell left of
the flag head and rewinds the word, using the existing `markWork` and `rewindWork` machines.
Every other tape and head, the real input head, and the output are preserved.

## Main definitions

* `Turing.MultiTapeTM.prepareInput`: prepare the last two work tapes as a virtual input.

## Main results

* `Turing.MultiTapeTM.runFrom_prepareInput`: the handoff costs `word.length + 4` transitions,
  including when the word is empty.

## References

Adapted from MultiTape/Plumbing/PrepareInput.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Christian Reitwiessner's tape routines.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Mark the left boundary and rewind the buffered word on the last two work tapes. -/
noncomputable def prepareInput (k : ℕ) (mark : Symbol) :
    MultiTapeTM (k + 2) Symbol (MarkWorkState ⊕ RewindWorkState) :=
  ((markWork Symbol (some mark)).extendTapes (tapeEmb (Fin.natAdd k 1))).seq
    ((rewindWork Symbol).extendTapes (tapeEmb (Fin.natAdd k 0)))

/-- Preparation rewinds the buffered word and marks its left boundary, preserving all other data.
The flag head must start at zero; the caller ensures its tape is otherwise blank. -/
theorem runFrom_prepareInput (mark : Symbol) (cfg : Cfg (k + 2) Symbol State input)
    (word : List Symbol) (hword : cfg.workTapes (Fin.natAdd k 0) = tapeOfList word)
    (hhead : cfg.workTapePos (Fin.natAdd k 0) = word.length)
    (hflag : cfg.workTapePos (Fin.natAdd k 1) = 0) :
    (prepareInput k mark).runFrom (cfg.withState (some (prepareInput k mark).q₀))
        (word.length + 4) =
      { cfg.withState (none : Option (MarkWorkState ⊕ RewindWorkState)) with
        workTapes := Function.update cfg.workTapes (Fin.natAdd k 1)
          (Function.update (cfg.workTapes (Fin.natAdd k 1)) (-1) (some mark))
        workTapePos := Function.update cfg.workTapePos (Fin.natAdd k 0) 0 } := by
  let marker := (markWork Symbol (some mark)).extendTapes (tapeEmb (Fin.natAdd k (1 : Fin 2)))
  let rewind := (rewindWork Symbol).extendTapes (tapeEmb (Fin.natAdd k (0 : Fin 2)))
  let mid : Cfg (k + 2) Symbol MarkWorkState input :=
    { cfg.withState none with
      workTapes := Function.update cfg.workTapes (Fin.natAdd k 1)
        (Function.update (cfg.workTapes (Fin.natAdd k 1)) (-1) (some mark)) }
  have hmark : marker.runFrom (cfg.withState (some marker.q₀)) 2 = mid := by
    simp only [marker, runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀,
      runFrom_markWork, embed_tapeEmb]
    simp [mid, Cfg.withState, hflag]
  have hrewind : rewind.runFrom (mid.withState (some rewind.q₀)) (word.length + 2) =
      { mid.withState (none : Option RewindWorkState) with
        workTapePos := Function.update cfg.workTapePos (Fin.natAdd k 0) 0 } := by
    simp only [rewind, runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀]
    have hmid : mid.workTapes (Fin.natAdd k 0) = cfg.workTapes (Fin.natAdd k 0) := by
      simp [mid]
    rw [hmid, show mid.workTapePos (Fin.natAdd k 0) = word.length from hhead,
      runFrom_rewindWork_none _ _ _ hword le_rfl, embed_tapeEmb]
    simp [mid, Cfg.withState]
  have hseq := runFrom_seq hmark rfl hrewind rfl
  simp only [prepareInput, marker, rewind, mid, Cfg.mapState,
    Cfg.withState, Option.map_none,
    show 2 + (word.length + 2) = word.length + 4 by lia] at hseq ⊢
  exact hseq

end Turing.MultiTapeTM
