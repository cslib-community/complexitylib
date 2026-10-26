/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of universal-machine execution)

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic

/-!
# Universal-machine execution at halting and input boundaries

Concrete transition tables check the collected output and halt flag at clocks before, at and
after a halt. Input and work-tape examples distinguish a blank cell from the natural-number
symbol zero.
-/

@[expose] public section

namespace ComplexityTests.UniversalExecution

open Turing.MultiTapeTM.Universal

/-- Emit zero, take a silent step, then emit one on the transition that halts. -/
def emitsAcrossSilence : Desc where
  tapes := 0
  q₀ := 0
  table :=
    [(⟨0, none, []⟩, ⟨.zero, [], some 0, some 1⟩),
      (⟨1, none, []⟩, ⟨.zero, [], none, some 2⟩),
      (⟨2, none, []⟩, ⟨.zero, [], some 1, none⟩)]

example : simulate emitsAcrossSilence [] 0 = ([], false) := by decide

example : simulate emitsAcrossSilence [] 1 = ([0], false) := by decide

example : simulate emitsAcrossSilence [] 2 = ([0], false) := by decide

example : simulate emitsAcrossSilence [] 3 = ([0, 1], true) := by decide

example : simulate emitsAcrossSilence [] 8 = ([0, 1], true) := by decide

/-- Read a real zero, emit seven and move right to a state with no transition. -/
def missingTransition : Desc where
  tapes := 0
  q₀ := 0
  table := [(⟨0, some 0, []⟩, ⟨.pos, [], some 7, some 1⟩)]

example : simulate missingTransition [0, 1] 1 = ([7], false) := by decide

example : simulate missingTransition [0, 1] 2 = ([7], true) := by decide

example : simulate missingTransition [0, 1] 6 = ([7], true) := by decide

-- A blank does not match the transition for a real zero.
example : simulate missingTransition [] 0 = ([], false) := by decide

example : simulate missingTransition [] 1 = ([], true) := by decide

-- The missing transition changes the halt status without moving the head or losing prior output.
example :
    let c := (stepOut missingTransition [0, 1])^[2] (init missingTransition, [])
    (c.1.inputPos, c.1.state, c.2) = (2, none, [7]) := by decide

/-- A halted configuration whose position is the initial input position. -/
def halted : SCfg := ⟨none, 1, []⟩

example : stepWith emitsAcrossSilence halted none = (halted, none) := rfl

example : stepOut emitsAcrossSilence [] (halted, [7, 0]) = (halted, [7, 0]) := rfl

-- There are separate left and right blanks, while the first actual symbol is zero.
example : [0, 1, 2, 3].map (inputSymbol [0, 1]) = [none, some 0, some 1, none] := by
  decide

example : [0, 1, 2].map (inputSymbol []) = [none, none, none] := by decide

example :
    [0, 1, 2, 3].map (fun p => moveInput p (inputSymbol [0, 1] p) .pos) =
      [1, 2, 3, 3] := by decide

example :
    [0, 1, 2, 3].map (fun p => moveInput p (inputSymbol [0, 1] p) .neg) =
      [0, 0, 1, 2] := by decide

example :
    [0, 1].map (fun p => moveInput p (inputSymbol [] p) .pos) = [1, 1] := by decide

/-- A work tape containing a real zero at the head. -/
def zeroTape : Tape := ⟨0, [], [some 0]⟩

-- Moving away and back with no write keeps zero; an explicit erasure removes it before moving.
example :
    let t := (zeroTape.apply (none, .pos)).move .neg
    (t.head, t.read) = (0, some 0) := by decide

example :
    let t := (zeroTape.apply (some none, .pos)).move .neg
    (t.head, t.read) = (0, none) := by decide

end ComplexityTests.UniversalExecution
