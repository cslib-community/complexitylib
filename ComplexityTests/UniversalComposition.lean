/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Compose
public import ComplexityTests.UniversalExecution

/-!
# Universal-machine composition at emission boundaries

Concrete descriptions exercise a final emission on the halting transition, a silent inner step,
recomputation after the outer machine halts, empty output, and the distinction between blanks and
zero-valued symbols. Literal output words are checked both through the control interpreter and
through the actual multi-pass callbacks.
-/

@[expose] public section

namespace ComplexityTests.UniversalComposition

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal
open ComplexityTests.UniversalExecution (emitsAcrossSilence)

/-- Copy each input bit and move right; a missing transition on blank halts without emission. -/
def copyBits : Desc where
  tapes := 0
  q₀ := 10
  table :=
    [(⟨10, some 0, []⟩, ⟨.pos, [], some 0, some 10⟩),
     (⟨10, some 1, []⟩, ⟨.pos, [], some 1, some 10⟩)]

/-- Copy the first input bit and halt on that same transition. -/
def firstBit : Desc where
  tapes := 0
  q₀ := 20
  table :=
    [(⟨20, some 0, []⟩, ⟨.zero, [], some 0, none⟩),
     (⟨20, some 1, []⟩, ⟨.zero, [], some 1, none⟩)]

/-- Halt at the first step with an empty output because no transition is present. -/
def emptyOutput : Desc where
  tapes := 0
  q₀ := 30
  table := []

/-- The composition control after a fixed number of interpreter steps. -/
def controlAt (outer inner : Desc) (input : List ℕ) (ticks : ℕ) : Ctl :=
  (fun c : Ctl => cstep c (inputSymbol input c.1.2.2.inputPos))^[ticks] (ctl₀ outer inner)

/-- Collect actual pre-transition emissions from the composition control. -/
def composedOutput (outer inner : Desc) (input : List ℕ) (ticks : ℕ) : List Bool :=
  ((List.range ticks).map fun i => gEmit (controlAt outer inner input i)).flatten

-- Three inner steps precede each outer step; emissions occur at indices 3 and 7; the outer machine
-- may halt before consuming the second inner output symbol; and empty inner output remains blank.
example :
    simulate copyBits [0, 1] 3 = ([0, 1], true) ∧
      composedOutput copyBits emitsAcrossSilence [] 3 = [] ∧
      composedOutput copyBits emitsAcrossSilence [] 4 = [false] ∧
      composedOutput copyBits emitsAcrossSilence [] 7 = [false] ∧
      composedOutput copyBits emitsAcrossSilence [] 8 = [false, true] ∧
      composedOutput copyBits emitsAcrossSilence [] 11 = [false, true] ∧
      (controlAt copyBits emitsAcrossSilence [] 11).1.1.2.state.isNone = false ∧
      composedOutput copyBits emitsAcrossSilence [] 12 = [false, true] ∧
      (controlAt copyBits emitsAcrossSilence [] 12).1.1.2.state.isNone = true ∧
      composedOutput copyBits emitsAcrossSilence [] 20 = [false, true] ∧
      composedOutput firstBit emitsAcrossSilence [] 3 = [] ∧
      composedOutput firstBit emitsAcrossSilence [] 4 = [false] ∧
      (controlAt firstBit emitsAcrossSilence [] 4).1.1.2.state.isNone = true ∧
      composedOutput firstBit emitsAcrossSilence [] 20 = [false] ∧
      (controlAt copyBits emptyOutput [] 1).1.1.2.state.isNone = false ∧
      (controlAt copyBits emptyOutput [] 2).1.1.2.state.isNone = true ∧
      composedOutput copyBits emptyOutput [] 8 = [] := by decide

/-- Read an outer input position after actually running the inner emitter to its first halt. -/
def innerSymbolAt (position : ℕ) : Option ℕ :=
  let outer : SCfg := ⟨some copyBits.q₀, position, []⟩
  let c : Ctl :=
    (((copyBits, outer), (emitsAcrossSilence, init emitsAcrossSilence)), (position, 0))
  gSym ((fun c : Ctl => cstep c none)^[3] c)

/-- Scan the actual input through the same callback used by composition's multi-pass fold. -/
def scannedSymbolAt (position : ℕ) : Option ℕ :=
  let inner : SCfg := ⟨some copyBits.q₀, position, []⟩
  let c : Ctl := (((copyBits, init copyBits), (copyBits, inner)), (1, 0))
  xSym (streamState (c, (position, 0)) cNext [false, true] 2)

/-- Collect the real end-of-pass emissions after each complete scan of the input. -/
def passOutput (outer inner : Desc) (input : List Bool) (passes : ℕ) : List Bool :=
  ((List.range passes).map fun i =>
    gEmit (streamState (passState (cInit outer inner) cNext cEnd input i)
      cNext input input.length).1).flatten

-- The zeroes in countdown storage do not turn boundary blanks into false bits, and multi-pass
-- input scanning exercises `cNext` and `cEnd` on every pass.
example :
    [0, 1, 2, 3].map innerSymbolAt = [none, some 0, some 1, none] ∧
      [0, 1, 2, 3].map scannedSymbolAt = [none, some 0, some 1, none] ∧
      passOutput copyBits copyBits [false, true] 3 = [] ∧
      passOutput copyBits copyBits [false, true] 4 = [false] ∧
      passOutput copyBits copyBits [false, true] 7 = [false] ∧
      passOutput copyBits copyBits [false, true] 8 = [false, true] ∧
      passOutput copyBits copyBits [false, true] 12 = [false, true] ∧
      passOutput copyBits copyBits [false, true] 20 = [false, true] ∧
      passOutput firstBit copyBits [true, false] 20 = [true] ∧
      passOutput copyBits emptyOutput [] 8 = [] := by decide

end ComplexityTests.UniversalComposition
