/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Admissible
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.ExecuteAt

/-!
# Native ordinary 3SUM controller

The fixed program executes preprocessing, reads its raw table/count/common-length registers,
and passes each actual payload pointer to the existing Convolution host. Matrices and solver
workspace begin at preprocessing's actual final heap frontier, above every live table and payload
cell. The independent polynomial word envelope bounds signed values and arithmetic width. No packed
input is copied or replaced; the concrete callee must keep the entire lower prefix.

The executable constructors take only finite solver code. Execution and resource certificates
are separate consumers, so proof-only time bounds do not affect evaluation of the program.

Inputs shorter than three positions return false directly. This is an intentional final verdict
shortcut; it does not claim that their exact preprocessing instance lists are empty.

## Main definitions

* `registerCount`, `preprocessingRegisters`, `hostRegisters`, `controllerRegisters`: fixed banks.
* `envelopeExponent`: exponent of the reused preprocessing word bound.
* `program`, `flatProgram`: actual finite controller and its raw Boolean-returning halt.

These native control/layout choices are original. The fast solver and final exponent 1.9992
remain separate; correctness and resource proofs are supplied in the consumer modules.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Fixed register count for preprocessing, one Convolution host/callee and sixteen controls. -/
abbrev registerCount (r : ℕ) : ℕ := 128 + (64 + (r + 7)) + 16

/-- The complete original preprocessing bank. -/
def preprocessingRegisters (r : ℕ) (i : Fin 128) : Fin (registerCount r) :=
  (i.castAdd (64 + (r + 7))).castAdd 16

/-- A disjoint bank for the actual Convolution host and supplied finite callee. -/
def hostRegisters (r : ℕ) (i : Fin (64 + (r + 7))) : Fin (registerCount r) :=
  (i.natAdd 128).castAdd 16

/-- Outer controls survive both preprocessing and every Convolution call. -/
def controllerRegisters (r : ℕ) (i : Fin 16) : Fin (registerCount r) :=
  i.natAdd (128 + (64 + (r + 7)))

/-- Saved actual input length. -/
abbrev inputLength : Fin 16 := 0
/-- Base `n+2` of the polynomial value bound. -/
abbrev scale : Fin 16 := 1
/-- Computed polynomial word envelope. -/
abbrev envelope : Fin 16 := 2
/-- Remaining native multiplications. -/
abbrev remaining : Fin 16 := 3
/-- Constant one. -/
abbrev one : Fin 16 := 4
/-- Constant two. -/
abbrev two : Fin 16 := 5
/-- Boundary-case threshold. -/
abbrev three : Fin 16 := 6
/-- Actual preprocessing pointer-table base. -/
abbrev table : Fin 16 := 7
/-- Actual preprocessing output count. -/
abbrev count : Fin 16 := 8
/-- Actual common packed length. -/
abbrev length : Fin 16 := 9
/-- Next actual table entry. -/
abbrev current : Fin 16 := 10
/-- Accumulated raw Boolean. -/
abbrev answer : Fin 16 := 11
/-- Actual pointed-to signed payload. -/
abbrev source : Fin 16 := 12
/-- Load-address temporary. -/
abbrev address : Fin 16 := 13
/-- Caller-owned matrix workspace, copied from the final live allocation frontier. -/
abbrev workspace : Fin 16 := 14
/-- Constant zero. -/
abbrev zero : Fin 16 := 15

/-- Read only the ordinary raw length header and initialize the small-case verdict. -/
def readLength : Code .standard 16 := ram[
  address ← #0; inputLength ← *address; three ← #3; answer ← #0 ]

/-- Save the actual preprocessing ABI and live frontier; initialize the value-bound loop. -/
def setup {r : ℕ} (κ : ℕ) : Code .standard (registerCount r) :=
  let m := controllerRegisters r
  let p := preprocessingRegisters r
  let out := p ChanHe.Traversal.outputs
  let num := p ChanHe.Traversal.outputCount
  let packed := p ChanHe.Preprocessing.packedLength
  let frontier := p ChanHe.Traversal.heap
  let mTable := m table
  let mCount := m count
  let mLength := m length
  let mWorkspace := m workspace
  let mOne := m one
  let mTwo := m two
  let mZero := m zero
  let mScale := m scale
  let mInput := m inputLength
  let mEnvelope := m envelope
  let mRemaining := m remaining
  let mCurrent := m current
  ram[ mTable ← out; mCount ← num; mLength ← packed; mWorkspace ← frontier;
    mOne ← #1; mTwo ← #2; mZero ← #0;
    mScale ← mInput + mTwo; mEnvelope ← #1;
    mRemaining ← #(envelopeExponent κ); mCurrent ← #0 ]

/-- Every multiplication and loop decrement is an actual charged instruction. -/
def powerBody : Code .standard 16 := ram[
  envelope ← envelope * scale; remaining ← remaining - one ]

/-- Compute the fixed-exponent value bound by native iteration. -/
def power : Code .standard 16 := .loop (.lt zero remaining) powerBody

/-- Fetch the next actual pointer; no mathematical layout function supplies runtime advice. -/
def loadSource : Code .standard 16 := ram[
  address ← table + current; source ← *address ]

/-- Deliver four raw arguments to the caller-owned Convolution entry point. -/
def callSetup {r : ℕ} : Code .standard (registerCount r) :=
  let m := controllerRegisters r
  let h := fun i => hostRegisters r (Host.hostRegisters (r := r + 7) i)
  let hLen := h Host.len
  let hUpper := h Host.upper
  let hBase := h Host.base
  let hAB := h Host.matAB
  let mLength := m length
  let mEnvelope := m envelope
  let mSource := m source
  let mWorkspace := m workspace
  ram[ hLen ← mLength; hUpper ← mEnvelope; hBase ← mSource; hAB ← mWorkspace ]

/-- Accumulate the actual Convolution return and advance one pointer. -/
def finish {r : ℕ} : Code .standard (registerCount r) :=
  let m := controllerRegisters r
  let verdict := hostRegisters r (Host.hostRegisters (r := r + 7) Host.found)
  let mOne := m one
  let mAnswer := m answer
  let mCurrent := m current
  ram[ if verdict = mOne then [ mAnswer ← mOne ] else [ mAnswer ← mAnswer ];
    mCurrent ← mCurrent + mOne ]

/-- One complete native pointed-to Convolution call. -/
def body {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .seq (.seq (loadSource.rename (controllerRegisters r)) callSetup)
    (.seq ((Host.bodyAt solver).rename (hostRegisters r)) finish)

/-- Visit all actually emitted packed instances. -/
def calls {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .loop (.lt (controllerRegisters r current) (controllerRegisters r count)) (body solver)

/-- Actual preprocessing and all caller-safe solver calls on inputs with at least three entries. -/
def large {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .seq ((ChanHe.Preprocessing.program κ).rename (preprocessingRegisters r))
    (.seq (.seq (setup κ) (power.rename (controllerRegisters r))) (calls solver))

/-- One finite standard-code body per fixed input exponent and concrete finite callee. -/
def program {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .seq (readLength.rename (controllerRegisters r))
    (.branch (.lt (controllerRegisters r inputLength) (controllerRegisters r three))
      (.op (.copy (controllerRegisters r answer) (controllerRegisters r answer))) (large κ solver))

/-- The single final halt returns the raw accumulated Boolean. -/
def flatProgram {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) :
    Program .standard (registerCount r) :=
  (program κ solver).program (controllerRegisters r answer)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
