/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Admissible
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Host.ExecuteAt

/-!
# Canonical native ordinary 3SUM visitor

The fixed program constructs each actual Chan–He node and calls the existing Convolution host
before pushing its children. Calls follow the exact finite preorder and multiplicity; Boolean
accumulation does not exit early. The host receives the runtime packed pointer and current
allocation endpoint. Its return frame preserves every lower-prefix cell needed by pending work,
while permitting arbitrary higher scratch writes.

The ordinary path neither publishes nor reads a packed-pointer table. After each node is consumed,
one native copy releases its packed/residue/histogram tail before pushing the children. Persistent
heavy-array allocation is monotone and retains the conservative old table-gap reservation.
Heavy-buffer capacities and count cells remain allocated; the dead tail is reused. The separately
computed polynomial value envelope bounds signed values and arithmetic width, rather than
selecting a workspace address. No improved total-space or callee high-water bound is asserted. The
existing register ABI, width threshold and charged cost envelope are retained.

Executable constructors accept only finite solver code. Execution and resource certificates are
separate consumers, so evaluating the program does not evaluate proof-only time metadata. Inputs
shorter than three positions return false directly; this verdict shortcut does not claim that
their exact mathematical preprocessing instance lists are empty.

## Main definitions

* `registerCount`, `preprocessingRegisters`, `hostRegisters`, `controllerRegisters`: fixed banks.
* `readLength`, `power`: actual header and value-envelope instructions.
* `Visitor.consume`, `Visitor.releasePacked`: actual node consumption and one-copy tail release.
* `Visitor.oneRoot`, `Visitor.forest`: the native root and forest traversals.
* `program`, `flatProgram`: the single canonical controller and its raw Boolean-returning halt.

These native control and layout choices are original. Consumer modules prove initialized
execution, resources and the concrete ordinary 1.9992 endpoint.
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
/-- Accumulated raw Boolean. -/
abbrev answer : Fin 16 := 11
/-- Load-address temporary. -/
abbrev address : Fin 16 := 13
/-- Constant zero. -/
abbrev zero : Fin 16 := 15

/-- Read only the ordinary raw length header and initialize the small-case verdict. -/
def readLength : Code .standard 16 := ram[
  address ← #0; inputLength ← *address; three ← #3; answer ← #0 ]

/-- Every multiplication and loop decrement is an actual charged instruction. -/
def powerBody : Code .standard 16 := ram[
  envelope ← envelope * scale; remaining ← remaining - one ]

/-- Compute the fixed-exponent value bound by native iteration. -/
def power : Code .standard 16 := .loop (.lt zero remaining) powerBody

namespace Visitor

/-- Copy actual current-node metadata into the disjoint Convolution host bank. -/
def prepareHost {r : ℕ} : Code .standard (registerCount r) :=
  let p := preprocessingRegisters r
  let m := controllerRegisters r
  let h := fun i => hostRegisters r (Host.hostRegisters (r := r + 7) i)
  let hLength := h Host.len
  let hUpper := h Host.upper
  let hBase := h Host.base
  let hWorkspace := h Host.matAB
  let pLength := p ChanHe.Preprocessing.packedLength
  let pPacked := p ChanHe.Traversal.packed
  let pHeap := p ChanHe.Traversal.heap
  let mEnvelope := m envelope
  ram[ hLength ← pLength; hUpper ← mEnvelope; hBase ← pPacked; hWorkspace ← pHeap ]

/-- OR the actual solver return into the existing Boolean accumulator. -/
def receive {r : ℕ} : Code .standard (registerCount r) :=
  let verdict := hostRegisters r (Host.hostRegisters (r := r + 7) Host.found)
  let mOne := controllerRegisters r one
  let mAnswer := controllerRegisters r answer
  ram[ if verdict = mOne then [ mAnswer ← mOne ] else [ mAnswer ← mAnswer ] ]

/-- The existing complete caller-owned host consumes this node immediately. -/
def consume {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .seq prepareHost (.seq ((Host.bodyAt solver).rename (hostRegisters r)) receive)

/-- Release the consumed packed/residue/histogram tail, retaining all live heavy arrays. -/
def releasePacked {r : ℕ} : Code .standard (registerCount r) :=
  .op (.copy (preprocessingRegisters r ChanHe.Traversal.heap)
    (preprocessingRegisters r ChanHe.Traversal.packed))

/-- Construct, consume, release the dead packed tail and expand one actual live node. -/
def visit {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  .seq (ChanHe.Traversal.localVisit.rename (preprocessingRegisters r))
    (.seq (consume solver)
      (.seq releasePacked (ChanHe.Traversal.pushChildren.rename (preprocessingRegisters r))))

/-- Pop and apply the exact zero-fuel and three empty-column guards before a live visit. -/
def body {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  let p := preprocessingRegisters r
  let f := p (ChanHe.Traversal.slot 0)
  let n₀ := p (ChanHe.Traversal.slot 2)
  let n₁ := p (ChanHe.Traversal.slot 4)
  let n₂ := p (ChanHe.Traversal.slot 6)
  let z := p ChanHe.Traversal.zero
  let skip := Code.op (B := Basis.standard) (.copy f f)
  .seq (ChanHe.Traversal.popFrame.rename p) (.branch (.eq f z) skip
    (.branch (.eq n₀ z) skip (.branch (.eq n₁ z) skip
      (.branch (.eq n₂ z) skip (visit solver)))))

/-- Initialize the actual native stack, then consume one root in preorder. -/
def oneRoot {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  let p := preprocessingRegisters r
  let z := p ChanHe.Traversal.zero
  let o := p ChanHe.Traversal.one
  let ptr := p (ChanHe.Traversal.registers ChanHe.Traversal.WordStack.ptr)
  let len := p (ChanHe.Traversal.registers ChanHe.Traversal.WordStack.len)
  let stack := p ChanHe.Traversal.stackBase
  .seq (ram[ z ← #0; o ← #1; ptr ← stack; len ← #0 ])
    (.seq (ChanHe.Traversal.pushFrame.rename p) (.loop (.lt z len) (body solver)))

/-- Visit the actual frontend forest without publishing or loading a packed-pointer table. -/
def forest {r : ℕ} (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  let p := preprocessingRegisters r
  let i := p ChanHe.Preprocessing.current
  let n := p ChanHe.Preprocessing.roots
  let o := p ChanHe.Preprocessing.one
  .loop (.lt i n) (.seq (ChanHe.Preprocessing.loadRoot.rename p)
    (.seq (oneRoot solver) (.op (.bin .add i i o))))

/-- Compute the input-global value envelope before entering the first actual node. -/
def prepareEnvelope {r : ℕ} (κ : ℕ) : Code .standard (registerCount r) :=
  let m := controllerRegisters r
  let mOne := m one
  let mTwo := m two
  let mZero := m zero
  let mScale := m scale
  let mInput := m inputLength
  let mEnvelope := m envelope
  let mRemaining := m remaining
  ram[ mOne ← #1; mTwo ← #2; mZero ← #0; mScale ← mInput + mTwo;
    mEnvelope ← #1; mRemaining ← #(envelopeExponent κ) ]

/-- Reuse the actual scalar snapshot, prime bitmap and traversal-layout initialization. -/
def prepareTraversal : Code .standard 128 :=
  .seq ChanHe.Preprocessing.snapshot
    (.seq (.seq ChanHe.Preprocessing.preparePrimes
      (PrimeTable.program.rename ChanHe.Preprocessing.primeRegisters))
      (.seq ChanHe.Preprocessing.setupTraversal
        (.seq ChanHe.Preprocessing.reserve ChanHe.Preprocessing.finishLayout)))

end Visitor

/-- Reuse native frontend/prime/layout initialization before the fused root forest. -/
def large {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) : Code .standard (registerCount r) :=
  let p := preprocessingRegisters r
  .seq ((Frontend.program κ).rename p)
    (.seq (Visitor.prepareTraversal.rename p)
      (.seq (Visitor.prepareEnvelope κ)
        (.seq (power.rename (controllerRegisters r)) (Visitor.forest solver))))

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
