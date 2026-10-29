/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalRoot
public import Complexity.Algorithms.WordRAM.PrimeTable

/-!
# Native initialized-input Chan–He preprocessing program

The complete finite instruction program first executes the native frontend and parameter
computation. It builds the prime bitmap by actual trial division, computes concrete stack and
output-table reservations, and loads and traverses every actual six-word frontend descriptor.
The ternary reservation is computed by a native multiplication loop, not supplied by a caller.

This module defines the executable program. `PreprocessingInput`, `PreprocessingWidth` and
`PreprocessingTime` prove initialized-input execution, derived width and charged global bounds.

## Main definitions

* `program`: one finite 128-register program per fixed magnitude exponent.
* `flatProgram`: the complete native program with its final count-returning halt.
* `loadRoot`, `forest`: actual descriptor loads and the outer native root loop.

## Main results

* `not_readsWidth`: runtime physical width never controls the program's computation.
* `size_program`: code size depends only on the fixed exponent.

The code and layout computations are original. Output metadata is unsigned; payload words use
the existing signed encoding. No solver, collision, primality or operation-count oracle is used.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Saved frontend descriptor base. -/
abbrev descriptors : Fin 128 := 109
/-- Saved number of roots. -/
abbrev roots : Fin 128 := 110
/-- Index of the next root. -/
abbrev current : Fin 128 := 111
/-- The computed recursion fuel shared by all roots. -/
abbrev levels : Fin 128 := 112
/-- The computed original-input magnitude. -/
abbrev inputMagnitude : Fin 128 := 113
/-- The computed candidate-prime bound. -/
abbrev candidateLimit : Fin 128 := 114
/-- The computed label-bit parameter. -/
abbrev labels : Fin 128 := 115
/-- Common packed length in words, retained as unsigned output metadata. -/
abbrev packedLength : Fin 128 := 116
/-- One-past-end frontend address; the shared prime bitmap begins here. -/
abbrev firstFree : Fin 128 := 117
/-- Six words per frontend root descriptor. -/
abbrev stride : Fin 128 := 118
/-- Outer-controller constant one. -/
abbrev one : Fin 128 := 119
/-- Outer-controller constant zero. -/
abbrev zero : Fin 128 := 120
/-- Descriptor-loading address temporary. -/
abbrev address : Fin 128 := 121
/-- Computed ternary-tree reservation. -/
abbrev power : Fin 128 := 122
/-- Remaining reservation multiplications. -/
abbrev remaining : Fin 128 := 123
/-- Reserved number of unsigned output pointers. -/
abbrev outputCapacity : Fin 128 := 124
/-- Setup constant, first seven and then three. -/
abbrev scalar : Fin 128 := 125
/-- The constant four converts packed words to groups. -/
abbrev four : Fin 128 := 126
/-- Initial heap frontier, above the complete stack and pointer-table reservations. -/
abbrev heapFloor : Fin 128 := 127

/-- The complete 15-register prime builder runs in the low registers. -/
def primeRegisters (i : Fin 15) : Fin 128 := ⟨i.val, by omega⟩

/-- Save every frontend/parameter output that the reused traversal registers will overwrite. -/
def snapshot : Code .standard 128 :=
  let frontBase := Frontend.descriptorBase
  let frontCount := Frontend.descriptorCount
  let frontEnd := Frontend.heapEnd
  let f := Frontend.parameterRegisters Parameters.fuel
  let U := Frontend.parameterRegisters Parameters.magnitude
  let m := Frontend.parameterRegisters Parameters.primeBound
  let Λ := Frontend.parameterRegisters Parameters.digits
  let N := Frontend.parameterRegisters Parameters.packedLen
  ram[ descriptors ← frontBase; roots ← frontCount; levels ← f; inputMagnitude ← U;
    candidateLimit ← m; labels ← Λ; packedLength ← N; firstFree ← frontEnd;
    current ← #0; stride ← #6; one ← #1; zero ← #0; four ← #4 ]

/-- Deliver the actual native prime-table inputs. -/
def preparePrimes : Code .standard 128 :=
  let m := primeRegisters PrimeTable.limit
  let b := primeRegisters PrimeTable.base
  ram[ m ← candidateLimit; b ← firstFree ]

/-- Compute the traversal ABI and concrete stack reservation, retaining the outer metadata. -/
def setupTraversal : Code .standard 128 :=
  let m := Traversal.limit
  let Λ := Traversal.digits
  let U := Traversal.magnitude
  let N := Traversal.groups
  let bitmap := Traversal.bitmap
  let card := Traversal.primeCount
  let nativeCard := primeRegisters PrimeTable.count
  let stack := Traversal.stackBase
  let capacity := Traversal.stackCapacity
  let out := Traversal.outputs
  let count := Traversal.outputCount
  let z := Traversal.zero
  let unit := Traversal.one
  ram[ m ← candidateLimit; Λ ← labels; U ← inputMagnitude + inputMagnitude;
    N ← packedLength / four; bitmap ← firstFree; card ← nativeCard;
    stack ← firstFree + candidateLimit; stack ← stack + one;
    capacity ← levels + levels; capacity ← capacity + one; scalar ← #7;
    capacity ← capacity * scalar; out ← stack + capacity; count ← #0; z ← #0; unit ← #1;
    power ← #1; remaining ← levels + one; scalar ← #3 ]

/-- One actual multiplication and decrement per ternary-reservation level. -/
def powerBody : Code .standard 128 := ram[
  power ← power * scalar; remaining ← remaining - one ]

/-- Compute `3^(fuel+1)` by a finite native loop. -/
def reserve : Code .standard 128 := .loop (.lt zero remaining) powerBody

/-- Reserve all output pointers before the initial fresh heap frontier. -/
def finishLayout : Code .standard 128 :=
  let out := Traversal.outputs
  let heap := Traversal.heap
  ram[ outputCapacity ← roots * power; heap ← out + outputCapacity; heapFloor ← heap ]

/-- Load all six descriptor words in their actual length/pointer order, with the shared fuel. -/
def loadRoot : Code .standard 128 :=
  let f := Traversal.slot 0
  let p₀ := Traversal.slot 1
  let n₀ := Traversal.slot 2
  let p₁ := Traversal.slot 3
  let n₁ := Traversal.slot 4
  let p₂ := Traversal.slot 5
  let n₂ := Traversal.slot 6
  ram[ address ← current * stride; address ← descriptors + address; f ← levels;
    n₀ ← *address; address ← address + one; p₀ ← *address; address ← address + one;
    n₁ ← *address; address ← address + one; p₁ ← *address; address ← address + one;
    n₂ ← *address; address ← address + one; p₂ ← *address ]

/-- Traverse the actually loaded root, then advance the actual descriptor index. -/
def body : Code .standard 128 :=
  .seq loadRoot (.seq Traversal.oneRoot (.op (.bin .add current current one)))

/-- Enumerate every frontend root, including the exact empty and multiplicity boundary roots. -/
def forest : Code .standard 128 := .loop (.lt current roots) body

/-- Complete native preprocessing after the native initialized-input frontend. -/
def afterFrontend : Code .standard 128 :=
  .seq snapshot (.seq (.seq preparePrimes (PrimeTable.program.rename primeRegisters))
    (.seq setupTraversal (.seq (.seq reserve finishLayout) forest)))

/-- One finite native program per fixed magnitude exponent, independent of input length/width. -/
def program (κ : ℕ) : Code .standard 128 := .seq (Frontend.program κ) afterFrontend

/-- Complete flat native program; it returns the unsigned output count. -/
def flatProgram (κ : ℕ) : Program .standard 128 := (program κ).program Traversal.outputCount

private theorem afterFrontend_not_readsWidth : ¬afterFrontend.ReadsWidth := by decide

/-- Physical width never determines radix passes, prime candidates, recursion fuel or code. -/
theorem not_readsWidth (κ : ℕ) : ¬(program κ).ReadsWidth :=
  not_or.mpr ⟨Frontend.not_readsWidth κ, afterFrontend_not_readsWidth⟩

/-- The finite controller adds a fixed code suffix to the exponent-dependent frontend. -/
theorem size_program (κ : ℕ) :
    (program κ).size = κ + 71 + Frontend.construct.size + afterFrontend.size := by
  rw [program, Code.size, Frontend.size_program]

/-- Only the current index and address scratch among registers 109–127 change during a root. -/
theorem body_preserves : ∀ i : Fin 128,
    109 ≤ i.val → i ≠ current → i ≠ address → body.Preserves i := by decide

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
