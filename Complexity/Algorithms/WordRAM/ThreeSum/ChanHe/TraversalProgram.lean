/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStack
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Modulus
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeSpec

/-!
# Fixed native controller for one Chan–He recursion tree

The controller pops actual seven-word records, skips zero fuel or empty inputs, computes the
modulus, constructs the complete heavy and packed outputs, records the packed pointer, and
pushes the three children. Children are pushed third, second, first so the existing native
stack visits them in the mathematical preorder. Fresh allocations follow every live node;
all earlier arrays, the prime bitmap, stack reservation and output table precede the heap.

This module defines executable code. Its correctness and resource proofs belong to the
traversal development; these definitions alone do not certify a native preprocessing bound.
The frontend and initialized-input composition remain separate.

## Main definitions

* `oneRoot`: the finite native traversal controller, independent of fuel, input sizes and width.
* `visit`: complete native modulus and node construction, including output delivery.
* `pushChildren`: actual reverse-order stack pushes preserving the original three descriptors.

The native code is original and reuses the existing finite Chan–He construction.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

/-- The complete node kernels occupy registers 0–63. -/
def kernel (i : Fin 64) : Fin 128 := ⟨i.val, by omega⟩

/-- The supplied candidate-prime bound. -/
abbrev limit : Fin 128 := 71
/-- The supplied label-bit parameter. -/
abbrev digits : Fin 128 := 72
/-- The common input-magnitude bound of the tree. -/
abbrev magnitude : Fin 128 := 73
/-- The common number of packed four-cell groups. -/
abbrev groups : Fin 128 := 74
/-- The prime bitmap, retained below the heap. -/
abbrev bitmap : Fin 128 := 75
/-- The exact number of candidate primes. -/
abbrev primeCount : Fin 128 := 76
/-- The current fresh allocation base. -/
abbrev heap : Fin 128 := 77
/-- The reserved output-pointer table. -/
abbrev outputs : Fin 128 := 78
/-- Accumulated output count; this is not reset between roots. -/
abbrev outputCount : Fin 128 := 79
/-- The reserved word-stack base. -/
abbrev stackBase : Fin 128 := 80
/-- The reserved word-stack capacity, used by the safety specification. -/
abbrev stackCapacity : Fin 128 := 81
/-- Controller constant zero. -/
abbrev zero : Fin 128 := 82
/-- Controller constant one. -/
abbrev one : Fin 128 := 83
/-- Controller address temporary. -/
abbrev temporary : Fin 128 := 85
/-- The computed unsigned modulus. -/
abbrev selected : Fin 128 := 87
/-- The three computed heavy lengths. -/
def heavyLength (j : Fin 3) : Fin 128 := ⟨88 + j.val, by omega⟩
/-- The three computed heavy bases. -/
def heavyBase (j : Fin 3) : Fin 128 := ⟨91 + j.val, by omega⟩
/-- Current packed-array base. -/
abbrev packed : Fin 128 := 94
/-- One-past-end of the current node allocation. -/
abbrev endpoint : Fin 128 := 95
/-- Saved original descriptor words, outside both kernels and the stack dispatcher. -/
def original (i : Fin 4) : Fin 128 := ⟨105 + i.val, by omega⟩

/-- Fourteen actual instructions deliver the modulus program's complete caller ABI. -/
def prepareModulus : Code .standard 128 :=
  let p₀ := slot 1
  let n₀ := slot 2
  let p₁ := slot 3
  let n₁ := slot 4
  let p₂ := slot 5
  let n₂ := slot 6
  let s₀ := kernel (CountCall.source 0)
  let l₀ := kernel (CountCall.length 0)
  let s₁ := kernel (CountCall.source 1)
  let l₁ := kernel (CountCall.length 1)
  let s₂ := kernel (CountCall.source 2)
  let l₂ := kernel (CountCall.length 2)
  let scratch := kernel CountCall.scratch
  let histogram := kernel CountCall.histogram
  let m := kernel Search.limit
  let b := kernel Search.primes
  let c := kernel CollisionTest.card
  let d := kernel Modulus.digits
  ram[ s₀ ← p₀; l₀ ← n₀; s₁ ← p₁; l₁ ← n₁; s₂ ← p₂; l₂ ← n₂;
    scratch ← heap; histogram ← heap + n₀; histogram ← histogram + n₁;
    histogram ← histogram + n₂; m ← limit; b ← bitmap; c ← primeCount; d ← digits ]

/-- Ten actual copies deliver the complete node builder's caller ABI. -/
def prepareNode : Code .standard 128 :=
  let p₀ := slot 1
  let n₀ := slot 2
  let p₁ := slot 3
  let n₁ := slot 4
  let p₂ := slot 5
  let n₂ := slot 6
  let s₀ := kernel (NodePacking.source 0)
  let l₀ := kernel (NodePacking.length 0)
  let s₁ := kernel (NodePacking.source 1)
  let l₁ := kernel (NodePacking.length 1)
  let s₂ := kernel (NodePacking.source 2)
  let l₂ := kernel (NodePacking.length 2)
  let b := kernel NodePacking.base
  let n := kernel NodePacking.groups
  let u := kernel NodePacking.magnitude
  let m := kernel NodePacking.modulus
  ram[ s₀ ← p₀; l₀ ← n₀; s₁ ← p₁; l₁ ← n₁; s₂ ← p₂; l₂ ← n₂;
    b ← heap; n ← groups; u ← magnitude; m ← selected ]

/-- Read the three actual count cells, record the packed pointer, and advance the fresh heap. -/
def deliver : Code .standard 128 :=
  let n₀ := slot 2
  let n₁ := slot 4
  let n₂ := slot 6
  let h₀ := heavyBase 0
  let h₁ := heavyBase 1
  let h₂ := heavyBase 2
  let c₀ := heavyLength 0
  let c₁ := heavyLength 1
  let c₂ := heavyLength 2
  ram[ packed ← #3; packed ← heap + packed; packed ← packed + n₀;
    packed ← packed + n₁; packed ← packed + n₂;
    temporary ← outputs + outputCount; *temporary ← packed;
    outputCount ← outputCount + one; c₀ ← *heap; h₀ ← heap + one;
    temporary ← h₀ + n₀; c₁ ← *temporary; h₁ ← temporary + one;
    temporary ← h₁ + n₁; c₂ ← *temporary; h₂ ← temporary + one;
    endpoint ← groups + groups; endpoint ← endpoint + endpoint;
    endpoint ← packed + endpoint; endpoint ← endpoint + n₀; endpoint ← endpoint + n₁;
    endpoint ← endpoint + n₂; endpoint ← endpoint + selected; heap ← endpoint ]

/-- Complete actual native calls, with argument preparation, modulus copy and output delivery. -/
def visit : Code .standard 128 :=
  .seq prepareModulus (.seq (Modulus.program.rename kernel)
    (.seq (.op (.copy selected (kernel Modulus.output)))
      (.seq prepareNode (.seq (NodePacking.program.rename kernel) deliver))))

/-- Decrease fuel, retain both descriptors needed for restoration, and prepare the third child. -/
def prepareThird : Code .standard 128 :=
  let f := slot 0
  let p₁ := slot 3
  let n₁ := slot 4
  let p₂ := slot 5
  let n₂ := slot 6
  let op₁ := original 0
  let on₁ := original 1
  let op₂ := original 2
  let on₂ := original 3
  let h₂ := heavyBase 2
  let c₂ := heavyLength 2
  ram[ f ← f - one; op₁ ← p₁; on₁ ← n₁; op₂ ← p₂; on₂ ← n₂;
    p₂ ← h₂; n₂ ← c₂ ]

/-- Restore the third original descriptor and prepare the second child. -/
def prepareSecond : Code .standard 128 :=
  let p₁ := slot 3
  let n₁ := slot 4
  let p₂ := slot 5
  let n₂ := slot 6
  let op₂ := original 2
  let on₂ := original 3
  let h₁ := heavyBase 1
  let c₁ := heavyLength 1
  ram[ p₂ ← op₂; n₂ ← on₂; p₁ ← h₁; n₁ ← c₁ ]

/-- Restore the second original descriptor and prepare the first child. -/
def prepareFirst : Code .standard 128 :=
  let p₀ := slot 1
  let n₀ := slot 2
  let p₁ := slot 3
  let n₁ := slot 4
  let op₁ := original 0
  let on₁ := original 1
  let h₀ := heavyBase 0
  let c₀ := heavyLength 0
  ram[ p₁ ← op₁; n₁ ← on₁; p₀ ← h₀; n₀ ← c₀ ]

/-- Push third, second, first. Every child retains the two other original set descriptors. -/
def pushChildren : Code .standard 128 :=
  .seq prepareThird (.seq pushFrame (.seq prepareSecond
    (.seq pushFrame (.seq prepareFirst pushFrame))))

/-- A popped record either skips exactly the mathematical guard or executes the complete node. -/
def body : Code .standard 128 :=
  let f := slot 0
  let n₀ := slot 2
  let n₁ := slot 4
  let n₂ := slot 6
  let skip := Code.op (B := Basis.standard) (.copy f f)
  .seq popFrame (.branch (.eq f zero) skip
    (.branch (.eq n₀ zero) skip (.branch (.eq n₁ zero) skip
      (.branch (.eq n₂ zero) skip (.seq visit pushChildren)))))

/-- The actual pending-word stack, including zero-fuel and empty entries, controls the loop. -/
def loop : Code .standard 128 := .loop (.lt zero (registers Stack.len)) body

/-- The complete finite native controller for one supplied root. It appends to the caller's
output table, retaining the accumulated count and advancing the fresh allocation base. -/
def oneRoot : Code .standard 128 :=
  let ptr := registers Stack.ptr
  let len := registers Stack.len
  .seq (ram[ zero ← #0; one ← #1; ptr ← stackBase; len ← #0 ])
    (.seq pushFrame loop)

/-- The same finite controller is used at every admitted word width. -/
theorem oneRoot_not_readsWidth : ¬oneRoot.ReadsWidth := by decide

/-- The native controller has a fixed finite instruction list, independent of recursion fuel. -/
theorem oneRoot_size : oneRoot.size ≤ 65536 := by decide

/-- Registers 109–127 are retained for the outer frontend-forest controller. -/
theorem oneRoot_preserves : ∀ i : Fin 128, 109 ≤ i.val → oneRoot.Preserves i := by decide

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
