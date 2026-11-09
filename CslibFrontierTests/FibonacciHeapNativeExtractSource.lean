/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.ExtractSource
public import CslibFrontier.Computability.WordRAM.Realization.Basic

/-!
# Exact extraction-result erasure

The erasure retains the entire memory/frontier and query history, independently of validity.
Concrete source clients cover zero capacity at three-bit width and a singleton maximum-key
extraction. The optional pair uses an unshifted handle and key; this is still source validation,
not a native extraction certificate.
-/

public section

namespace CslibFrontierTests.FibonacciHeapNativeExtractSource

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native

/-- The exact erasure equation preserves the full memory and history pair, even before any
particular allocated layout or validity hypothesis is supplied. -/
example {n : ℕ} (L : Record.Layout (Cell.ok n)) (handlerWidth w : ℕ) (mem : Memory.State) :
    ((Memory.spec w).runClient mem
      (Cslib.DataStructure.link (E := Memory.spec handlerWidth) (L.methods handlerWidth)
        (extractRaw n))).2 =
      ((Memory.spec w).runClient mem
        (Cslib.DataStructure.link (E := Memory.spec handlerWidth) (L.methods handlerWidth)
          (extractMin n))).2 := by
  rw [runClient_extractRaw]

/-- The original allocator admits zero capacity at width three, retaining the maximum input. -/
@[expose] def emptyZero : Memory.State :=
  (Memory.spec 3).clientState (Memory.State.init [7])
    ((zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)).run (pure ()))

example :
    let p := Cslib.DataStructure.link (E := Memory.spec 0) ((layout 0 2).methods 0) (extractRaw 0)
    (Memory.spec 3).ValidHistory emptyZero ((Memory.spec 3).clientHistory emptyZero p) ∧
    (Memory.spec 3).clientResult emptyZero p = none ∧ memoryCost p emptyZero = 1 ∧
    ((Memory.spec 3).clientState emptyZero p).mem 1 = 7 ∧
    ((Memory.spec 3).clientState emptyZero p).frontier = 7 := by decide

/-- One actual valid insertion at the original maximum key. -/
@[expose] def singleton : Memory.State :=
  (Memory.spec 5).clientState (Memory.State.init [31])
    ((zeroAllocator (n := 1) (K := 31) (w := 5) (by decide) (by decide)).run
      ((indexedMinPQSpec 1 31).call (.insert 0 31)))

example :
    let p := Cslib.DataStructure.link (E := Memory.spec 0) ((layout 1 2).methods 0) (extractRaw 1)
    (Memory.spec 5).ValidHistory singleton ((Memory.spec 5).clientHistory singleton p) ∧
    (Memory.spec 5).clientResult singleton p = some (0, 31) ∧ memoryCost p singleton = 12 ∧
    ((Memory.spec 5).clientState singleton p).mem 1 = 31 ∧
    ((Memory.spec 5).clientState singleton p).frontier = 16 := by decide

end CslibFrontierTests.FibonacciHeapNativeExtractSource
