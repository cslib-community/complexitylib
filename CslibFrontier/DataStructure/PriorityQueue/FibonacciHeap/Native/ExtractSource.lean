/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Memory

/-!
# Uniform result words for the original Fibonacci extraction source

The original extractor returns a typed handle. Erasing only that handle's type gives one result
type for every runtime capacity, without changing any memory query, state or operation history.
There is no new checked-pair decoder or extraction algorithm here.

## Main definitions

* `extractRaw`: the exact optional-pair erasure of the original `extractMin` program.

## Main results

* `link_extractRaw_eq`: erasure commutes with the original record-to-memory interpretation.
* `runClient_extractRaw`: full result, memory/frontier and history transport at every width.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM

/-- The original extraction source, with only the `Fin` proof erased from a successful result.
The returned words are the unshifted handle and key; absent results remain absent. -/
@[expose] def extractRaw (n : ℕ) : Prog (Option (ℕ × ℕ)) :=
  (Option.map (fun a : Fin n × ℕ => (a.1.val, a.2))) <$> extractMin n

/-- The same erasure applies after interpreting the record, as an equality of whole programs. -/
theorem link_extractRaw_eq {n : ℕ} (L : Record.Layout (Cell.ok n)) (handlerWidth : ℕ) :
    DataStructure.link (E := Memory.spec handlerWidth) (L.methods handlerWidth) (extractRaw n) =
      (Option.map (fun a : Fin n × ℕ => (a.1.val, a.2))) <$>
        DataStructure.link (E := Memory.spec handlerWidth) (L.methods handlerWidth)
          (extractMin n) :=
  PFunctor.FreeM.liftM_map _ _ _

/-- Result erasure retains every memory cell, the frontier and the complete query history.
Handler width and execution width are independent; validity remains a separate source premise. -/
theorem runClient_extractRaw {n : ℕ} (L : Record.Layout (Cell.ok n))
    (handlerWidth w : ℕ) (mem : Memory.State) :
    (Memory.spec w).runClient mem
      (DataStructure.link (E := Memory.spec handlerWidth) (L.methods handlerWidth) (extractRaw n)) =
      (Option.map (fun a : Fin n × ℕ => (a.1.val, a.2))
        ((Memory.spec w).clientResult mem (DataStructure.link (E := Memory.spec handlerWidth)
          (L.methods handlerWidth) (extractMin n))),
        (Memory.spec w).clientState mem (DataStructure.link (E := Memory.spec handlerWidth)
          (L.methods handlerWidth) (extractMin n)),
        (Memory.spec w).clientHistory mem (DataStructure.link (E := Memory.spec handlerWidth)
          (L.methods handlerWidth) (extractMin n))) := by
  rw [link_extractRaw_eq]
  rw [← bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind]
  rw [StateTransitionSpec.runClient_bind]
  simp only [StateTransitionSpec.runClient_pure', List.append_nil]

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
