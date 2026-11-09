/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Backend
public import ComplexityTests.FibonacciHeapNativeExtract

/-!
# Original typed heap clients of the native Fibonacci method family

An actual source heap with a child inhabits the shared native representation. The existing
implementation interface gives a complete typed extraction transition. Its amortized clock
retains the original nonzero heap potential, and the shared frame theorem preserves the input.
Argument installation remains the explicit uncharged method calling convention.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeBackend

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open FibonacciHeapNativeCut

noncomputable section

private def impl := FibonacciHeap.Native.implementation
  (n := 3) (K := 63) (base := 2) (w := 6) (by decide) (by decide) (by decide)

private def old := abs 3 ((layout 3 2).abs consolidated)
/-- The shared native bank loaded with the original consolidated source memory. -/
@[expose] def initial := Backend.data certificates consolidated

private theorem represented : impl.rep old initial :=
  Backend.rep_data (implements (by decide) (by decide) (by decide))
    consolidated_wellFormed consolidated_inv rfl

/-- A genuine old heap supplies a typed transition in the five-tag native implementation. -/
theorem typed_extract : ∃ (a : Option (Fin 3 × ℕ))
    (y : Data (Backend.registers certificates)) (steps : ℕ),
    (backend 3 63 2).exec 6 initial .extractMin a y steps :=
  impl.total .extractMin represented trivial

/-- The family exposes the original nonzero-potential amortized contract at this actual client. -/
example {a : Option (Fin 3 × ℕ)} {y : Data (Backend.registers certificates)} {steps : ℕ}
    (he : (backend 3 63 2).exec 6 initial .extractMin a y steps) :
    steps + Backend.factor certificates *
        potential 3 ((layout 3 2).abs (memoryState (Backend.frontier certificates) y)) ≤
      Backend.factor certificates * (charge 3 old .extractMin + 1) +
        Backend.factor certificates * potential 3 ((layout 3 2).abs consolidated) := by
  obtain ⟨_, _, _, hcost⟩ :=
    (FibonacciHeap.Native.amortized (by decide) (by decide) (by decide)).step
      represented (show IndexedMinPQ.valid 63 old .extractMin from trivial) he
  simpa only [Nat.add_zero, id_eq, initial, Backend.memoryState_data] using hcost

/-- The full source frame keeps the maximum-word input even through nonempty extraction. -/
example {a : Option (Fin 3 × ℕ)} {y : Data (Backend.registers certificates)} {steps : ℕ}
    (he : (backend 3 63 2).exec 6 initial .extractMin a y steps) : y.mem 1 = 63 := by
  have hf := FibonacciHeap.Native.modifies (by decide) (by decide) (by decide)
    represented (show IndexedMinPQ.valid 63 old .extractMin from trivial) he
  have hm : initial.mem = consolidated.mem :=
    congrArg Memory.State.mem (Backend.memoryState_data certificates consolidated)
  exact (hf 1 (by decide)).trans ((congrFun hm 1).trans (by decide))

end

end ComplexityTests.FibonacciHeapNativeBackend
