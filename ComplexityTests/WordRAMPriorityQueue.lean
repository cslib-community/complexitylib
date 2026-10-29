/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PriorityQueue.BinaryHeap

/-! Nonvacuity and interpreter checks for `IndexedMinPQ` and the standalone word-RAM binary
min-heap (`Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap`). -/

@[expose] public section

open Cslib Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.PriorityQueue
open Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap
open Cslib.Algorithms.WordRAM.PriorityQueue.BinaryHeap.Reg

namespace WordRAMPriorityQueueTests

/-- Pure interpreter step for a single `IndexedMinPQ` operation on `BinaryHeap.pqCode`. -/
def stepEval {n K_max : ℕ} (w fuel : ℕ) (x : Data rBin)
    (o : (IndexedMinPQ.spec n K_max).Op) :
    Option (Data rBin × (IndexedMinPQ.spec n K_max).Result o × ℕ) := do
  let x' : Data rBin :=
    { regs := fun i => if pqCode.input i then pqCode.encode o i else x.regs i, mem := x.mem }
  let yn ← pqCode.code.eval w fuel x'
  let res ← pqCode.decode (n := n) (K_max := K_max) o yn.1.regs
  pure (yn.1, res, yn.2)

/-- Full concrete trace exercising `initFresh`, `isEmpty`, `getKey` (absent and present), `insert`
(including key `0`), `decreaseKey`, equal-key lexicographic tie-breaking by `v.val`, and
`extractMin` down to empty, checking every operation's instruction count against `charge`. -/
def runSequence : Option (List (Option ℕ) × List (Option (Fin 4 × ℕ)) × Bool) := do
  let x0 := (((Data.init [] : Data rBin).set frontierReg 10).set nReg 4)
  let (x1, tInit) ← pqCode.initFresh.eval 10 8 x0
  let (x2, emp0, tEmp0) ← stepEval (n := 4) (K_max := 20) 10 8 x1 .isEmpty
  let (x3, gk0, tGk0) ← stepEval (n := 4) (K_max := 20) 10 8 x2 (.getKey 2)
  let (x4, _, tIns2) ← stepEval (n := 4) (K_max := 20) 10 8 x3 (.insert 2 0)
  let (x5, emp1, tEmp1) ← stepEval (n := 4) (K_max := 20) 10 8 x4 .isEmpty
  let (x6, gk2, tGk2) ← stepEval (n := 4) (K_max := 20) 10 8 x5 (.getKey 2)
  let (x7, gk1, tGk1) ← stepEval (n := 4) (K_max := 20) 10 8 x6 (.getKey 1)
  let (x8, _, tIns3) ← stepEval (n := 4) (K_max := 20) 10 8 x7 (.insert 3 5)
  let (x9, _, tIns1) ← stepEval (n := 4) (K_max := 20) 10 8 x8 (.insert 1 5)
  let (x10, _, tIns0) ← stepEval (n := 4) (K_max := 20) 10 8 x9 (.insert 0 9)
  let (x11, _, tDec0) ← stepEval (n := 4) (K_max := 20) 10 8 x10 (.decreaseKey 0 5)
  let (x12, e1, tExt1) ← stepEval (n := 4) (K_max := 20) 10 8 x11 .extractMin
  let (x13, e2, tExt2) ← stepEval (n := 4) (K_max := 20) 10 8 x12 .extractMin
  let (x14, e3, tExt3) ← stepEval (n := 4) (K_max := 20) 10 8 x13 .extractMin
  let (x15, e4, tExt4) ← stepEval (n := 4) (K_max := 20) 10 8 x14 .extractMin
  let (x16, e5, tExt5) ← stepEval (n := 4) (K_max := 20) 10 8 x15 .extractMin
  let (_, emp2, tEmp2) ← stepEval (n := 4) (K_max := 20) 10 8 x16 .isEmpty
  let ok :=
    decide (x1.regs frontierReg = 10 + space 4) &&
    decide (tInit ≤ 11) &&
    emp0 && !emp1 && emp2 &&
    decide (tEmp0 ≤ charge 4 .isEmpty ∧ tEmp1 ≤ charge 4 .isEmpty ∧ tEmp2 ≤ charge 4 .isEmpty) &&
    decide (tGk0 ≤ charge 4 (.getKey 2) ∧ tGk2 ≤ charge 4 (.getKey 2) ∧
      tGk1 ≤ charge 4 (.getKey 1)) &&
    decide (tIns2 ≤ charge 4 (.insert 2 0) ∧ tIns3 ≤ charge 4 (.insert 3 5) ∧
      tIns1 ≤ charge 4 (.insert 1 5) ∧ tIns0 ≤ charge 4 (.insert 0 9)) &&
    decide (tDec0 ≤ charge 4 (.decreaseKey 0 5)) &&
    decide (tExt1 ≤ charge 4 .extractMin ∧ tExt2 ≤ charge 4 .extractMin ∧
      tExt3 ≤ charge 4 .extractMin ∧ tExt4 ≤ charge 4 .extractMin ∧
      tExt5 ≤ charge 4 .extractMin)
  pure ([gk0, gk2, gk1], [e1, e2, e3, e4, e5], ok)

example : runSequence =
    some ([none, some 0, none],
      [some (2, 0), some (0, 5), some (1, 5), some (3, 5), none], true) := by
  decide +kernel

/-- Dirty-memory `initClear` check: starting with non-zero stale words across `[4, 4 + space 4)`,
`pqCode.initClear` wipes the heap footprint in `≤ 4 * space 4 + 17 = 69` instructions so subsequent
queries observe an empty priority queue and clean operations succeed. -/
def runDirtyInitClear : Option (Bool × Option ℕ × Option (Fin 4 × ℕ) × Bool) := do
  let dirty := (((Data.init (List.replicate 24 42) : Data rBin).set frontierReg 4).set nReg 4)
  let (x1, tClr) ← pqCode.initClear.eval 10 32 dirty
  let (x2, emp, _) ← stepEval (n := 4) (K_max := 20) 10 8 x1 .isEmpty
  let (x3, gk, _) ← stepEval (n := 4) (K_max := 20) 10 8 x2 (.getKey 1)
  let (x4, _, _) ← stepEval (n := 4) (K_max := 20) 10 8 x3 (.insert 1 7)
  let (_, ext, _) ← stepEval (n := 4) (K_max := 20) 10 8 x4 .extractMin
  let ok := decide (x1.regs frontierReg = 4 + space 4 ∧ tClr ≤ 4 * space 4 + 17)
  pure (emp, gk, ext, ok)

example : runDirtyInitClear = some (true, none, some (1, 7), true) := by
  decide +kernel

/-- Lift a single `IndexedMinPQ` operation into `Client` for `spec 4 20`. -/
abbrev callOp (o : IndexedMinPQ.Op 4) :
    (IndexedMinPQ.spec 4 20).Client ((IndexedMinPQ.spec 4 20).Result o) :=
  PFunctor.FreeM.lift (P := (IndexedMinPQ.spec 4 20).signature) o

/-- Concrete adaptive client inserting `(2, 8)` and `(1, 8)`, decreasing `2` to `0`, and extracting
the minimum. -/
def sampleClient : (IndexedMinPQ.spec 4 20).Client (Option (Fin 4 × ℕ)) := do
  callOp (.insert 2 8)
  callOp (.insert 1 8)
  callOp (.decreaseKey 2 0)
  callOp .extractMin

/-- Nonvacuity check for `BinaryHeap.subroutineDS`, `Rep`, `instruction_bound`, and
`run_client_bound`: initializes an actual `Rep 4 10 10 (IndexedMinPQ.empty 4) y₀` state from
zeroed memory and executes `sampleClient` over `Basis.standard` with result `some (2, 0)`. -/
example :
    ∃ y₀ y traces,
      Rep 4 10 10 (IndexedMinPQ.empty 4) y₀ ∧
      Stateful.Executes ((dynamicProgram 4 20).ExecOp 10) sampleClient y₀
        (some (2, 0)) y traces ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        (IndexedMinPQ.spec 4 20).totalCost (fun _ o => charge 4 o + 1)
          (IndexedMinPQ.empty 4)
          ((IndexedMinPQ.spec 4 20).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 := by
  have hS : Fits 10 (10 + space 4) := by decide
  have hK : Fits 10 20 := by decide
  let x₀ : Data rBin := (((⟨fun _ => 0, fun _ => 0⟩ : Data rBin).set frontierReg 10).set nReg 4)
  have hx₀ : x₀.Bounded 10 :=
    ⟨fun i => by fin_cases i <;> decide, fun _ => show Fits 10 0 by decide⟩
  have hfr : x₀.regs frontierReg = 10 := by decide
  have hpar : ∀ j, x₀.regs (pqCode.toSubroutineCode.initParams j) = (![4] : Fin 1 → ℕ) j := by
    intro j; fin_cases j; decide
  have hz : ∀ a ∈ (Block.mk 10 (space 4)).footprint, x₀.mem a = 0 := fun _ _ => rfl
  obtain ⟨y₀, _, _, hr₀, _, _⟩ := (subroutineDS hS hK).initFresh_exec hx₀ hfr hpar hz
  have hhist : ((IndexedMinPQ.spec 4 20).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 =
      [.insert 2 8, .insert 1 8, .decreaseKey 2 0, .extractMin] := rfl
  have hv : (IndexedMinPQ.spec 4 20).ValidHistory (IndexedMinPQ.empty 4)
      ((IndexedMinPQ.spec 4 20).runClient (IndexedMinPQ.empty 4) sampleClient).2.2 := by
    rw [hhist]
    simp [Stateful.Spec.ValidHistory, IndexedMinPQ.spec, IndexedMinPQ.empty]
  have hres : ((IndexedMinPQ.spec 4 20).runClient (IndexedMinPQ.empty 4) sampleClient).1 =
      some (2, 0) := by
    decide
  obtain ⟨y, traces, hex, _, hcost⟩ := run_client_bound hS hK sampleClient hr₀ hv
  rw [hres] at hex
  exact ⟨y₀, y, traces, hr₀, hex, hcost⟩

end WordRAMPriorityQueueTests
