/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterExecution

/-!
Actual fixed-dispatcher calls carry their count registers from one call to the next. External
prepare delivers only tag/payload; no Backend.install or replacement metadata is used. The
six-instruction initializer starts from dirty registers and preserves every memory cell.
-/

@[expose] public section

namespace CslibFrontierTests.QueueRegisterExecution

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.Queue.WordRAM

/-- Dirty entry registers, zero-valued physical and inaccessible memory. -/
def rawTwo : Data registers := ⟨fun _ => 3, fun _ => 0⟩

theorem rawTwo_bounded : rawTwo.Bounded 2 :=
  ⟨fun _ => (by decide : Fits 2 3), fun _ => fits_zero 2⟩

/-- At the old small-width boundary, one fixed program enqueues and dequeues every fitting
value, with paid initialization, carried metadata, typed observation and an intact sentinel. -/
theorem roundTrip_native (v : ℕ) (hv : Fits 2 v) :
    ∃ ready y z n m, Exec 2 (initializeCode 1 1) rawTwo ready 6 ∧
      Exec 2 program ((implementation 2 1).prepare (.enqueue v) ready) y n ∧
      Exec 2 program ((implementation 2 1).prepare .dequeue y) z m ∧
      (implementation 2 1).decode .dequeue z.regs = some (some v) ∧
      QueueRep 2 1 1 [] z ∧ 6 + (n + 1) + (m + 1) ≤ 6 + (6 * Backend.factor family + 11) ∧
      z.mem 4 = 0 := by
  let ready := initialized 1 1 rawTwo
  have hr : Rep 2 1 1 [] [] ready := initialized_rep rawTwo_bounded (by decide)
  obtain ⟨y, n, he, hn, hry, hmy⟩ := execute_enqueue (by decide) hr (by decide) hv
  obtain ⟨z, m, hd, hm, hrz, ha, hmz⟩ := execute_dequeue (by decide) hry
  have hm' : m + 1 ≤ Backend.factor family * 4 + 6 := hm
  have houtside : 4 ∉ (Block.mk 1 (2 * 1)).footprint := by decide
  have hsentinel : z.mem 4 = 0 := (hmz 4 houtside).trans ((hmy 4 houtside).trans rfl)
  refine ⟨ready, y, z, n, m, (initialize_exec rawTwo_bounded (by decide)).1,
    he, hd, ha, ⟨[], [], rfl, hrz⟩, ?_, hsentinel⟩
  omega

-- Some-zero and the maximum word use the same program and persistent register file.
example := roundTrip_native 0 (fits_zero 2)
example := roundTrip_native 3 (by decide)

/-- A larger old two-array region, with arbitrary dirty unused cells. -/
def rawThree : Data registers := ⟨fun _ => 7, fun _ => 5⟩

theorem rawThree_bounded : rawThree.Bounded 3 :=
  ⟨fun _ => (by decide : Fits 3 7), fun _ => (by decide : Fits 3 5)⟩

-- Five actual calls carry metadata through a two-iteration reversal, an immediate pop and
-- the empty case. The values zero and maximum7 remain distinct from the empty observation.
example : ∃ ready a b c d e n0 n1 n2 n3 n4,
    Exec 3 (initializeCode 1 2) rawThree ready 6 ∧
      Exec 3 program ((implementation 3 2).prepare (.enqueue 0) ready) a n0 ∧
      Exec 3 program ((implementation 3 2).prepare (.enqueue 7) a) b n1 ∧
      Exec 3 program ((implementation 3 2).prepare .dequeue b) c n2 ∧
      Exec 3 program ((implementation 3 2).prepare .dequeue c) d n3 ∧
      Exec 3 program ((implementation 3 2).prepare .dequeue d) e n4 ∧
      (implementation 3 2).decode .dequeue c.regs = some (some 0) ∧
      (implementation 3 2).decode .dequeue d.regs = some (some 7) ∧
      (implementation 3 2).decode .dequeue e.regs = some none ∧ QueueRep 3 1 2 [] e := by
  let ready := initialized 1 2 rawThree
  have hr : Rep 3 1 2 [] [] ready := initialized_rep rawThree_bounded (by decide)
  obtain ⟨a, n0, h0, _, hra, _⟩ := execute_enqueue (v := 0) (by decide) hr (by decide) (by decide)
  obtain ⟨b, n1, h1, _, hrb, _⟩ := execute_enqueue (v := 7) (by decide) hra (by decide) (by decide)
  obtain ⟨c, n2, h2, _, hrc, hc, _⟩ := execute_dequeue (by decide) hrb
  obtain ⟨d, n3, h3, _, hrd, hd, _⟩ := execute_dequeue (by decide) hrc
  obtain ⟨e, n4, h4, _, hre, he, _⟩ := execute_dequeue (by decide) hrd
  exact ⟨ready, a, b, c, d, e, n0, n1, n2, n3, n4,
    (initialize_exec rawThree_bounded (by decide)).1,
    h0, h1, h2, h3, h4, hc, hd, he, ⟨[], [], rfl, hre⟩⟩

/-- Capacity-zero entry is dirty in every register and every memory cell. -/
def rawOne : Data registers := ⟨fun _ => 1, fun _ => 1⟩

theorem rawOne_bounded : rawOne.Bounded 1 :=
  ⟨fun _ => (by decide : Fits 1 1), fun _ => (by decide : Fits 1 1)⟩

example : ∃ ready y n, Exec 1 (initializeCode 0 0) rawOne ready 6 ∧
      Exec 1 program ((implementation 1 0).prepare .dequeue ready) y n ∧
      n + 1 ≤ Backend.factor family + 6 ∧
      (implementation 1 0).decode .dequeue y.regs = some none ∧
      QueueRep 1 0 0 [] y ∧ y.mem = rawOne.mem := by
  let ready := initialized 0 0 rawOne
  have hr : Rep 1 0 0 [] [] ready := initialized_rep rawOne_bounded (by decide)
  obtain ⟨y, n, he, hn, hry, ha, hm⟩ := execute_dequeue (by decide) hr
  have hn' : n + 1 ≤ Backend.factor family + 6 := by
    change n + 1 ≤ Backend.factor family * 1 + 6 at hn
    simpa only [Nat.mul_one] using hn
  refine ⟨ready, y, n, (initialize_exec rawOne_bounded (by decide)).1,
    he, hn', ha, ⟨[], [], rfl, hry⟩, ?_⟩
  funext a
  exact hm a (by simp [footprint, Block.footprint])

end CslibFrontierTests.QueueRegisterExecution
