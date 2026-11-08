/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterCorrectness

/-! Logical clients of the physical-array source proofs. Native prepared-body regressions
are in `QueueRegisterMethods`; raw initialization and persistent dispatch are separate. -/

@[expose] public section

namespace CslibFrontierTests.QueueRegisterCorrectness

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

/-- Two rear entries are stored in physical stack order in otherwise dirty memory. -/
def rear : Memory.State := ⟨fun a => if a = 3 then 0 else if a = 4 then 7 else 5, 5⟩

theorem rear_bounded : Memory.WellFormed 3 rear := by
  refine ⟨by decide, fun a => ?_⟩
  dsimp only [rear]
  split <;> (try split) <;> decide

-- Existing pairStep, not a separate FIFO specification, supplies the actual dequeue result.
example :
    (Memory.spec 0).clientResult rear (dequeue ![0, 2, 1, 2, 0]) = ((1, 0), some 0) ∧
      Block.HoldsList 1 [7] ((Memory.spec 0).clientState rear
        (dequeue ![0, 2, 1, 2, 0])).mem := by
  have h := dequeue_contents (d := ![0, 2, 1, 2, 0]) [] [7, 0] rear
    rear_bounded rfl rfl (by decide) (by decide) (Block.holdsList_nil _ _)
    (by intro i; fin_cases i <;> rfl)
  exact ⟨h.1, h.2.1⟩

-- A nonempty front and a live rear are both retained correctly after the front pop.
example :
    (Memory.spec 0).clientResult rear (dequeue ![1, 1, 1, 2, 0]) = ((0, 1), some 5) ∧
      Block.HoldsList 3 [0] ((Memory.spec 0).clientState rear
        (dequeue ![1, 1, 1, 2, 0])).mem := by
  have h := dequeue_contents (d := ![1, 1, 1, 2, 0]) [5] [0] rear
    rear_bounded rfl rfl (by decide) (by decide)
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  exact ⟨h.1, h.2.2⟩

-- Enqueue preserves the existing front and extends the rear in physical stack order.
example : Block.HoldsList 3 [0, 7]
    ((Memory.spec 0).clientState ⟨fun _ => 0, 5⟩ (enqueue ![0, 1, 1, 2, 7])).mem := by
  have h := enqueue_contents (d := ![0, 1, 1, 2, 7]) [] [0] ⟨fun _ => 0, 5⟩
    rfl rfl (by decide) (Block.holdsList_nil _ _) (by intro i; fin_cases i; rfl)
  exact h.2.2

/-- A source client threads the returned count values, with no hidden memory count cells. -/
def cycle (v : ℕ) : Memory.Prog (Option ℕ) := do
  let m ← enqueue ![0, 0, 1, 1, v]
  let r ← dequeue ![m.1, m.2, 1, 1, v]
  pure r.2

example : (Memory.spec 2).clientResult ⟨fun _ => 1, 3⟩ (cycle 3) = some 3 := rfl
example : memoryCost (cycle 3) ⟨fun _ => 1, 3⟩ = 4 := rfl
example : ((Memory.spec 2).clientState ⟨fun _ => 1, 3⟩ (cycle 3)).mem 4 = 1 := rfl

-- Full and overflowing enqueues remain rejected; zero-capacity dequeue remains admitted.
example : ¬ enqueueDomain 2 ![0, 1, 1, 1, 3] ⟨fun _ => 3, 3⟩ := by unfold enqueueDomain; decide
example : ¬ enqueueDomain 2 ![0, 0, 1, 1, 4] ⟨fun _ => 3, 3⟩ := by unfold enqueueDomain; decide
example : transferDomain 1 ![0, 0, 0, 0, 1] ⟨fun _ => 1, 0⟩ := by unfold transferDomain; decide

end CslibFrontierTests.QueueRegisterCorrectness
