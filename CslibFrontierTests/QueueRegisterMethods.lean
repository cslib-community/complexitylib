/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterProgram

/-!
The production finite family is fixed before every runtime count, base, capacity, width and memory.
These are prepared-body executions. A later fixed native dispatcher must pay for tag selection,
metadata commit and the final halt; `Backend.install` is explicit here and is not a raw loader.
-/

@[expose] public section

namespace CslibFrontierTests.QueueRegisterMethods

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Queue.WordRAM.RegisterMetadata
open Cslib.DataStructure.Queue.WordRAM

noncomputable def result (b : Bool) (i : Fin (family b).l) :
    Fin (Backend.registers family) :=
  Backend.tmp family b (Fin.castAdd ((family b).realizes.scratchSize + 1) i)

/-- Enqueue's whole source memory and its two count words are realized by the fixed body. -/
theorem native_enqueue {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (hwords : ∀ i, Fits w (d i))
    (h : enqueueDomain w d s) :
    ∃ y n, Exec w (Backend.code family false)
        (Backend.install family false d (Backend.data family s)) y n ∧
      n ≤ Backend.factor family * 2 ∧
      y.mem = Function.update s.mem (d 2 + d 3 + d 1) (d 4) ∧
      ∀ i, y.regs (result false i) = counts (d 0, d 1 + 1) i := by
  obtain ⟨y, n, he, hn, hm, hout, _⟩ := Backend.exists_exec family false d
    (Backend.bounded_data family hw) hwords
    (by simpa only [Backend.memoryState_data] using h)
    (by simpa only [Backend.memoryState_data] using valid_enqueue h)
  rw [Backend.memoryState_data, memoryCost_enqueue] at hn
  have hmem := congrArg Memory.State.mem hm
  rw [Backend.memoryState_data, clientState_width w] at hmem
  rw [Backend.memoryState_data, clientResult_width w] at hout
  exact ⟨y, n, he, hn, hmem, hout⟩

/-- The same dequeue body realizes empty, immediate and transferred option answers. -/
theorem native_dequeue {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (hwords : ∀ i, Fits w (d i))
    (h : transferDomain w d s) :
    ∃ y n, Exec w (Backend.code family true)
        (Backend.install family true d (Backend.data family s)) y n ∧
      n ≤ Backend.factor family *
        ((if d 0 = 0 then 2 * d 1 + (if d 1 = 0 then 0 else 1) else 1) + 1) ∧
      y.mem = ((Memory.spec 0).clientState s (dequeue d)).mem ∧
      ∀ i, y.regs (result true i) =
        appendWords counts optionWords ((Memory.spec 0).clientResult s (dequeue d)) i := by
  have hi := dequeue_invariant hw h
  obtain ⟨y, n, he, hn, hm, hout, _⟩ := Backend.exists_exec family true d
    (Backend.bounded_data family hw) hwords
    (by simpa only [Backend.memoryState_data] using h)
    (by simpa only [Backend.memoryState_data] using hi.1)
  rw [Backend.memoryState_data, hi.2.2.2.2.1] at hn
  have hmem := congrArg Memory.State.mem hm
  rw [Backend.memoryState_data, clientState_width w] at hmem
  rw [Backend.memoryState_data, clientResult_width w] at hout
  exact ⟨y, n, he, hn, hmem, hout⟩

-- The old decisive small-width domain admits a maximum-word enqueue with only two cells.
example : ∃ y n, Exec 2 (Backend.code family false)
      (Backend.install family false ![0, 0, 1, 1, 3]
        (Backend.data family ⟨fun _ => 1, 3⟩)) y n ∧
    n ≤ Backend.factor family * 2 ∧ y.mem 2 = 3 ∧ y.mem 4 = 1 ∧
      y.regs (result false 0) = 0 ∧ y.regs (result false 1) = 1 := by
  obtain ⟨y, n, he, hn, hm, ho⟩ := native_enqueue (w := 2)
    (d := ![0, 0, 1, 1, 3]) (s := ⟨fun _ => 1, 3⟩)
    ⟨by decide, fun _ => (by decide : Fits 2 1)⟩ (fun i => by fin_cases i <;> decide)
    (by change 0 + 0 < 1 ∧ 1 + 2 * 1 ≤ 3 ∧ Fits 2 3; decide)
  exact ⟨y, n, he, hn, hm ▸ rfl, hm ▸ rfl, ho 0, ho 1⟩

/-- A dirty two-element rear contains zero and the maximum three-bit word. -/
def dirty : Memory.State := ⟨fun a => if a = 3 then 0 else if a = 4 then 7 else 5, 5⟩

theorem dirty_bounded : Memory.WellFormed 3 dirty := by
  refine ⟨by decide, fun a => ?_⟩
  dsimp only [dirty]
  split <;> (try split) <;> decide

-- The actual fallback returns the oldest value zero, with a separate present tag.
example : ∃ y n, Exec 3 (Backend.code family true)
      (Backend.install family true ![0, 2, 1, 2, 7]
        (Backend.data family dirty)) y n ∧
    n ≤ Backend.factor family * 6 ∧ y.mem 6 = 5 ∧
      y.regs (result true 0) = 1 ∧ y.regs (result true 1) = 0 ∧
      y.regs (result true 2) = 1 ∧ y.regs (result true 3) = 0 := by
  obtain ⟨y, n, he, hn, hm, ho⟩ := native_dequeue (d := ![0, 2, 1, 2, 7])
    dirty_bounded (fun i => by fin_cases i <;> decide)
    (by change 0 + 2 ≤ 2 ∧ 1 + 2 * 2 ≤ 5; decide)
  exact ⟨y, n, he, hn, hm ▸ rfl, ho 0, ho 1, ho 2, ho 3⟩

-- A nonempty front returns a maximum word without touching any memory cell.
example : ∃ y n, Exec 2 (Backend.code family true)
      (Backend.install family true ![1, 0, 1, 1, 0]
        (Backend.data family ⟨fun _ => 3, 3⟩)) y n ∧
    n ≤ Backend.factor family * 2 ∧ y.mem = (fun _ => 3) ∧
      y.regs (result true 0) = 0 ∧ y.regs (result true 1) = 0 ∧
      y.regs (result true 2) = 1 ∧ y.regs (result true 3) = 3 := by
  obtain ⟨y, n, he, hn, hm, ho⟩ := native_dequeue (w := 2)
    (d := ![1, 0, 1, 1, 0]) (s := ⟨fun _ => 3, 3⟩)
    ⟨by decide, fun _ => (by decide : Fits 2 3)⟩ (fun i => by fin_cases i <;> decide)
    (by change 1 + 0 ≤ 1 ∧ 1 + 2 * 1 ≤ 3; decide)
  exact ⟨y, n, he, hn, hm, ho 0, ho 1, ho 2, ho 3⟩

-- The same dequeue body handles capacity zero on arbitrary dirty bounded memory.
example : ∃ y n, Exec 1 (Backend.code family true)
      (Backend.install family true ![0, 0, 0, 0, 1]
        (Backend.data family ⟨fun _ => 1, 0⟩)) y n ∧
    n ≤ Backend.factor family ∧ y.mem = (fun _ => 1) ∧
      y.regs (result true 0) = 0 ∧ y.regs (result true 1) = 0 ∧
      y.regs (result true 2) = 0 ∧ y.regs (result true 3) = 0 := by
  obtain ⟨y, n, he, hn, hm, ho⟩ := native_dequeue (w := 1)
    (d := ![0, 0, 0, 0, 1]) (s := ⟨fun _ => 1, 0⟩)
    ⟨by decide, fun _ => (by decide : Fits 1 1)⟩ (fun i => by fin_cases i <;> decide)
    (by change 0 + 0 ≤ 0 ∧ 0 + 2 * 0 ≤ 0; decide)
  exact ⟨y, n, he, by simpa using hn, hm, ho 0, ho 1, ho 2, ho 3⟩

end CslibFrontierTests.QueueRegisterMethods
