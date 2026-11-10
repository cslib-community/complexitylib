/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterTransfer
public import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
One standard-basis body serves all prepared transfer inputs below. Argument installation is
explicit in the entry state; these are body executions, not an uncharged raw initializer or a
stateful `Backend.implementation`. The separate metadata feasibility test pays its initializer.
-/

@[expose] public section

namespace CslibFrontierTests.QueueRegisterTransfer

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure

open Cslib.DataStructure.Queue.WordRAM.RegisterMetadata

/-- The same globally fixed certificate family is used by every width/layout/value case. -/
noncomputable abbrev certificates (_ : Unit) : Certificate .standard :=
  Certificate.ofRealizes realizes_transfer_standard

noncomputable def result (i : Fin 2) : Fin (Backend.registers certificates) :=
  Backend.tmp certificates () (Fin.castAdd ((certificates ()).realizes.scratchSize + 1) i)

theorem native_body {w : ℕ} {d : Input} {s : Memory.State}
    (hw : Memory.WellFormed w s) (hwords : ∀ i, Fits w (d i))
    (h : transferDomain w d s) :
    ∃ y n, Exec w (Backend.code certificates ())
        (Backend.install certificates () d (Backend.data certificates s)) y n ∧
      n ≤ Backend.factor certificates * (2 * d 1 + 1) ∧
      y.mem = ((Memory.spec w).clientState s (transfer d)).mem ∧
      y.regs (result 0) = d 0 + d 1 ∧ y.regs (result 1) = 0 := by
  have hi := transfer_invariant hw h
  obtain ⟨y, n, he, hn, hm, hout, _⟩ := Backend.exists_exec certificates () d
    (Backend.bounded_data certificates hw) hwords
    (by simpa only [certificates, Certificate.ofRealizes, Backend.memoryState_data] using h)
    (by simpa only [certificates, Certificate.ofRealizes, Backend.memoryState_data] using hi.1)
  dsimp only [certificates, Certificate.ofRealizes] at hn hm hout
  have hcost := hi.2.2.2.2.1
  change memoryCost (transfer d) s = 2 * d 1 at hcost
  have hresult : (Memory.spec w).clientResult s (transfer d) = (d 0 + d 1, 0) :=
    (clientResult_width w _ _).trans hi.2.2.1
  have h0 := hout (0 : Fin 2)
  have h1 := hout (1 : Fin 2)
  rw [Backend.memoryState_data, hresult] at h0 h1
  rw [Backend.memoryState_data, hcost] at hn
  have hmem := congrArg Memory.State.mem hm
  rw [Backend.memoryState_data] at hmem
  exact ⟨y, n, he, hn, hmem, h0, h1⟩

/-- Two iterations move a zero and the largest three-bit word through dirty physical arrays. -/
def two : Input := ![0, 2, 1, 2, 7]

def dirty : Memory.State := ⟨fun a => if a = 3 then 7 else if a = 4 then 0 else 5, 5⟩

theorem dirty_bounded : Memory.WellFormed 3 dirty := by
  refine ⟨by decide, fun a => ?_⟩
  dsimp only [dirty]
  split <;> (try split) <;> decide

example : (Memory.spec 3).clientResult dirty (transfer two) = (2, 0) := rfl
example : memoryCost (transfer two) dirty = 4 := rfl
example : let t := (Memory.spec 3).clientState dirty (transfer two)
    t.mem 1 = 0 ∧ t.mem 2 = 7 ∧ t.mem 3 = 7 ∧ t.mem 4 = 0 ∧ t.mem 6 = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example : Block.HoldsList 1 [0, 7]
    ((Memory.spec 3).clientState dirty (transfer two)).mem := by
  rw [clientState_width 3]
  exact transfer_contents (d := two) [0, 7] [] dirty rfl rfl (by decide)
    (fun i => Fin.elim0 i) (by intro i; fin_cases i <;> rfl)

example : ∃ y n, Exec 3 (Backend.code certificates ())
      (Backend.install certificates () two (Backend.data certificates dirty)) y n ∧
    n ≤ Backend.factor certificates * 5 ∧ y.mem 1 = 0 ∧ y.mem 2 = 7 ∧
      y.mem 6 = 5 ∧ y.regs (result 0) = 2 ∧ y.regs (result 1) = 0 := by
  obtain ⟨y, n, he, hn, hm, h0, h1⟩ := native_body (d := two) dirty_bounded
    (fun i => by fin_cases i <;> decide) (by change 0 + 2 ≤ 2 ∧ 1 + 2 * 2 ≤ 5; decide)
  refine ⟨y, n, he, hn, ?_, ?_, ?_, h0, h1⟩ <;> rw [hm] <;> rfl

-- The original small-width domain: base1/C1 fits without two extra count cells.
example : ∃ y n, Exec 2 (Backend.code certificates ())
      (Backend.install certificates () ![0, 1, 1, 1, 3]
        (Backend.data certificates ⟨fun _ => 3, 3⟩)) y n ∧
    n ≤ Backend.factor certificates * 3 ∧ y.regs (result 0) = 1 ∧
      y.regs (result 1) = 0 := by
  obtain ⟨y, n, he, hn, _, h0, h1⟩ := native_body (w := 2)
    (d := ![0, 1, 1, 1, 3]) (s := ⟨fun _ => 3, 3⟩)
    ⟨by decide, fun _ => (by decide : Fits 2 3)⟩ (fun i => by fin_cases i <;> decide)
    (by change 0 + 1 ≤ 1 ∧ 1 + 2 * 1 ≤ 3; decide)
  exact ⟨y, n, he, hn, h0, h1⟩

-- The same body exits with zero capacity, keeping every dirty memory cell.
example : ∃ y n, Exec 1 (Backend.code certificates ())
      (Backend.install certificates () ![0, 0, 0, 0, 1]
        (Backend.data certificates ⟨fun _ => 1, 0⟩)) y n ∧
    n ≤ Backend.factor certificates ∧ y.mem = (fun _ => 1) ∧
      y.regs (result 0) = 0 ∧ y.regs (result 1) = 0 := by
  obtain ⟨y, n, he, hn, hm, h0, h1⟩ := native_body (w := 1)
    (d := ![0, 0, 0, 0, 1]) (s := ⟨fun _ => 1, 0⟩)
    ⟨by decide, fun _ => (by decide : Fits 1 1)⟩ (fun i => by fin_cases i <;> decide)
    (by change 0 + 0 ≤ 0 ∧ 0 + 2 * 0 ≤ 0; decide)
  exact ⟨y, n, he, by simpa using hn, hm, h0, h1⟩

end CslibFrontierTests.QueueRegisterTransfer
