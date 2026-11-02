/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueDispatch
import Complexity.Computability.WordRAM.Realization.Witness

/-! One fixed native dequeue body handles an immediate payload equal to one, a runtime-sized
transfer returning the maximum word, and an empty queue. The first case distinguishes the
presence tag from a coincidentally equal payload. All cases retain inaccessible memory. -/

namespace ComplexityTests.WordRAMMemoryQueueDispatch

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open MemoryQueueDispatch

private def front : Stack.Memory.Layout := ⟨⟨0, 1⟩, ⟨1, 2⟩⟩
private def rear : Stack.Memory.Layout := ⟨⟨3, 1⟩, ⟨4, 2⟩⟩
private def state (nf nr v : ℕ) : Memory.State :=
  ⟨fun a => if a = 0 then nf else if a = 1 then v else if a = 3 then nr else
    if a = 4 then 15 else if a = 5 then 7 else 9, 6⟩
private def immediate := state 1 1 1
private def fallback := state 0 2 9
private def empty := state 0 0 9

private theorem front_valid : front.Valid 4 2 := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> norm_num [front, Block.Owns, Fits]

private theorem rear_valid : rear.Valid 4 2 := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> norm_num [rear, Block.Owns, Fits]

private theorem state_wf {nf nr v : ℕ} (hf : Fits 4 nf) (hr : Fits 4 nr) (hv : Fits 4 v) :
    Memory.WellFormed 4 (state nf nr v) := by
  refine ⟨by change Fits 4 6; decide, fun a => ?_⟩
  change Fits 4 (if a = 0 then nf else if a = 1 then v else if a = 3 then nr else
    if a = 4 then 15 else if a = 5 then 7 else 9)
  split_ifs <;> first | assumption | decide

private theorem inv_front {nf nr v : ℕ} (h : nf ≤ 2) :
    Stack.Memory.Inv front (state nf nr v) := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 + 1 ≤ 6; omega
  · change 1 + 2 ≤ 6; omega
  · exact h

private theorem inv_rear {nf nr v : ℕ} (h : nr ≤ 2) :
    Stack.Memory.Inv rear (state nf nr v) := by
  refine ⟨?_, ?_, ?_⟩
  · change 3 + 1 ≤ 6; omega
  · change 4 + 2 ≤ 6; omega
  · exact h

private theorem safe_immediate : dequeueSafe 4 (front, rear) immediate := by
  change front.Valid 4 2 ∧ Stack.Memory.Inv front immediate ∧ True
  exact ⟨front_valid, inv_front (by decide), trivial⟩

private theorem safe_fallback : dequeueSafe 4 (front, rear) fallback := by
  have hw : Memory.WellFormed 4 fallback := state_wf (by decide) (by decide) (by decide)
  have hF : Stack.Memory.Inv front fallback := inv_front (by decide)
  have hR : Stack.Memory.Inv rear fallback := inv_rear (by decide)
  have hd : Disjoint front.footprint rear.footprint := by decide
  have ht := MemoryQueue.transfer_invariant (n := 2) front_valid rear_valid hd hw hF hR
    rfl (by decide)
  change front.Valid 4 2 ∧ Stack.Memory.Inv front fallback ∧
    iterationSafe MemoryQueue.transferBody MemoryQueue.transferSafe 4 (front, rear) 2 true
      fallback ∧ Stack.Memory.Inv front ((Memory.spec 0).clientState fallback
        (link (Stack.Memory.pairMethods front rear 0 0) (Queue.transfer 2)))
  refine ⟨front_valid, hF, ht.1, ?_⟩
  rw [MemoryQueue.transfer_eq_iterate]
  simpa only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind,
    StateTransitionSpec.runClient_pure, StateTransitionSpec.runClient_pure'] using ht.2.2.1

private theorem safe_empty : dequeueSafe 4 (front, rear) empty := by
  change front.Valid 4 2 ∧ Stack.Memory.Inv front empty ∧ True ∧ Stack.Memory.Inv front empty
  exact ⟨front_valid, inv_front (by decide), trivial, inv_front (by decide)⟩

private theorem realization :
    Realizes .exact (fun L : Stack.Memory.Layout × Stack.Memory.Layout =>
      Queue.Memory.memMethods L.1 L.2 4 2 .dequeue)
      MemoryQueue.layoutWords optionWords dequeueSafe dequeueWork := realizes_dequeue 4 2

private noncomputable def registers : ℕ := realization.scratchSize + 12
private noncomputable def src (i : Fin 8) : Fin registers :=
  ⟨i.val, by have := i.isLt; unfold registers; omega⟩
private noncomputable def frontier : Fin registers := ⟨8, by unfold registers; omega⟩
private noncomputable def scratch (i : Fin (2 + realization.scratchSize + 1)) : Fin registers :=
  ⟨9 + i.val, by have := i.isLt; unfold registers; omega⟩
private noncomputable def code := realization.code frontier src scratch

private noncomputable def data (s : Memory.State) : Data registers where
  regs i := if h : i.val < 8 then MemoryQueue.layoutWords (front, rear) ⟨i.val, h⟩
    else if i.val = 8 then 6 else 0
  mem := s.mem

private theorem encoded_fits (i : Fin 8) : Fits 4 (MemoryQueue.layoutWords (front, rear) i) := by
  fin_cases i <;> decide

private theorem execution (s : Memory.State) (hw : Memory.WellFormed 4 s) (hf : s.frontier = 6)
    (hsafe : dequeueSafe 4 (front, rear) s)
    (hvalid : (Memory.spec 4).ValidHistory s ((Memory.spec 4).clientHistory s
      (Queue.Memory.memMethods front rear 4 2 .dequeue))) :
    ∃ y, ExecWithin 4 code (data s) y
        (realization.factor * (memoryCost (Queue.Memory.memMethods front rear 4 2 .dequeue) s +
          dequeueWork (front, rear) s + 1)) ∧
      memoryState frontier y = (Memory.spec 4).clientState s
        (Queue.Memory.memMethods front rear 4 2 .dequeue) ∧
      ∀ i : Fin 2, y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) i)) =
        optionWords ((Memory.spec 4).clientResult s
          (Queue.Memory.memMethods front rear 4 2 .dequeue)) i := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    change 9 + i.val = 9 + j.val at this
    omega
  have hd (i : Fin 8) (j) : src i ≠ scratch j := by
    intro h
    have := congrArg Fin.val h
    change i.val = 9 + j.val at this
    have := i.isLt
    omega
  have hfr (j) : scratch j ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    change 9 + j.val = 8 at this
    omega
  have hsrc (i : Fin 8) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    change i.val = 8 at this
    have := i.isLt
    omega
  have hb : (data s).Bounded 4 := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    change Fits 4 (if h : i.val < 8 then MemoryQueue.layoutWords (front, rear) ⟨i.val, h⟩
      else if i.val = 8 then 6 else 0)
    split
    · exact encoded_fits _
    · split <;> norm_num [Fits]
  have hin : (data s).regs ∘ src = MemoryQueue.layoutWords (front, rear) := by
    funext i
    simp [data, src]
  have hm : memoryState frontier (data s) = s := by
    apply Memory.State.ext
    · rfl
    · simp [memoryState, data, frontier, hf]
  obtain ⟨y, he, hmem, hout, _⟩ := (realization.code_spec frontier src scratch hi hd hfr hsrc).2
    4 (front, rear) (data s) hb hin (hm ▸ hsafe) (hm ▸ hvalid)
  rw [hm] at he hmem hout
  exact ⟨y, he, hmem, hout⟩

-- Payload one must take the immediate path, although its tag and payload are both one.
example : ∃ y, ExecWithin 4 code (data immediate) y (realization.factor * 32) ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 0)) = 1 ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 1)) = 1 ∧
    y.mem 0 = 0 ∧ y.mem 3 = 1 ∧ y.mem 100 = 9 := by
  obtain ⟨y, he, hm, hout⟩ := execution immediate
    (state_wf (by decide) (by decide) (by decide)) rfl safe_immediate (by decide)
  refine ⟨y, he, hout 0, hout 1, ?_, ?_, ?_⟩
  · exact congrArg (fun s : Memory.State => s.mem 0) hm
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

-- The same code reads rear fuel two, executes the certified transfer, and returns word fifteen.
example : ∃ y, ExecWithin 4 code (data fallback) y (realization.factor * 167) ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 0)) = 1 ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 1)) = 15 ∧
    y.mem 0 = 1 ∧ y.mem 3 = 0 ∧ y.mem 100 = 9 := by
  obtain ⟨y, he, hm, hout⟩ := execution fallback
    (state_wf (by decide) (by decide) (by decide)) rfl safe_fallback (by decide)
  refine ⟨y, he, hout 0, hout 1, ?_, ?_, ?_⟩
  · exact congrArg (fun s : Memory.State => s.mem 0) hm
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

-- Zero runtime fuel and the empty final pop return none with the same selected emitter.
example : ∃ y, ExecWithin 4 code (data empty) y (realization.factor * 73) ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 0)) = 0 ∧
    y.regs (scratch (Fin.castAdd (realization.scratchSize + 1) 1)) = 0 ∧ y.mem 100 = 9 := by
  obtain ⟨y, he, hm, hout⟩ := execution empty
    (state_wf (by decide) (by decide) (by decide)) rfl safe_empty (by decide)
  exact ⟨y, he, hout 0, hout 1, congrArg (fun s : Memory.State => s.mem 100) hm⟩

end ComplexityTests.WordRAMMemoryQueueDispatch
