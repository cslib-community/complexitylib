/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (uniform typed-label queue method regressions)

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueMethod
import Complexity.Computability.WordRAM.Realization.Witness

/-!
# One native code for runtime queue operations and layouts

These clients share one selected global method emitter. They vary the operation, payload and
both layout base addresses, exercise immediate/transfer/empty dequeue, and retain an inaccessible
memory cell and a live caller control register. Label coordinates include the operation itself;
no result or payload is supplied by free host computation.
-/

public section

namespace ComplexityTests.WordRAMMemoryQueueMethod

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open MemoryQueueMethod

private def front (b : ℕ) : Stack.Memory.Layout := ⟨⟨b, 1⟩, ⟨b + 1, 2⟩⟩
private def rear (b : ℕ) : Stack.Memory.Layout := ⟨⟨b + 3, 1⟩, ⟨b + 4, 2⟩⟩
private def state (b nf nr v : ℕ) : Memory.State :=
  ⟨fun a => if a = b then nf else if a = b + 1 then v else if a = b + 3 then nr else
    if a = b + 4 then 15 else if a = b + 5 then 7 else 9, b + 6⟩

private theorem front_valid (b : ℕ) : (front b).Valid 4 2 := by
  refine ⟨rfl, ?_, rfl, by decide⟩
  change ¬(b + 1 ≤ b ∧ b < b + 1 + 2)
  omega

private theorem rear_valid (b : ℕ) : (rear b).Valid 4 2 := by
  refine ⟨rfl, ?_, rfl, by decide⟩
  change ¬(b + 4 ≤ b + 3 ∧ b + 3 < b + 4 + 2)
  omega

private theorem state_wf {b nf nr v : ℕ} (hb : b ≤ 6)
    (hf : Fits 4 nf) (hr : Fits 4 nr) (hv : Fits 4 v) : Memory.WellFormed 4 (state b nf nr v) := by
  refine ⟨?_, fun a => ?_⟩
  · change b + 6 < 2 ^ 4
    omega
  · change Fits 4 (if a = b then nf else if a = b + 1 then v else if a = b + 3 then nr else
      if a = b + 4 then 15 else if a = b + 5 then 7 else 9)
    split_ifs <;> first | assumption | decide

private theorem inv_front {b nf nr v : ℕ} (h : nf ≤ 2) :
    Stack.Memory.Inv (front b) (state b nf nr v) := by
  refine ⟨?_, ?_, ?_⟩
  · change b + 1 ≤ b + 6; omega
  · change b + 1 + 2 ≤ b + 6; omega
  · simpa [front, state] using h

private theorem inv_rear {b nf nr v : ℕ} (h : nr ≤ 2) :
    Stack.Memory.Inv (rear b) (state b nf nr v) := by
  refine ⟨?_, ?_, ?_⟩
  · change b + 3 + 1 ≤ b + 6; omega
  · change b + 4 + 2 ≤ b + 6; omega
  · simpa [rear, state, show b + 3 ≠ b from by omega,
      show b + 3 ≠ b + 1 from by omega] using h

private def immediate := state 0 1 1 1
private def fallback := state 0 0 2 9
private def empty := state 0 0 0 9
private def shiftedEmpty := state 6 0 0 9

private theorem safe_immediate : methodSafe 4 ((front 0, rear 0), .dequeue) immediate := by
  change (front 0).Valid 4 2 ∧ Stack.Memory.Inv (front 0) immediate ∧ True
  exact ⟨front_valid 0, inv_front (by decide), trivial⟩

private theorem safe_fallback : methodSafe 4 ((front 0, rear 0), .dequeue) fallback := by
  have hw : Memory.WellFormed 4 fallback := state_wf (by decide) (by decide) (by decide) (by decide)
  have hF : Stack.Memory.Inv (front 0) fallback := inv_front (by decide)
  have hR : Stack.Memory.Inv (rear 0) fallback := inv_rear (by decide)
  have hd : Disjoint (front 0).footprint (rear 0).footprint := by decide
  have ht := MemoryQueue.transfer_invariant (n := 2) (front_valid 0) (rear_valid 0) hd hw hF hR
    rfl (by decide)
  change (front 0).Valid 4 2 ∧ Stack.Memory.Inv (front 0) fallback ∧
    iterationSafe MemoryQueue.transferBody MemoryQueue.transferSafe 4 (front 0, rear 0) 2 true
      fallback ∧ Stack.Memory.Inv (front 0) ((Memory.spec 0).clientState fallback
        (link (Stack.Memory.pairMethods (front 0) (rear 0) 0 0) (Queue.transfer 2)))
  refine ⟨front_valid 0, hF, ht.1, ?_⟩
  rw [MemoryQueue.transfer_eq_iterate]
  simpa only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind,
    StateTransitionSpec.runClient_pure, StateTransitionSpec.runClient_pure'] using ht.2.2.1

private theorem safe_empty : methodSafe 4 ((front 0, rear 0), .dequeue) empty := by
  change (front 0).Valid 4 2 ∧ Stack.Memory.Inv (front 0) empty ∧
    True ∧ Stack.Memory.Inv (front 0) empty
  exact ⟨front_valid 0, inv_front (by decide), trivial, inv_front (by decide)⟩

private theorem safe_shifted : methodSafe 4 ((front 6, rear 6), .enqueue 15) shiftedEmpty := by
  change (rear 6).Valid 4 2 ∧ Stack.Memory.Inv (rear 6) shiftedEmpty ∧ 0 < 2
  exact ⟨rear_valid 6, inv_rear (by decide), by decide⟩

/-- Typed labels distinguish enqueue payloads from dequeue results even when values coincide. -/
theorem label_enqueue_ne_dequeue : labelWords ⟨.enqueue 1, ()⟩ ≠
    labelWords ⟨.dequeue, some 1⟩ := by decide

private noncomputable def registers : ℕ := realizes_method.scratchSize + 22
private noncomputable def src (i : Fin 11) : Fin registers :=
  ⟨i.val, by have := i.isLt; unfold registers; omega⟩
private noncomputable def frontier : Fin registers := ⟨11, by unfold registers; omega⟩
private noncomputable def control : Fin registers := ⟨12, by unfold registers; omega⟩
private noncomputable def scratch (i : Fin (4 + realizes_method.scratchSize + 1)) : Fin registers :=
  ⟨16 + i.val, by have := i.isLt; unfold registers; omega⟩
private noncomputable def code := realizes_method.code frontier src scratch
private noncomputable def out (i : Fin 4) :=
  scratch (Fin.castAdd (realizes_method.scratchSize + 1) i)

private noncomputable def data
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (s : Memory.State) :
    Data registers where
  regs i := if h : i.val < 11 then methodWords d ⟨i.val, h⟩
    else if i.val = 11 then s.frontier else if i.val = 12 then 9 else 0
  mem := s.mem

private theorem execution
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (s : Memory.State)
    (hw : Memory.WellFormed 4 s) (hwords : ∀ i, Fits 4 (methodWords d i))
    (hsafe : methodSafe 4 d s)
    (hvalid : (Memory.spec 4).ValidHistory s ((Memory.spec 4).clientHistory s (method d))) :
    ∃ y, ExecWithin 4 code (data d s) y
        (realizes_method.factor * (memoryCost (method d) s + methodWork d s + 1)) ∧
      memoryState frontier y = (Memory.spec 4).clientState s (method d) ∧
      (∀ i : Fin 4, y.regs (out i) =
        labelWords ((Memory.spec 4).clientResult s (method d)) i) ∧
      y.regs control = 9 := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change 16 + i.val = 16 + j.val at hh
    omega
  have hd (i : Fin 11) (j) : src i ≠ scratch j := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = 16 + j.val at hh
    omega
  have hf (j) : scratch j ≠ frontier := by
    intro h
    have hh := congrArg Fin.val h
    change 16 + j.val = 11 at hh
    omega
  have hs (i : Fin 11) : src i ≠ frontier := by
    intro h
    have hh := congrArg Fin.val h
    change i.val = 11 at hh
    omega
  have hb : (data d s).Bounded 4 := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    change Fits 4 (if h : i.val < 11 then methodWords d ⟨i.val, h⟩
      else if i.val = 11 then s.frontier else if i.val = 12 then 9 else 0)
    split
    · exact hwords _
    · split
      · exact hw.frontier_fits
      · split <;> decide
  have hin : (data d s).regs ∘ src = methodWords d := by
    funext i
    simp [data, src]
  have hm : memoryState frontier (data d s) = s := by
    apply Memory.State.ext
    · rfl
    · simp [memoryState, data, frontier]
  obtain ⟨y, hy, hmy, hout, hyframe⟩ :=
    (realizes_method.code_spec frontier src scratch hi hd hf hs).2
      4 d (data d s) hb hin (hm ▸ hsafe) (hm ▸ hvalid)
  rw [hm] at hy hmy hout
  refine ⟨y, hy, hmy, hout, ?_⟩
  rw [hyframe control (by simp [control, frontier]) (fun j => ?_)]
  · simp [data, control]
  · intro h
    have hh := congrArg Fin.val h
    change 16 + j.val = 12 at hh
    omega

-- Runtime enqueue and shifted layout bases use the very same code as every dequeue below.
example : ∃ y, ExecWithin 4 code (data ((front 6, rear 6), .enqueue 15) shiftedEmpty) y
      (realizes_method.factor * 25) ∧
    (∀ i : Fin 4, y.regs (out i) = ![0, 15, 0, 0] i) ∧
    y.mem 9 = 1 ∧ y.mem 10 = 15 ∧ y.mem 100 = 9 ∧ y.regs control = 9 := by
  obtain ⟨y, he, hm, hout, hc⟩ := execution ((front 6, rear 6), .enqueue 15) shiftedEmpty
    (state_wf (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i <;> decide) safe_shifted (by decide)
  refine ⟨y, he, hout, ?_, ?_, ?_, hc⟩
  · exact congrArg (fun s : Memory.State => s.mem 9) hm
  · exact congrArg (fun s : Memory.State => s.mem 10) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

example : ∃ y, ExecWithin 4 code (data ((front 0, rear 0), .dequeue) immediate) y
      (realizes_method.factor * 43) ∧
    (∀ i : Fin 4, y.regs (out i) = ![1, 0, 1, 1] i) ∧
    y.mem 0 = 0 ∧ y.mem 3 = 1 ∧ y.mem 100 = 9 ∧ y.regs control = 9 := by
  obtain ⟨y, he, hm, hout, hc⟩ := execution ((front 0, rear 0), .dequeue) immediate
    (state_wf (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i <;> decide) safe_immediate (by decide)
  refine ⟨y, he, hout, ?_, ?_, ?_, hc⟩
  · exact congrArg (fun s : Memory.State => s.mem 0) hm
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

example : ∃ y, ExecWithin 4 code (data ((front 0, rear 0), .dequeue) fallback) y
      (realizes_method.factor * 178) ∧
    (∀ i : Fin 4, y.regs (out i) = ![1, 0, 1, 15] i) ∧
    y.mem 0 = 1 ∧ y.mem 3 = 0 ∧ y.mem 100 = 9 ∧ y.regs control = 9 := by
  obtain ⟨y, he, hm, hout, hc⟩ := execution ((front 0, rear 0), .dequeue) fallback
    (state_wf (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i <;> decide) safe_fallback (by decide)
  refine ⟨y, he, hout, ?_, ?_, ?_, hc⟩
  · exact congrArg (fun s : Memory.State => s.mem 0) hm
  · exact congrArg (fun s : Memory.State => s.mem 3) hm
  · exact congrArg (fun s : Memory.State => s.mem 100) hm

example : ∃ y, ExecWithin 4 code (data ((front 0, rear 0), .dequeue) empty) y
      (realizes_method.factor * 84) ∧
    (∀ i : Fin 4, y.regs (out i) = ![1, 0, 0, 0] i) ∧
    y.mem 100 = 9 ∧ y.regs control = 9 := by
  obtain ⟨y, he, hm, hout, hc⟩ := execution ((front 0, rear 0), .dequeue) empty
    (state_wf (by decide) (by decide) (by decide) (by decide))
    (by intro i; fin_cases i <;> decide) safe_empty (by decide)
  exact ⟨y, he, hout, congrArg (fun s : Memory.State => s.mem 100) hm, hc⟩

end ComplexityTests.WordRAMMemoryQueueMethod
