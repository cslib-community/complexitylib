/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryQueue
import Complexity.Computability.WordRAM.Realization.Witness

/-!
A native transfer consumes the actual two-stack queue's linked memory program. The rear holds
15 and 7 at word width four, including the maximum fitting payload. The selected code, register
bank and exchange constant precede all runtime words; the memory proof is the generic kernel's.
-/

namespace ComplexityTests.WordRAMRealizationQueue

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.MemoryQueue

private def front : Stack.Memory.Layout := ⟨⟨0, 1⟩, ⟨1, 2⟩⟩
private def rear : Stack.Memory.Layout := ⟨⟨3, 1⟩, ⟨4, 2⟩⟩
private def initial : Memory.State :=
  ⟨fun a => if a = 0 then 0 else if a = 3 then 2 else if a = 4 then 7 else
    if a = 5 then 15 else 9, 6⟩

private def afterOne : Memory.State :=
  ⟨Function.update (Function.update (Function.update initial.mem 3 1) 1 15) 0 1, 6⟩

private theorem safe : iterationSafe transferBody transferSafe 4 (front, rear) 2 true initial := by
  change transferSafe 4 ((front, rear), true) initial ∧
    transferSafe 4 ((front, rear), true) afterOne ∧ True
  refine ⟨?_, ?_, trivial⟩
  all_goals
    change rear.Valid 4 2 ∧ Stack.Memory.Inv rear _ ∧ front.Valid 4 2 ∧
      Stack.Memory.Inv front _ ∧ _ < 2 ∧ Fits 4 1
    refine ⟨⟨rfl, ?_, rfl, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨rfl, ?_, rfl, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      norm_num [front, rear, initial, afterOne, Block.Allocated, Block.Owns, Fits] <;> decide

private theorem valid : (Memory.spec 4).ValidHistory initial
    ((Memory.spec 4).clientHistory initial
      (link (Stack.Memory.pairMethods front rear 4 2) (Queue.transfer 2))) := by decide

private theorem encoded_fits : ∀ i,
    Fits 4 (transferWords layoutWords ((front, rear), 2) i) := by
  intro i
  fin_cases i <;> decide

private theorem mem_fits (a : ℕ) : Fits 4 (initial.mem a) := by
  simp only [initial]
  split_ifs <;> norm_num [Fits]

private theorem realization :
    Realizes .exact
      (fun d => link (Stack.Memory.pairMethods d.1.1 d.1.2 4 2) (Queue.transfer d.2))
      (transferWords layoutWords) (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => iterationSafe transferBody transferSafe w d.1 d.2 true s)
      (fun d _ => 40 * d.2 + 1) := realizes_source_transfer 4 2
private noncomputable def registers : ℕ := realization.scratchSize + 13
private noncomputable def src (i : Fin 11) : Fin registers :=
  ⟨i.val, by have := i.isLt; unfold registers; omega⟩
private noncomputable def frontier : Fin registers := ⟨11, by unfold registers; omega⟩
private noncomputable def scratch (i : Fin (0 + realization.scratchSize + 1)) : Fin registers :=
  ⟨12 + i.val, by have := i.isLt; unfold registers; omega⟩

private noncomputable def data : Data registers where
  regs i := if h : i.val < 11 then transferWords layoutWords ((front, rear), 2) ⟨i.val, h⟩
    else if i.val = 11 then 6 else 0
  mem := initial.mem

private theorem execution (x : Data registers) (hb : x.Bounded 4)
    (hin : x.regs ∘ src = transferWords layoutWords ((front, rear), 2))
    (hsafe : iterationSafe transferBody transferSafe 4 (front, rear) 2 true
      (memoryState frontier x))
    (hvalid : (Memory.spec 4).ValidHistory (memoryState frontier x)
      ((Memory.spec 4).clientHistory (memoryState frontier x)
        (link (Stack.Memory.pairMethods front rear 4 2) (Queue.transfer 2)))) :
    ∃ y, ExecWithin 4 (realization.code frontier src scratch) x y
        (realization.factor * (memoryCost
          (link (Stack.Memory.pairMethods front rear 4 2) (Queue.transfer 2))
            (memoryState frontier x) + 82)) ∧
      memoryState frontier y = (Memory.spec 4).clientState (memoryState frontier x)
        (link (Stack.Memory.pairMethods front rear 4 2) (Queue.transfer 2)) := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    change 12 + i.val = 12 + j.val at this
    omega
  have hd (i : Fin 11) (j) : src i ≠ scratch j := by
    intro h
    have := congrArg Fin.val h
    change i.val = 12 + j.val at this
    have := i.isLt
    omega
  have hf (j) : scratch j ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    change 12 + j.val = 11 at this
    omega
  have hs (i : Fin 11) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    change i.val = 11 at this
    have := i.isLt
    omega
  obtain ⟨y, he, hm, _, _⟩ := (realization.code_spec frontier src scratch hi hd hf hs).2
    4 ((front, rear), 2) x hb hin hsafe hvalid
  exact ⟨y, he, hm⟩

-- A genuine compiled transfer reverses the rear into the front, with all memory framed globally.
example : ∃ y, ExecWithin 4 (realization.code frontier src scratch) data y
    (94 * realization.factor) ∧ y.mem 0 = 2 ∧ y.mem 1 = 15 ∧ y.mem 2 = 7 ∧
      y.mem 3 = 0 ∧ y.mem 100 = 9 ∧ y.regs frontier = 6 := by
  have hb : data.Bounded 4 := by
    refine ⟨fun i => ?_, mem_fits⟩
    change Fits 4 (if h : i.val < 11 then
      transferWords layoutWords ((front, rear), 2) ⟨i.val, h⟩ else
      if i.val = 11 then 6 else 0)
    split
    · exact encoded_fits _
    · split <;> norm_num [Fits]
  have hin : data.regs ∘ src = transferWords layoutWords ((front, rear), 2) := by
    funext i
    simp [data, src]
  have hm : memoryState frontier data = initial := by
    apply Memory.State.ext
    · rfl
    · simp [memoryState, data, frontier, initial]
  obtain ⟨y, he, hmem⟩ := execution data hb hin (hm ▸ safe) (hm ▸ valid)
  rw [hm] at he hmem
  change ExecWithin 4 (realization.code frontier src scratch) data y
    (realization.factor * (12 + (40 * 2 + 1) + 1)) at he
  refine ⟨y, he.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact congrArg (fun s : Memory.State => s.mem 0) hmem
    | exact congrArg (fun s : Memory.State => s.mem 1) hmem
    | exact congrArg (fun s : Memory.State => s.mem 2) hmem
    | exact congrArg (fun s : Memory.State => s.mem 3) hmem
    | exact congrArg (fun s : Memory.State => s.mem 100) hmem
    | exact congrArg Memory.State.frontier hmem

private def empty : Memory.State := ⟨fun a => if a = 0 ∨ a = 3 then 0 else 9, 6⟩
private noncomputable def emptyData : Data registers := ⟨data.regs, empty.mem⟩

-- The SAME fixed emitter pays its inactive tail: the source stops after one empty rear pop,
-- while the runtime fuel is two. No further memory query is introduced by the inactive loop.
example : ∃ y, ExecWithin 4 (realization.code frontier src scratch) emptyData y
    (83 * realization.factor) ∧ y.mem = empty.mem ∧ y.regs frontier = 6 := by
  have hb : emptyData.Bounded 4 := by
    constructor
    · intro i
      change Fits 4 (if h : i.val < 11 then
        transferWords layoutWords ((front, rear), 2) ⟨i.val, h⟩ else
        if i.val = 11 then 6 else 0)
      split
      · exact encoded_fits _
      · split <;> norm_num [Fits]
    · intro a
      change Fits 4 (if a = 0 ∨ a = 3 then 0 else 9)
      split <;> norm_num [Fits]
  have hin : emptyData.regs ∘ src = transferWords layoutWords ((front, rear), 2) := by
    funext i
    simp [emptyData, data, src]
  have hm : memoryState frontier emptyData = empty := by
    apply Memory.State.ext
    · rfl
    · simp [memoryState, emptyData, data, frontier, empty]
  have hsafe : iterationSafe transferBody transferSafe 4 (front, rear) 2 true empty := by
    change (rear.Valid 4 2 ∧ Stack.Memory.Inv rear empty ∧ True) ∧ True ∧ True
    refine ⟨⟨⟨rfl, ?_, rfl, ?_⟩, ⟨?_, ?_, ?_⟩, trivial⟩, trivial, trivial⟩ <;>
      norm_num [rear, empty, Block.Allocated, Block.Owns, Fits]
  have hvalid : (Memory.spec 4).ValidHistory empty ((Memory.spec 4).clientHistory empty
      (link (Stack.Memory.pairMethods front rear 4 2) (Queue.transfer 2))) := by decide
  obtain ⟨y, he, hmem⟩ := execution emptyData hb hin (hm ▸ hsafe) (hm ▸ hvalid)
  rw [hm] at he hmem
  change ExecWithin 4 (realization.code frontier src scratch) emptyData y
    (realization.factor * (1 + 82)) at he
  refine ⟨y, he.mono (by omega), ?_, ?_⟩
  · exact congrArg Memory.State.mem hmem
  · exact congrArg Memory.State.frontier hmem

end ComplexityTests.WordRAMRealizationQueue
