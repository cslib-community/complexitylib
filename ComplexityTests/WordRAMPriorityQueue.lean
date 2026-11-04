/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: local-only (native priority-queue migration regressions)

public import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Certificate

/-! The original operation sequence and dirty-initialization cases, through the replacement
fixed program. These are certified actual executions, with halt-inclusive call bounds. The
old interpreter's implementation-specific instruction/register constants are not retained.
External argument delivery and host continuations have the existing operation-call semantics. -/

public section

namespace WordRAMPriorityQueueTests

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

/-- The existing indexed-priority-queue specification for this four-handle fixture. -/
abbrev spec := indexedMinPQSpec 4 20
private abbrev SequenceResult := List (Option ℕ) × List (Option (Fin 4 × ℕ)) × Bool

/-- The retained sequence checks absent/present lookup, zero key, decrease, strict key/handle
ties, extraction down to empty and the empty test on both sides. -/
private def sequence : spec.Client SequenceResult := do
  let emp₀ ← spec.call .isEmpty
  let gk₀ ← spec.call (.getKey 2)
  spec.call (.insert 2 0)
  let emp₁ ← spec.call .isEmpty
  let gk₂ ← spec.call (.getKey 2)
  let gk₁ ← spec.call (.getKey 1)
  spec.call (.insert 3 5)
  spec.call (.insert 1 5)
  spec.call (.insert 0 9)
  spec.call (.decreaseKey 0 5)
  let e₁ ← spec.call .extractMin
  let e₂ ← spec.call .extractMin
  let e₃ ← spec.call .extractMin
  let e₄ ← spec.call .extractMin
  let e₅ ← spec.call .extractMin
  let emp₂ ← spec.call .isEmpty
  pure ([gk₀, gk₂, gk₁], [e₁, e₂, e₃, e₄, e₅], emp₀ && !emp₁ && emp₂)

private def sequenceResult : SequenceResult :=
  ([none, some 0, none], [some (2, 0), some (0, 5), some (1, 5), some (3, 5), none], true)

/-- Clearing stale words really yields an empty queue before a new insertion/extraction. -/
private def clearedClient : spec.Client (Bool × Option ℕ × Option (Fin 4 × ℕ)) := do
  let emp ← spec.call .isEmpty
  let key ← spec.call (.getKey 1)
  spec.call (.insert 1 7)
  let entry ← spec.call .extractMin
  pure (emp, key, entry)

private theorem sequence_valid : spec.ValidHistory (IndexedMinPQ.empty 4)
    (spec.clientHistory (IndexedMinPQ.empty 4) sequence) := by
  change spec.ValidHistory (IndexedMinPQ.empty 4)
    [.isEmpty, .getKey 2, .insert 2 0, .isEmpty, .getKey 2, .getKey 1, .insert 3 5,
      .insert 1 5, .insert 0 9, .decreaseKey 0 5, .extractMin, .extractMin, .extractMin,
      .extractMin, .extractMin, .isEmpty]
  simp [StateTransitionSpec.ValidHistory, spec, IndexedMinPQ.valid, IndexedMinPQ.step,
    IndexedMinPQ.empty]

private theorem sequence_result :
    spec.clientResult (IndexedMinPQ.empty 4) sequence = sequenceResult := by decide +kernel

private theorem cleared_valid : spec.ValidHistory (IndexedMinPQ.empty 4)
    (spec.clientHistory (IndexedMinPQ.empty 4) clearedClient) := by
  change spec.ValidHistory (IndexedMinPQ.empty 4)
    [.isEmpty, .getKey 1, .insert 1 7, .extractMin]
  simp [StateTransitionSpec.ValidHistory, spec, IndexedMinPQ.valid, IndexedMinPQ.step,
    IndexedMinPQ.empty]

private theorem cleared_result : spec.clientResult (IndexedMinPQ.empty 4) clearedClient =
    (true, none, some (1, 7)) := by decide +kernel

noncomputable section

private def initial (base : ℕ) (mem : ℕ → ℕ) : Data Program.registers :=
  ⟨fun i => if i = Program.code.frontierReg then base else
    if i = Program.code.nReg then 4 else 0, mem⟩

private theorem initial_bounded (base : ℕ) (mem : ℕ → ℕ)
    (hb : Fits 10 base) (hm : ∀ a, Fits 10 (mem a)) : (initial base mem).Bounded 10 := by
  refine ⟨fun i => ?_, hm⟩
  dsimp only [initial]
  split_ifs
  · exact hb
  · decide
  · exact fits_zero _

private theorem initial_frontier (base : ℕ) (mem : ℕ → ℕ) :
    (initial base mem).regs Program.code.frontierReg = base := by
  simp only [initial, ite_true]

private theorem initial_dimension (base : ℕ) (mem : ℕ → ℕ) :
    (initial base mem).regs Program.code.nReg = 4 := by
  simp only [initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]

example : ∃ y₀ y traces,
    ExecWithin 10 Program.code.initFresh (initial 10 (fun _ => 0)) y₀
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
    Executes ((dynamicProgram 4 20).ExecOp 10) sequence y₀ sequenceResult y traces ∧
    Representation.Rep 10 (show Fits 10 4 by decide) (show Fits 10 20 by decide)
      (IndexedMinPQ.empty 4) y ∧
    DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
      spec.totalCost (fun _ o => operationTime o + 1) (IndexedMinPQ.empty 4)
        (spec.clientHistory (IndexedMinPQ.empty 4) sequence) := by
  have hS : Fits 10 (10 + space 4) := by decide
  have hK : Fits 10 20 := by decide
  obtain ⟨y₀, he, _, _, hr₀⟩ := Representation.initFresh_rep
    (show Fits 10 4 by decide) hK (initial 10 (fun _ => 0))
    (initial_bounded _ _ (by decide) (fun _ => fits_zero _))
    (initial_frontier _ _) (initial_dimension _ _) hS (fun _ _ => rfl)
  obtain ⟨y, tr, hex, hr, ht⟩ := run_client_bound hS hK sequence hr₀ sequence_valid
  have hempty : spec.clientState (IndexedMinPQ.empty 4) sequence = IndexedMinPQ.empty 4 :=
    by decide +kernel
  rw [sequence_result] at hex
  rw [hempty] at hr
  exact ⟨y₀, y, tr, he, hex, hr, ht⟩

private def dirtyMemory (a : ℕ) : ℕ := if a = 0 then 7 else if a = 100 then 9 else 42

example : ∃ y₀ y traces,
    ExecWithin 10 Program.code.initClear (initial 4 dirtyMemory) y₀
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor +
        4 * space 4 + 6) ∧
    Executes ((dynamicProgram 4 20).ExecOp 10) clearedClient y₀ (true, none, some (1, 7)) y
      traces ∧
    DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
      spec.totalCost (fun _ o => operationTime o + 1) (IndexedMinPQ.empty 4)
        (spec.clientHistory (IndexedMinPQ.empty 4) clearedClient) := by
  have hS : Fits 10 (4 + space 4) := by decide
  have hK : Fits 10 20 := by decide
  let C := subroutineImpl hS hK
  have hp : ∀ i, (initial 4 dirtyMemory).regs (Program.code.initParams i) =
      (![4] : Fin 1 → ℕ) i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Program.code.initParams_eq, Matrix.cons_val_zero] using initial_dimension 4 _
  have hm : ∀ a, Fits 10 (dirtyMemory a) := by
    intro a
    unfold dirtyMemory
    split_ifs <;> decide
  obtain ⟨y₀, he, _, hr₀, _, _⟩ := C.initClear_exec
    (initial_bounded _ _ (by decide) hm) (initial_frontier _ _) hp
  have hrep : Representation.Rep 4 (show Fits 10 4 by decide) hK (IndexedMinPQ.empty 4) y₀ := by
    rw [subroutineImpl_toBase] at hr₀
    exact (subroutineBase_rep_iff hS hK _ _).mp hr₀
  have htime : C.initTime =
      2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor := by
    rw [subroutineImpl_toBase, subroutineBase_initTime]
  have hspace : C.space = space 4 := by
    rw [subroutineImpl_toBase, subroutineBase_space]
  rw [htime, hspace] at he
  obtain ⟨y, tr, hex, _, ht⟩ := run_client_bound hS hK clearedClient hrep cleared_valid
  rw [cleared_result] at hex
  exact ⟨y₀, y, tr, he, hex, ht⟩

end

end WordRAMPriorityQueueTests
