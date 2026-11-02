/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueDispatch
public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueAdapter
public import Complexity.Computability.WordRAM.Realization.Program

/-!
# Faithful allocation for the memory-oracle queue

The existing initializer zeroes each one-cell count and allocates each item array dirty. The
certificates preserve this literal whole-memory behavior, without clearing the item arrays or
replacing the initial memory. Code precedes the runtime capacity, frontier and allocation replies.

## Main definitions

* `allocPair`: exactly the two allocation calls that prefix `Queue.Memory.run`.
* `roundTrip`: the supported concrete enqueue/dequeue client.

## Main results

* `realizes_allocLayout`, `realizes_allocPair`: certified initialization with constant local work.
* `run_eq_allocPair_bind`: the prefix is the one used by the actual M1a queue run.
* `realizes_roundTrip`, `roundTrip_correct_source`: uniform realization and the actual source
  answer, with all fits and the physical word width explicit.

The existing flat-program projections apply to these certificates. Their `Data.init` input
prefix is charged separately and starts with zero future cells; it is distinct from the body
ABI on arbitrary bounded old memory, which can retain dirty item words such as seven.

## References

This is original realization infrastructure for the existing `Stack.Memory` and `Queue.Memory`
programs. Their source-algorithm citations and credit remain in those modules.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueAllocation

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private theorem copyResult {δ α : Type} {k l : ℕ} (input : δ ↪ (Fin k → ℕ))
    (output : α ↪ (Fin l → ℕ)) (f : δ → α) (ix : Fin l → Fin k)
    (hf : ∀ d i, output (f d) i = input d (ix i)) :
    Realizes .exact (fun d => pure (f d)) input output
      (fun _ _ _ => True) (fun _ _ => 2 * l) := by
  have h := Realizes.glueVector (B := .exact) input output f
    (fun i v => v (ix i)) (fun i v => v (ix i)) (fun _ => 1) hf
    (P := fun _ => True) (fun i => GlueComputes.proj (ix i) (fun _ _ => le_rfl))
  exact h.consequence (fun _ _ _ hwords _ _ => ⟨trivial, fun i => hwords (ix i)⟩)
    (fun _ _ => by simp [two_mul])

/-- Exactly the allocation prefix of the existing queue run: only the two one-cell count
fields are cleared. Both item arrays retain their old contents. -/
def allocPair (C : ℕ) : Memory.Prog (Stack.Memory.Layout × Stack.Memory.Layout) := do
  let front ← Stack.Memory.allocLayout C
  let rear ← Stack.Memory.allocLayout C
  pure (front, rear)

/-- The named prefix changes no source method or client. -/
theorem run_eq_allocPair_bind (w C : ℕ) {α : Type}
    (p : (Queue.WordRAM.spec w C).Client α) :
    Queue.Memory.run w C p = (allocPair C).bind
      (fun L => link (Queue.Memory.memMethods L.1 L.2 w C) p) := by
  simp only [Queue.Memory.run, allocPair, PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]

/-- The source prefix returns the actual allocation addresses and retains the full dirty memory. -/
theorem runClient_allocPair (w C : ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s (allocPair C) =
      ((Queue.Memory.frontLayout s C, Queue.Memory.rearLayout s C), Queue.Memory.allocated s C,
        [.alloc 1, .allocDirty C, .alloc 1, .allocDirty C]) := rfl

/-- The exact single-stack initializer has fixed code before capacity, frontier or replies.
The staged one and all four returned layout coordinates are charged. -/
theorem realizes_allocLayout :
    Realizes .exact Stack.Memory.allocLayout (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      MemoryStack.layoutWords (fun w C s => Fits w (s.frontier + 1 + C)) (fun _ _ => 12) := by
  let e₁ := appendWords word word
  let e₂ := appendWords e₁ word
  let e₃ := appendWords e₂ word
  have hone := Realizes.glue word
    (GlueComputes.const (B := .exact) (P := fun _ => True) (bound := fun _ => 1)
      1 (fun _ _ => le_rfl))
  have hcount := Realizes.alloc e₁ 1
  have hitems := Realizes.allocDirty e₂ 0
  have hreturn := copyResult e₃ MemoryStack.layoutWords
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ =>
      (⟨⟨d.1.2, d.1.1.2⟩, ⟨d.2, d.1.1.1⟩⟩ : Stack.Memory.Layout))
    ![2, 1, 3, 0] (by intro d i; fin_cases i <;> rfl)
  have h := hone.bind (hcount.bind (hitems.bind hreturn))
  have hp : (fun C : ℕ => (pure 1 : Memory.Prog ℕ).bind (fun one =>
      (Memory.alloc one).bind (fun count => (Memory.allocDirty C).bind (fun items =>
        pure (⟨⟨count, one⟩, ⟨items, C⟩⟩ : Stack.Memory.Layout))))) = Stack.Memory.allocLayout := by
    funext C
    simp only [Stack.Memory.allocLayout, Memory.allocBlock, Memory.allocBlockDirty,
      PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
  simp only [PFunctor.FreeM.bind_eq_bind, pure_bind] at hp h
  change Realizes .exact (fun C : ℕ => (Memory.alloc 1).bind (fun count =>
    (Memory.allocDirty C).bind (fun items =>
      pure (⟨⟨count, 1⟩, ⟨items, C⟩⟩ : Stack.Memory.Layout)))) word MemoryStack.layoutWords _ _ at h
  simp only [PFunctor.FreeM.bind_eq_bind] at h
  rw [hp] at h
  apply h.consequence (hwork := fun _ _ => le_rfl)
  intro w C s _ _ hf
  exact ⟨⟨trivial, hf.of_le (by omega)⟩, trivial, trivial, trivial⟩

/-- The actual two-stack prefix has six memory units and 42 explicitly certified local units,
independent of the item capacity. No item cell is cleared by this initialization. -/
theorem realizes_allocPair :
    Realizes .exact allocPair (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding MemoryQueue.layoutWords
      (fun w C s => Fits w (s.frontier + 2 * (C + 1))) (fun _ _ => 42) := by
  let e₁ := appendWords word MemoryStack.layoutWords
  let e₂ := appendWords e₁ MemoryStack.layoutWords
  have hsecond := realizes_allocLayout.reindex (fun d : ℕ × Stack.Memory.Layout => d.1)
    e₁ ![0] (by intro d i; fin_cases i; rfl)
  have hreturn := copyResult e₂ MemoryQueue.layoutWords
    (fun d : (ℕ × Stack.Memory.Layout) × Stack.Memory.Layout => (d.1.2, d.2))
    ![1, 2, 3, 4, 5, 6, 7, 8] (by intro d i; fin_cases i <;> rfl)
  apply (realizes_allocLayout.bind (hsecond.bind hreturn)).consequence
    (hwork := fun _ _ => le_rfl)
  intro w C s _ _ hf
  change Fits w (s.frontier + 1 + C) ∧
    Fits w (s.frontier + 1 + C + 1 + C) ∧ True
  refine ⟨hf.of_le (by omega), ?_, trivial⟩
  convert hf using 1; omega

/-- This initialization's actual memory charge is constant; it does not clear `C` item cells. -/
theorem allocPair_memoryCost (C : ℕ) (s : Memory.State) : memoryCost (allocPair C) s = 6 := rfl

/-- The end-fit condition makes every operation of the exact allocation prefix admissible. -/
theorem valid_allocPair {w C : ℕ} {s : Memory.State}
    (hf : Fits w (s.frontier + 2 * (C + 1))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (allocPair C)) := by
  change Fits w (s.frontier + 1) ∧ Fits w (s.frontier + 1 + C) ∧
    Fits w (s.frontier + 1 + C + 1) ∧ Fits w (s.frontier + 1 + C + 1 + C) ∧ True
  exact ⟨hf.of_le (by omega), hf.of_le (by omega), hf.of_le (by omega),
    hf.of_le (by omega), trivial⟩

private theorem allocated_counts (C : ℕ) (s : Memory.State) :
    (Queue.Memory.allocated s C).mem (Queue.Memory.frontLayout s C).count.base = 0 ∧
    (Queue.Memory.allocated s C).mem (Queue.Memory.rearLayout s C).count.base = 0 := by
  constructor
  · change clear (clear s.mem s.frontier 1) (s.frontier + 1 + C) 1 s.frontier = 0
    rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
    apply clear_of_owns
    change s.frontier ≤ s.frontier ∧ s.frontier < s.frontier + 1
    omega
  · apply clear_of_owns
    change s.frontier + 1 + C ≤ s.frontier + 1 + C ∧
      s.frontier + 1 + C < s.frontier + 1 + C + 1
    omega

private theorem allocated_invariants (C : ℕ) (s : Memory.State) :
    Stack.Memory.Inv (Queue.Memory.frontLayout s C) (Queue.Memory.allocated s C) ∧
      Stack.Memory.Inv (Queue.Memory.rearLayout s C) (Queue.Memory.allocated s C) := by
  obtain ⟨hF, hR⟩ := allocated_counts C s
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · change s.frontier + 1 ≤ s.frontier + 1 + C + 1 + C; omega
    · change s.frontier + 1 + C ≤ s.frontier + 1 + C + 1 + C; omega
    · rw [hF]; exact Nat.zero_le _
  · refine ⟨?_, ?_, ?_⟩
    · change s.frontier + 1 + C + 1 ≤ s.frontier + 1 + C + 1 + C; omega
    · exact le_rfl
    · rw [hR]; exact Nat.zero_le _

private theorem wellFormed_client {w : ℕ} {α : Type} {s : Memory.State}
    (hw : Memory.WellFormed w s) (p : Memory.Prog α)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  have h := hw.run hv
  rw [StateTransitionSpec.run_runClient, clientState_width] at h
  exact h

private theorem allocated_wellFormed {w C : ℕ} {s : Memory.State} (hw : Memory.WellFormed w s)
    (hf : Fits w (s.frontier + 2 * (C + 1))) :
    Memory.WellFormed w (Queue.Memory.allocated s C) := by
  simpa only [StateTransitionSpec.clientState, runClient_allocPair] using
    wellFormed_client hw (allocPair C) (valid_allocPair hf)

/-- The concrete supported client; no certificate for an arbitrary opaque client is assumed. -/
def roundTrip (w C v : ℕ) : (Queue.WordRAM.spec w C).Client (Option ℕ) := do
  let _ ← PFunctor.FreeM.lift (P := (Queue.WordRAM.spec w C).signature) (Queue.QueueOp.enqueue v)
  PFunctor.FreeM.lift (P := (Queue.WordRAM.spec w C).signature) Queue.QueueOp.dequeue

/-- Both runtime argument words are faithfully retained. -/
def roundTripWords : (ℕ × ℕ) ↪ (Fin 2 → ℕ) :=
  ((Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding.prodMap
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans (Fin.appendEquiv 1 1).toEmbedding

private def enqueued (C v : ℕ) (s : Memory.State) : Memory.State :=
  (Memory.spec 0).clientState (Queue.Memory.allocated s C)
    (Stack.Memory.push (Queue.Memory.rearLayout s C) v)

private theorem enqueued_counts (C v : ℕ) (s : Memory.State) :
    (enqueued C v s).mem (Queue.Memory.frontLayout s C).count.base = 0 ∧
      (enqueued C v s).mem (Queue.Memory.rearLayout s C).count.base = 1 := by
  obtain ⟨hF, hR⟩ := allocated_counts C s
  let m := clear (clear s.mem s.frontier 1) (s.frontier + 1 + C) 1
  change m s.frontier = 0 at hF
  change m (s.frontier + 1 + C) = 0 at hR
  simp only [enqueued, StateTransitionSpec.clientState, Stack.Memory.runClient_push]
  constructor
  · change Function.update
      (Function.update m (s.frontier + 1 + C + 1 + m (s.frontier + 1 + C)) v)
      (s.frontier + 1 + C) (m (s.frontier + 1 + C) + 1) s.frontier = 0
    rw [hR, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hF
  · change Function.update (_ : ℕ → ℕ) (s.frontier + 1 + C)
      (m (s.frontier + 1 + C) + 1) (s.frontier + 1 + C) = 1
    rw [Function.update_self, hR]

private theorem enqueued_work (C v : ℕ) (s : Memory.State) :
    MemoryQueueDispatch.dequeueWork (Queue.Memory.frontLayout s C, Queue.Memory.rearLayout s C)
      (enqueued C v s) = 109 := by
  obtain ⟨hF, hR⟩ := enqueued_counts C v s
  have hp := Stack.Memory.runClient_pop_of_eq_zero (w := 0) (Queue.Memory.frontLayout s C)
    (enqueued C v s) hF
  simp only [MemoryQueueDispatch.dequeueWork, MemoryQueueDispatch.dequeueFuel,
    StateTransitionSpec.clientResult, StateTransitionSpec.clientState, hp,
    Stack.Memory.runClient_size, hR]

private theorem enqueued_domain {w C v : ℕ} {s : Memory.State} (hw : Memory.WellFormed w s)
    (hf : Fits w (s.frontier + 2 * (C + 1))) (hC : 1 ≤ C) (hv : Fits w v) :
    MemoryQueueDispatch.dequeueSafe w
      (Queue.Memory.frontLayout s C, Queue.Memory.rearLayout s C) (enqueued C v s) := by
  have hLayouts := MemoryQueueAdapter.layouts_valid (base := s.frontier) hf
  change (Queue.Memory.frontLayout s C).Valid w C ∧ (Queue.Memory.rearLayout s C).Valid w C ∧
    Disjoint (Queue.Memory.frontLayout s C).footprint
      (Queue.Memory.rearLayout s C).footprint at hLayouts
  obtain ⟨hL₁, hL₂, hd⟩ := hLayouts
  obtain ⟨hi₁, hi₂⟩ := allocated_invariants C s
  obtain ⟨hc₁, hc₂⟩ := allocated_counts C s
  have hwA := allocated_wellFormed hw hf
  have hvPush : (Stack.WordRAM.spec w C).valid
      (Stack.Memory.abs (Queue.Memory.rearLayout s C) (Queue.Memory.allocated s C))
      (.push v) := by
    refine ⟨?_, hv⟩
    rw [Stack.Memory.length_abs, hc₂]
    omega
  let M := Stack.Memory.refinement hL₂
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    (M.valid (.push v) hi₂ hvPush)
  have hcorrect := M.correct (.push v) hi₂ hvPush
    ((Memory.spec w).clientRun_canonical (Queue.Memory.allocated s C) _ hvalid)
  have hframe := Stack.Memory.frame hL₂ hL₁ hd.symm hi₁ (.push v) hvPush
  have hi₁' : Stack.Memory.Inv (Queue.Memory.frontLayout s C) (enqueued C v s) := by
    simpa only [enqueued, Stack.Memory.methods, StateTransitionSpec.clientState, runClient_width]
      using hframe.2
  have hi₂' : Stack.Memory.Inv (Queue.Memory.rearLayout s C) (enqueued C v s) := by
    have hcorrect' := hcorrect.2
    change Stack.Memory.Inv (Queue.Memory.rearLayout s C)
      ((Memory.spec w).clientState (Queue.Memory.allocated s C)
        (Stack.Memory.push (Queue.Memory.rearLayout s C) v)) at hcorrect'
    simpa only [enqueued, StateTransitionSpec.clientState, runClient_width] using hcorrect'
  have hvalid' : (Memory.spec w).ValidHistory (Queue.Memory.allocated s C)
      ((Memory.spec w).clientHistory (Queue.Memory.allocated s C)
        (Stack.Memory.push (Queue.Memory.rearLayout s C) v)) := hvalid
  have hwE : Memory.WellFormed w (enqueued C v s) := wellFormed_client hwA _ hvalid'
  apply MemoryQueueAdapter.dequeue_safe hL₁ hL₂ hd hwE hi₁' hi₂'
  obtain ⟨hF, hR⟩ := enqueued_counts C v s
  rw [hF, hR]
  omega

/-- The concrete allocated source client has a uniform native emitter before capacity, value,
frontier, width or either allocated layout. Its explicit local work includes faithful allocation
and the actual fallback transfer; the old dirty item cells are not initialized for free. -/
theorem realizes_roundTrip (sourceWidth : ℕ) :
    Realizes .exact (fun d : ℕ × ℕ =>
      Queue.Memory.run sourceWidth d.1 (roundTrip sourceWidth d.1 d.2))
      roundTripWords optionWords
      (fun w d s => 1 ≤ d.1 ∧ Fits w (s.frontier + 2 * (d.1 + 1))) (fun _ _ => 163) := by
  let e₁ := appendWords roundTripWords MemoryQueue.layoutWords
  let e₂ := appendWords e₁ (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
  have halloc := realizes_allocPair.reindex (fun d : ℕ × ℕ => d.1) roundTripWords ![0]
    (by intro d i; fin_cases i; rfl)
  have henqueue := (MemoryQueueDispatch.realizes_enqueue 0 0).reindex
    (fun d : (ℕ × ℕ) × (Stack.Memory.Layout × Stack.Memory.Layout) => (d.2, d.1.2))
    e₁ ![2, 3, 4, 5, 6, 7, 8, 9, 1] (by intro d i; fin_cases i <;> rfl)
  have hdequeue := (MemoryQueueDispatch.realizes_dequeue 0 0).reindex
    (fun d : ((ℕ × ℕ) × (Stack.Memory.Layout × Stack.Memory.Layout)) × Unit => d.1.2)
    e₂ ![2, 3, 4, 5, 6, 7, 8, 9] (by intro d i; fin_cases i <;> rfl)
  have h := halloc.bind (henqueue.bind hdequeue)
  have hp : (fun d : ℕ × ℕ => (allocPair d.1).bind (fun L =>
      (Queue.Memory.memMethods L.1 L.2 0 0 (.enqueue d.2)).bind
        (fun _ => Queue.Memory.memMethods L.1 L.2 0 0 .dequeue))) =
      (fun d : ℕ × ℕ => Queue.Memory.run sourceWidth d.1
        (roundTrip sourceWidth d.1 d.2)) := by
    funext d
    rw [run_eq_allocPair_bind]
    congr 1
    funext L
    simp only [roundTrip, link, PFunctor.FreeM.liftM_bind]
    rw [PFunctor.FreeM.liftM_lift, PFunctor.FreeM.liftM_lift]
    simp only [PFunctor.FreeM.bind_eq_bind,
      MemoryQueue.memMethods_enqueue, MemoryQueue.memMethods_dequeue]
  simp only [PFunctor.FreeM.bind_eq_bind] at hp h
  rw [hp] at h
  apply h.consequence
  · intro w d s hwords hw ⟨hC, hf⟩
    obtain ⟨hi₁, hi₂⟩ := allocated_invariants d.1 s
    obtain ⟨_, hc₂⟩ := allocated_counts d.1 s
    have hL₂ : (Queue.Memory.rearLayout s d.1).Valid w d.1 :=
      Stack.Memory.valid_allocLayout (hf.of_le (by omega))
    change Fits w (s.frontier + 2 * (d.1 + 1)) ∧
      ((Queue.Memory.rearLayout s d.1).Valid w d.1 ∧
        Stack.Memory.Inv (Queue.Memory.rearLayout s d.1) (Queue.Memory.allocated s d.1) ∧
        (Queue.Memory.allocated s d.1).mem (Queue.Memory.rearLayout s d.1).count.base < d.1) ∧
      MemoryQueueDispatch.dequeueSafe w
        (Queue.Memory.frontLayout s d.1, Queue.Memory.rearLayout s d.1)
        ((Memory.spec 0).clientState (Queue.Memory.allocated s d.1)
          (Queue.Memory.memMethods (Queue.Memory.frontLayout s d.1)
            (Queue.Memory.rearLayout s d.1) 0 0 (.enqueue d.2)))
    refine ⟨hf, ⟨hL₂, hi₂, ?_⟩, ?_⟩
    · rw [hc₂]; omega
    · rw [MemoryQueue.memMethods_enqueue]
      exact enqueued_domain hw hf hC (hwords 1)
  · intro d s
    change 42 + (10 + MemoryQueueDispatch.dequeueWork
      (Queue.Memory.frontLayout s d.1, Queue.Memory.rearLayout s d.1)
      ((Memory.spec 0).clientState (Queue.Memory.allocated s d.1)
        (Queue.Memory.memMethods (Queue.Memory.frontLayout s d.1)
          (Queue.Memory.rearLayout s d.1) 0 0 (.enqueue d.2))) + 1) + 1 ≤ 163
    rw [MemoryQueue.memMethods_enqueue]
    change 42 + (10 + MemoryQueueDispatch.dequeueWork
      (Queue.Memory.frontLayout s d.1, Queue.Memory.rearLayout s d.1)
      (enqueued d.1 d.2 s) + 1) + 1 ≤ 163
    rw [enqueued_work]

/-- The actual allocated source client is admissible and returns `some v`. The capacity,
value-word and final-frontier fits are explicit; no arbitrary-client native claim is used. -/
theorem roundTrip_correct {w C v : ℕ} {s : Memory.State} (hC : 1 ≤ C) (hv : Fits w v)
    (hf : Fits w (s.frontier + 2 * (C + 1))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (Queue.Memory.run w C (roundTrip w C v))) ∧
      (Memory.spec w).clientResult s (Queue.Memory.run w C (roundTrip w C v)) = some v := by
  apply Queue.Memory.run_correct (roundTrip w C v) hf
  change (0 < C ∧ Fits w v) ∧ True ∧ True
  exact ⟨⟨by omega, hv⟩, trivial, trivial⟩

/-- The specification-width parameter does not select source code for this concrete client.
Native word bounds and operation admissibility are still checked separately. -/
theorem roundTrip_run_width (w C v : ℕ) :
    Queue.Memory.run w C (roundTrip w C v) = Queue.Memory.run 0 C (roundTrip 0 C v) := by
  rw [run_eq_allocPair_bind, run_eq_allocPair_bind]
  congr 1
  funext L
  simp only [roundTrip, link, PFunctor.FreeM.liftM_bind]
  rw [PFunctor.FreeM.liftM_lift, PFunctor.FreeM.liftM_lift,
    PFunctor.FreeM.liftM_lift, PFunctor.FreeM.liftM_lift]
  simp only [MemoryQueue.memMethods_enqueue, MemoryQueue.memMethods_dequeue]

/-- Fix a source interface once, before the physical word width, while retaining the exact
source answer and memory-history admissibility of the supported client. -/
theorem roundTrip_correct_source (sourceWidth : ℕ) {w C v : ℕ} {s : Memory.State}
    (hC : 1 ≤ C) (hv : Fits w v) (hf : Fits w (s.frontier + 2 * (C + 1))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (Queue.Memory.run sourceWidth C (roundTrip sourceWidth C v))) ∧
      (Memory.spec w).clientResult s
        (Queue.Memory.run sourceWidth C (roundTrip sourceWidth C v)) = some v := by
  have h := roundTrip_correct hC hv hf
  rw [roundTrip_run_width w C v] at h
  rw [roundTrip_run_width sourceWidth C v]
  exact h

end Cslib.WordRAM.Realization.MemoryQueueAllocation
