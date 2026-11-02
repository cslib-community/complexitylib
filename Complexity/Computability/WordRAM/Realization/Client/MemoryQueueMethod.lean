/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueDispatch

/-!
# Uniform typed-label realization of both queue methods

Both complete stack layouts and the queue operation are runtime inputs. One native branch
selects the existing certified method; certified vector glue then stages the complete typed
operation/result label. Tags, payload copies, binds and dispatch are charged rather than supplied
as free host computation. The emitter and exchange constant precede every layout, base, capacity,
operation and word width.

The canonical source uses the computationally erased parameters `w = C = 0`; `method_source_eq`
identifies it with the actual memory method at any chosen specification parameters without
choosing another native emitter. The underlying memory and queue methods are unchanged.

## Main definitions

* `opWords`, `methodWords`: faithful operation and complete runtime argument encodings.
* `labelWords`: a faithful four-word encoding of the typed queue operation/result label.
* `method`, `methodSafe`, `methodWork`: canonical source, actual path domain and local-work charge.

## Main results

* `realizes_method`: one realization handles every runtime layout and queue operation.
* `methodWork_le`: a uniform affine bound uses the rear-count expression for transfer fuel.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueMethod

open Cslib.DataStructure

private abbrev Layouts := Stack.Memory.Layout × Stack.Memory.Layout
private abbrev Label := (Queue.queue ℕ).Label
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

/-- The operation tag, unshifted enqueue payload and a retained comparison-zero word. -/
def opWords : Queue.QueueOp ℕ ↪ (Fin 3 → ℕ) where
  toFun
    | .enqueue v => ![0, v, 0]
    | .dequeue => ![1, 0, 0]
  inj' := by
    intro a b h
    cases a with
    | enqueue u =>
      cases b with
      | enqueue v => exact congrArg Queue.QueueOp.enqueue (congrFun h 1)
      | dequeue => have hh := congrFun h 0; simp at hh
    | dequeue =>
      cases b with
      | enqueue v => have hh := congrFun h 0; simp at hh
      | dequeue => rfl

/-- Layout fields occupy `0..7`, then operation tag `8`, payload `9` and comparison zero `10`. -/
def methodWords :
    ((Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) ↪ (Fin 11 → ℕ) :=
  (MemoryQueue.layoutWords.prodMap opWords).trans (Fin.appendEquiv 8 3).toEmbedding

/-- Typed labels retain the operation. Enqueue is `(0,v,0,0)`; dequeue is
`(1,0,option-tag,unshifted-payload)`, including the canonical zero payload for `none`. -/
def labelWords : (Queue.queue ℕ).Label ↪ (Fin 4 → ℕ) where
  toFun
    | ⟨.enqueue v, _⟩ => ![0, v, 0, 0]
    | ⟨.dequeue, a⟩ => ![1, 0, optionWords a 0, optionWords a 1]
  inj' := by
    rintro ⟨a, ar⟩ ⟨b, br⟩ h
    cases a with
    | enqueue u =>
      cases b with
      | enqueue v =>
        have hv : u = v := congrFun h 1
        cases hv
        cases ar
        cases br
        rfl
      | dequeue => have hh := congrFun h 0; simp at hh
    | dequeue =>
      cases b with
      | enqueue v => have hh := congrFun h 0; simp at hh
      | dequeue =>
        have ho : optionWords ar = optionWords br := by
          funext i
          fin_cases i
          · exact congrFun h 2
          · exact congrFun h 3
        have hab := optionWords.injective ho
        cases hab
        rfl

/-- The actual queue memory method followed by its complete typed label. -/
def method (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) :
    Memory.Prog (Queue.queue ℕ).Label := do
  let a ← Queue.Memory.memMethods d.1.1 d.1.2 0 0 d.2
  pure ⟨d.2, a⟩

/-- Specification width/capacity do not change the computational memory-method body. -/
theorem method_source_eq
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (w C : ℕ) :
    method d = (do
      let a ← Queue.Memory.memMethods d.1.1 d.1.2 w C d.2
      pure (⟨d.2, a⟩ : (Queue.queue ℕ).Label)) := by
  rcases d with ⟨L, op⟩
  unfold method
  cases op with
  | enqueue v => rw [MemoryQueue.memMethods_enqueue, MemoryQueue.memMethods_enqueue]
  | dequeue => rw [MemoryQueue.memMethods_dequeue, MemoryQueue.memMethods_dequeue]

/-- The entry domain is the existing domain of the selected path, with memory admissibility
retained separately in `Realizes`. -/
def methodSafe (w : ℕ)
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (s : Memory.State) : Prop :=
  match d.2 with
  | .enqueue _ => d.1.2.Valid w d.1.2.items.length ∧ Stack.Memory.Inv d.1.2 s ∧
      s.mem d.1.2.count.base < d.1.2.items.length
  | .dequeue => MemoryQueueDispatch.dequeueSafe w d.1 s

/-- Eight vector-staging units, a bind and the dispatch are charged in addition to the method.
Enqueue costs `21`; dequeue costs its actual path ledger plus `11`. -/
def methodWork (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ)
    (s : Memory.State) : ℕ :=
  match d.2 with
  | .enqueue _ => 21
  | .dequeue => MemoryQueueDispatch.dequeueWork d.1 s + 11

/-- A single affine estimate covers both operations without asserting a memory-only bound. -/
theorem methodWork_le (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ)
    (s : Memory.State) :
    methodWork d s ≤ 40 * MemoryQueueDispatch.dequeueFuel d.1 s + 80 := by
  rcases d with ⟨L, op⟩
  have h := MemoryQueueDispatch.dequeueWork_le L s
  cases op <;> dsimp only [methodWork] <;> omega

private def enqueueInput :=
  (methodWords.prodMap unitWords).trans (Fin.appendEquiv 11 0).toEmbedding

private def dequeueInput :=
  (methodWords.prodMap optionWords).trans (Fin.appendEquiv 11 2).toEmbedding

private def enqueueCoordinates : Fin 4 → (Fin 11 → ℕ) → ℕ :=
  ![fun _ => 0, fun v => v 9, fun _ => 0, fun _ => 0]

private theorem enqueueLabel :
    Realizes .exact (fun d : (Layouts × Queue.QueueOp ℕ) × Unit =>
        pure (⟨.enqueue (opWords d.1.2 1), ()⟩ : Label))
      enqueueInput labelWords (fun _ _ _ => True) (fun _ _ => 8) := by
  have hc (i : Fin 4) : GlueComputes .exact (fun _ : Fin 11 → ℕ => True)
      (enqueueCoordinates i) (enqueueCoordinates i) 1 := by
    fin_cases i
    · exact GlueComputes.const 0 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 9 (fun _ _ => le_rfl)
    · exact GlueComputes.const 0 (fun _ _ => le_rfl)
    · exact GlueComputes.const 0 (fun _ _ => le_rfl)
  have h := Realizes.glueVector enqueueInput labelWords
    (fun d => (⟨.enqueue (opWords d.1.2 1), ()⟩ : Label))
    enqueueCoordinates enqueueCoordinates (fun _ => 1)
    (fun d i => by fin_cases i <;> rfl) hc
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s hwords _ _
  refine ⟨trivial, fun i => ?_⟩
  fin_cases i
  · exact fits_zero w
  · exact hwords 9
  · exact fits_zero w
  · exact fits_zero w

private def dequeueCoordinates : Fin 4 → (Fin 13 → ℕ) → ℕ :=
  ![fun _ => 1, fun _ => 0, fun v => v 11, fun v => v 12]

private def dequeueBounds : Fin 4 → (Fin 13 → ℕ) → ℕ :=
  ![fun v => v 1, fun _ => 0, fun v => v 11, fun v => v 12]

private theorem dequeueLabel :
    Realizes .exact (fun d : (Layouts × Queue.QueueOp ℕ) × Option ℕ =>
        pure (⟨.dequeue, d.2⟩ : Label)) dequeueInput labelWords
      (fun w d _ => d.1.1.1.Valid w d.1.1.1.items.length) (fun _ _ => 8) := by
  have hc (i : Fin 4) : GlueComputes .exact (fun v : Fin 13 → ℕ => v 1 = 1)
      (dequeueCoordinates i) (dequeueBounds i) 1 := by
    fin_cases i
    · exact GlueComputes.const 1 (fun _ h => h.ge)
    · exact GlueComputes.const 0 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 11 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 12 (fun _ _ => le_rfl)
  have h := Realizes.glueVector dequeueInput labelWords
    (fun d => (⟨.dequeue, d.2⟩ : Label)) dequeueCoordinates dequeueBounds (fun _ => 1)
    (fun d i => by fin_cases i <;> rfl) hc
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s hwords _ hL
  refine ⟨hL.count_length, fun i => ?_⟩
  fin_cases i
  · exact hwords 1
  · exact fits_zero w
  · exact hwords 11
  · exact hwords 12

/-- One native emitter and factor precede every runtime layout, operation and width. Its result
is the faithful typed label, and its combined currency charges all label staging and control. -/
theorem realizes_method : Realizes .exact method methodWords labelWords methodSafe methodWork := by
  have henqueue := (MemoryQueueDispatch.realizes_enqueue 0 0).reindex
    (fun d : Layouts × Queue.QueueOp ℕ => (d.1, opWords d.2 1)) methodWords
    ![0, 1, 2, 3, 4, 5, 6, 7, 9] (by intro d i; fin_cases i <;> rfl)
  have hdequeue := (MemoryQueueDispatch.realizes_dequeue 0 0).reindex
    (fun d : Layouts × Queue.QueueOp ℕ => d.1) methodWords
    ![0, 1, 2, 3, 4, 5, 6, 7] (by intro d i; fin_cases i <;> rfl)
  have hpos := henqueue.bind enqueueLabel
  have hneg := hdequeue.bind dequeueLabel
  have h := Realizes.branch (.eq 8 10) hpos hneg
  have hp : (fun d : Layouts × Queue.QueueOp ℕ =>
      if test (.eq 8 10) (methodWords d) then
        (Queue.Memory.memMethods d.1.1 d.1.2 0 0 (.enqueue (opWords d.2 1))).bind
          (fun _ => pure (⟨.enqueue (opWords d.2 1), ()⟩ : Label))
      else (Queue.Memory.memMethods d.1.1 d.1.2 0 0 .dequeue).bind
        (fun a => pure (⟨.dequeue, a⟩ : Label))) = method := by
    funext d
    rcases d with ⟨L, op⟩
    cases op with
    | enqueue v =>
      change (Queue.Memory.memMethods L.1 L.2 0 0 (.enqueue v)).bind
        (fun _ => pure (⟨.enqueue v, ()⟩ : Label)) = _
      rfl
    | dequeue => rfl
  rw [hp] at h
  apply h.consequence
  · intro w d s hwords hmem hsafe
    rcases d with ⟨L, op⟩
    cases op with
    | enqueue v =>
      change (L.2.Valid w L.2.items.length ∧ Stack.Memory.Inv L.2 s ∧
        s.mem L.2.count.base < L.2.items.length) ∧ True
      exact ⟨hsafe, trivial⟩
    | dequeue =>
      change MemoryQueueDispatch.dequeueSafe w L s ∧ L.1.Valid w L.1.items.length
      exact ⟨hsafe, hsafe.1⟩
  · intro d s
    rcases d with ⟨L, op⟩
    cases op with
    | enqueue v => change 19 + 2 ≤ 21; omega
    | dequeue => change MemoryQueueDispatch.dequeueWork L s + 8 + 1 + 2 ≤
        MemoryQueueDispatch.dequeueWork L s + 11; omega

end Cslib.WordRAM.Realization.MemoryQueueMethod
