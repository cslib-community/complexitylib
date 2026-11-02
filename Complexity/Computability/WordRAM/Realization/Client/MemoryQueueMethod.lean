/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueDispatch

/-!
# Uniform answer realization of both queue methods

Both complete stack layouts and the queue operation are runtime inputs. One native branch
selects the existing certified method. Enqueue returns `none` in the common `Option ℕ` carrier;
its observed answer is unit. Dequeue returns its actual optional word. The output never echoes
the operation or enqueue payload. The faithful option encoding distinguishes `none` from `some 0`
and retains maximum-word payloads unchanged.

The canonical source erases specification parameters `w = C = 0`; `method_source_eq` identifies
its body at every actual width and capacity. `answer` and `method_answer` connect the common
result to each operation's result type. The emitter and exchange constant precede every runtime
layout, base, capacity, operation and width. Native output staging and control remain charged.

## Main definitions

* `opWords`, `methodWords`: faithful operation and complete runtime argument encodings.
* `answer`: recover the operation-specific answer from the common optional-word result.
* `method`, `methodSafe`, `methodWork`: canonical source, actual path domain and local-work charge.

## Main results

* `realizes_method`: one realization handles every runtime layout and queue operation.
* `methodWork_le`: a uniform affine bound uses the rear-count expression for transfer fuel.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueMethod

open Cslib.DataStructure

private abbrev Layouts := Stack.Memory.Layout × Stack.Memory.Layout
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

/-- Recover a known operation's answer. Enqueue ignores the common result; dequeue retains it.
This semantic observation need not be injective and does not compute native output words. -/
def answer : (o : Queue.QueueOp ℕ) → Option ℕ → (Queue.queue ℕ).Result o
  | .enqueue _, _ => ()
  | .dequeue, a => a

/-- The actual queue method returns a common optional word, without an operation/payload echo. -/
def method (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) :
    Memory.Prog (Option ℕ) :=
  match d.2 with
  | .enqueue v => do
      let _ ← Queue.Memory.memMethods d.1.1 d.1.2 0 0 (.enqueue v)
      pure none
  | .dequeue => Queue.Memory.memMethods d.1.1 d.1.2 0 0 .dequeue

/-- Specification width/capacity do not change the computational memory-method body. -/
theorem method_source_eq
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (w C : ℕ) :
    method d = (match d.2 with
      | .enqueue v => do
          let _ ← Queue.Memory.memMethods d.1.1 d.1.2 w C (.enqueue v)
          pure none
      | .dequeue => Queue.Memory.memMethods d.1.1 d.1.2 w C .dequeue) := by
  rcases d with ⟨L, op⟩
  unfold method
  cases op with
  | enqueue v =>
    dsimp only
    rw [MemoryQueue.memMethods_enqueue, MemoryQueue.memMethods_enqueue]
  | dequeue =>
    dsimp only
    rw [MemoryQueue.memMethods_dequeue, MemoryQueue.memMethods_dequeue]

/-- Observing the common result preserves the exact original memory program and its history. -/
theorem method_answer
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (w C : ℕ) :
    (do let a ← method d; pure (answer d.2 a)) =
      Queue.Memory.memMethods d.1.1 d.1.2 w C d.2 := by
  rw [method_source_eq d w C]
  rcases d with ⟨L, op⟩
  cases op with
  | enqueue v =>
    change ((Queue.Memory.memMethods L.1 L.2 w C (.enqueue v)).bind
      (fun _ => pure none)).bind (fun _ => pure ()) = _
    rw [PFunctor.FreeM.bind_assoc]
    simp only [PFunctor.FreeM.pure_bind]
    have hunit : (fun _ : Unit => (pure () : Memory.Prog Unit)) = pure := by
      funext u
      cases u
      rfl
    rw [hunit]
    exact PFunctor.FreeM.bind_pure _
  | dequeue => exact bind_pure _

/-- The entry domain is the existing domain of the selected path, with memory admissibility
retained separately in `Realizes`. -/
def methodSafe (w : ℕ)
    (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ) (s : Memory.State) : Prop :=
  match d.2 with
  | .enqueue _ => d.1.2.Valid w d.1.2.items.length ∧ Stack.Memory.Inv d.1.2 s ∧
      s.mem d.1.2.count.base < d.1.2.items.length
  | .dequeue => MemoryQueueDispatch.dequeueSafe w d.1 s

/-- Enqueue pays four units for the two-word `none`, one bind and two dispatch units.
Dequeue reuses its faithful result vector, paying only the two dispatch units. -/
def methodWork (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ)
    (s : Memory.State) : ℕ :=
  match d.2 with
  | .enqueue _ => 17
  | .dequeue => MemoryQueueDispatch.dequeueWork d.1 s + 2

/-- A single affine estimate covers both operations without asserting a memory-only bound. -/
theorem methodWork_le (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Queue.QueueOp ℕ)
    (s : Memory.State) :
    methodWork d s ≤ 40 * MemoryQueueDispatch.dequeueFuel d.1 s + 71 := by
  rcases d with ⟨L, op⟩
  have h := MemoryQueueDispatch.dequeueWork_le L s
  cases op <;> dsimp only [methodWork] <;> omega

private def enqueueInput :=
  (methodWords.prodMap unitWords).trans (Fin.appendEquiv 11 0).toEmbedding

private def enqueueCoordinates : Fin 2 → (Fin 11 → ℕ) → ℕ := ![fun _ => 0, fun _ => 0]

private theorem enqueueAnswer :
    Realizes .exact (fun _ : (Layouts × Queue.QueueOp ℕ) × Unit => pure (none : Option ℕ))
      enqueueInput optionWords (fun _ _ _ => True) (fun _ _ => 4) := by
  have hc (i : Fin 2) : GlueComputes .exact (fun _ : Fin 11 → ℕ => True)
      (enqueueCoordinates i) (enqueueCoordinates i) 1 := by
    fin_cases i <;> exact GlueComputes.const 0 (fun _ _ => le_rfl)
  have h := Realizes.glueVector enqueueInput optionWords (fun _ => (none : Option ℕ))
    enqueueCoordinates enqueueCoordinates (fun _ => 1)
    (fun d i => by fin_cases i <;> rfl) hc
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s _ _ _
  exact ⟨trivial, fun i => by fin_cases i <;> exact fits_zero w⟩

/-- One emitter precedes every runtime input. Only the faithful common answer is returned;
all output staging, binding and operation dispatch is included in its local-work grading. -/
theorem realizes_method :
    Realizes .exact method methodWords optionWords methodSafe methodWork := by
  have henqueue := (MemoryQueueDispatch.realizes_enqueue 0 0).reindex
    (fun d : Layouts × Queue.QueueOp ℕ => (d.1, opWords d.2 1)) methodWords
    ![0, 1, 2, 3, 4, 5, 6, 7, 9] (by intro d i; fin_cases i <;> rfl)
  have hdequeue := (MemoryQueueDispatch.realizes_dequeue 0 0).reindex
    (fun d : Layouts × Queue.QueueOp ℕ => d.1) methodWords
    ![0, 1, 2, 3, 4, 5, 6, 7] (by intro d i; fin_cases i <;> rfl)
  have h := Realizes.branch (.eq 8 10) (henqueue.bind enqueueAnswer) hdequeue
  have hp : (fun d : Layouts × Queue.QueueOp ℕ =>
      if test (.eq 8 10) (methodWords d) then
        (Queue.Memory.memMethods d.1.1 d.1.2 0 0 (.enqueue (opWords d.2 1))).bind
          (fun _ => pure (none : Option ℕ))
      else Queue.Memory.memMethods d.1.1 d.1.2 0 0 .dequeue) = method := by
    funext d
    rcases d with ⟨L, op⟩
    cases op <;> rfl
  rw [hp] at h
  apply h.consequence
  · intro w d s _ _ hsafe
    rcases d with ⟨L, op⟩
    cases op with
    | enqueue v => exact ⟨hsafe, trivial⟩
    | dequeue => exact hsafe
  · intro d s
    rcases d with ⟨L, op⟩
    cases op with
    | enqueue v => change 10 + 4 + 1 + 2 ≤ 17; omega
    | dequeue => exact le_rfl

end Cslib.WordRAM.Realization.MemoryQueueMethod
