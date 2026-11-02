/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueue

/-!
# Native dispatch for the memory-oracle queue

The existing enqueue and dequeue methods consume both complete runtime stack layouts. The
dequeue branch tests a certified zero against the front-pop presence tag, so a payload equal to
one cannot be mistaken for an empty result. The fallback computes the complete transfer argument
encoding with certified vector glue before consuming the uniform transfer certificate.

The visible entry domains follow the actual intermediate memory states. Local work includes
argument staging, result copies, both dispatch alternatives and every bind; memory charges alone
do not account for this work. No source queue or stack method is changed.

## Main definitions

* `enqueueWords`: both runtime layouts followed by the enqueue payload.
* `dequeueSafe`, `dequeueWork`: actual-state domain and path-selected local-work ledger.

## Main results

* `realizes_enqueue`, `realizes_dequeue`: the existing complete queue methods have uniform
  native emitters.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueDispatch

open Cslib.DataStructure

private abbrev Layouts := Stack.Memory.Layout × Stack.Memory.Layout
private abbrev word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) := (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

private def append {δ α : Type} {k l : ℕ} (input : δ ↪ (Fin k → ℕ))
    (answer : α ↪ (Fin l → ℕ)) : δ × α ↪ (Fin (k + l) → ℕ) :=
  (input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding

/-- Both complete runtime layouts precede the unshifted payload. -/
def enqueueWords : ((Stack.Memory.Layout × Stack.Memory.Layout) × ℕ) ↪ (Fin 9 → ℕ) :=
  (MemoryQueue.layoutWords.prodMap (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
    (Fin.appendEquiv 8 1).toEmbedding

/-- The rear-size reply is read at the actual state after the initial front pop. -/
def dequeueFuel (L : Stack.Memory.Layout × Stack.Memory.Layout) (s : Memory.State) : ℕ :=
  (Memory.spec 0).clientResult ((Memory.spec 0).clientState s (Stack.Memory.pop L.1))
    (Stack.Memory.size L.2)

/-- Only the fallback requires the transfer's actual-state domain and the final front-pop
invariant. The memory-history admissibility premise of `Realizes` remains separate. -/
def dequeueSafe (w : ℕ) (L : Stack.Memory.Layout × Stack.Memory.Layout)
    (s : Memory.State) : Prop :=
  L.1.Valid w L.1.items.length ∧ Stack.Memory.Inv L.1 s ∧
    match (Memory.spec 0).clientResult s (Stack.Memory.pop L.1) with
    | some _ => True
    | none =>
      let mid := (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (Stack.Memory.pop L.1)) (Stack.Memory.size L.2)
      iterationSafe MemoryQueue.transferBody MemoryQueue.transferSafe w L (dequeueFuel L s)
        true mid ∧
      Stack.Memory.Inv L.1 ((Memory.spec 0).clientState mid
        (link (Stack.Memory.pairMethods L.1 L.2 0 0) (Queue.transfer (dequeueFuel L s))))

/-- The immediate path pays 28 units. The fallback additionally pays forty units per actual
rear-size reply and a total constant allowance of 69, including transfer argument staging. -/
def dequeueWork (L : Stack.Memory.Layout × Stack.Memory.Layout) (s : Memory.State) : ℕ :=
  match (Memory.spec 0).clientResult s (Stack.Memory.pop L.1) with
  | some _ => 28
  | none => 40 * dequeueFuel L s + 69

/-- A convenient affine bound retains the actual queried fuel, even on the shorter path. -/
theorem dequeueWork_le (L : Stack.Memory.Layout × Stack.Memory.Layout) (s : Memory.State) :
    dequeueWork L s ≤ 40 * dequeueFuel L s + 69 := by
  unfold dequeueWork
  split <;> omega

/-- Enqueue consumes the rear stack's certified push, with all runtime words retained. -/
theorem realizes_enqueue (w C : ℕ) :
    Realizes .exact
      (fun d : (Stack.Memory.Layout × Stack.Memory.Layout) × ℕ =>
        Queue.Memory.memMethods d.1.1 d.1.2 w C (.enqueue d.2))
      enqueueWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => d.1.2.Valid w d.1.2.items.length ∧ Stack.Memory.Inv d.1.2 s ∧
        s.mem d.1.2.count.base < d.1.2.items.length) (fun _ _ => 10) := by
  have h := MemoryStack.realizes_push.reindex
    (fun d : Layouts × ℕ => (d.1.2, d.2)) enqueueWords ![4, 5, 6, 7, 8]
    (by intro d i; fin_cases i <;> rfl)
  simpa only [MemoryQueue.memMethods_enqueue] using h

private def replyInput := append MemoryQueue.layoutWords optionWords
private def zeroInput := append replyInput word
private def fuelInput := append zeroInput word
private def stagedInput := append fuelInput (MemoryQueue.transferWords MemoryQueue.layoutWords)
private def lastInput := append stagedInput unitWords

private theorem returnZero {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) :
    Realizes .exact (fun _ => pure 0) input word
      (fun _ _ _ => True) (fun _ _ => 1) := by
  have h := Realizes.glue input
    (GlueComputes.const (B := .exact) (P := fun _ => True) (bound := fun _ => 0)
      0 (fun _ _ => le_rfl))
  exact h.consequence (fun w _ _ _ _ _ => ⟨trivial, fits_zero w⟩) (fun _ _ => le_rfl)

private theorem returnOption {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ))
    (f : δ → Option ℕ) (ix : Fin 2 → Fin k)
    (hf : ∀ d i, optionWords (f d) i = input d (ix i)) :
    Realizes .exact (fun d => pure (f d)) input optionWords
      (fun _ _ _ => True) (fun _ _ => 4) := by
  have h := Realizes.glueVector (B := .exact) input optionWords f
    (fun i v => v (ix i)) (fun i v => v (ix i)) (fun _ => 1) hf
    (P := fun _ => True) (fun i => GlueComputes.proj (ix i) (fun _ _ => le_rfl))
  exact h.consequence (fun _ _ _ hwords _ _ => ⟨trivial, fun i => hwords (ix i)⟩)
    (fun _ _ => by simp)

private def stageCoordinates (i : Fin 11) (v : Fin 12 → ℕ) : ℕ :=
  Fin.append (Fin.append (fun j : Fin 8 => v (Fin.castLE (by omega) j))
    (boolWords true)) (fun _ : Fin 1 => v 11) i

private theorem stageTransfer :
    Realizes .exact (fun d : ((Layouts × Option ℕ) × ℕ) × ℕ => pure (d.1.1.1, d.2))
      fuelInput (MemoryQueue.transferWords MemoryQueue.layoutWords)
      (fun w _ _ => Fits w 1) (fun _ _ => 22) := by
  have hc (i : Fin 11) : GlueComputes .exact (fun _ : Fin 12 → ℕ => True)
      (stageCoordinates i) (stageCoordinates i) 1 := by
    fin_cases i
    · exact GlueComputes.proj 0 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 1 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 2 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 3 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 4 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 5 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 6 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 7 (fun _ _ => le_rfl)
    · exact GlueComputes.const 1 (fun _ _ => le_rfl)
    · exact GlueComputes.const 0 (fun _ _ => le_rfl)
    · exact GlueComputes.proj 11 (fun _ _ => le_rfl)
  have h := Realizes.glueVector fuelInput (MemoryQueue.transferWords MemoryQueue.layoutWords)
    (fun d => (d.1.1.1, d.2)) stageCoordinates stageCoordinates (fun _ => 1)
    (fun _ i => by fin_cases i <;> rfl) hc
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s hwords _ h1
  refine ⟨trivial, fun i => ?_⟩
  fin_cases i
  · exact hwords 0
  · exact hwords 1
  · exact hwords 2
  · exact hwords 3
  · exact hwords 4
  · exact hwords 5
  · exact hwords 6
  · exact hwords 7
  · exact h1
  · exact fits_zero w
  · exact hwords 11

private def afterSizeSafe (w : ℕ) (L : Layouts) (n : ℕ) (s : Memory.State) : Prop :=
  Fits w 1 ∧ iterationSafe MemoryQueue.transferBody MemoryQueue.transferSafe w L n true s ∧
    L.1.Valid w L.1.items.length ∧ Stack.Memory.Inv L.1 ((Memory.spec 0).clientState s
      (link (Stack.Memory.pairMethods L.1 L.2 0 0) (Queue.transfer n)))

/-- The complete existing dequeue has one emitter before either layout, any payload, the queried
rear count and every intermediate state. Its local-work ledger includes the pure staging paths. -/
theorem realizes_dequeue (w C : ℕ) :
    Realizes .exact (fun L : Stack.Memory.Layout × Stack.Memory.Layout =>
      Queue.Memory.memMethods L.1 L.2 w C .dequeue)
      MemoryQueue.layoutWords optionWords dequeueSafe dequeueWork := by
  have hfirst := MemoryStack.realizes_pop.reindex (fun L : Layouts => L.1)
    MemoryQueue.layoutWords ![0, 1, 2, 3] (by intro d i; fin_cases i <;> rfl)
  have hsize := MemoryStack.realizes_size.reindex
    (fun d : (Layouts × Option ℕ) × ℕ => d.1.1.2) zeroInput ![4, 5, 6, 7]
    (by intro d i; fin_cases i <;> rfl)
  have htransfer := (MemoryQueue.realizes_source_transfer w C).reindex
    (fun d : (((Layouts × Option ℕ) × ℕ) × ℕ) × (Layouts × ℕ) => d.2)
    stagedInput (Fin.natAdd 12) (by
      intro d i
      change MemoryQueue.transferWords MemoryQueue.layoutWords d.2 i =
        Fin.append (fuelInput d.1) (MemoryQueue.transferWords MemoryQueue.layoutWords d.2)
          (Fin.natAdd 12 i)
      rw [Fin.append_right])
  have hlast := MemoryStack.realizes_pop.reindex
    (fun d : ((((Layouts × Option ℕ) × ℕ) × ℕ) × (Layouts × ℕ)) × Unit => d.1.2.1.1)
    lastInput ![12, 13, 14, 15] (by intro d i; fin_cases i <;> rfl)
  have hstage := (stageTransfer.bind (htransfer.bind hlast)).consequence
    (safe' := fun w d s => afterSizeSafe w d.1.1.1 d.2 s)
    (work' := fun d _ => 40 * d.2 + 44)
    (by
      intro ww d s _ _ hh
      simpa only [afterSizeSafe, StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
        StateTransitionSpec.runClient_pure, StateTransitionSpec.runClient_pure',
        MemoryQueue.transfer_eq_iterate] using hh)
    (by intro d s; change 22 + (40 * d.2 + 1 + 19 + 1) + 1 ≤ _; omega)
  have hnone := (hsize.bind hstage).consequence
    (safe' := fun w d s => afterSizeSafe w d.1.1
      ((Memory.spec 0).clientResult s (Stack.Memory.size d.1.1.2))
      ((Memory.spec 0).clientState s (Stack.Memory.size d.1.1.2)))
    (work' := fun d s => 40 * (Memory.spec 0).clientResult s (Stack.Memory.size d.1.1.2) + 45)
    (fun _ _ _ _ _ h => ⟨trivial, h⟩) (by
      intro d s
      change 0 + (40 * (Memory.spec 0).clientResult s (Stack.Memory.size d.1.1.2) + 44) + 1 ≤ _
      omega)
  have hsome := returnOption zeroInput (fun d => d.1.2) ![8, 9]
    (by intro d i; fin_cases i <;> rfl)
  have hbranch := Realizes.branch (.eq 8 10) hnone hsome
  have h := hfirst.bind ((returnZero replyInput).bind hbranch)
  have hprogram :
      (fun L : Layouts => (Stack.Memory.pop L.1).bind (fun a =>
        (pure 0 : Memory.Prog ℕ).bind (fun z =>
          if test (.eq 8 10) (zeroInput ((L, a), z)) then
            (Stack.Memory.size L.2).bind (fun n =>
              (link (Stack.Memory.pairMethods L.1 L.2 w C) (Queue.transfer n)).bind
                (fun _ => Stack.Memory.pop L.1))
          else pure a))) =
      (fun L : Layouts => Queue.Memory.memMethods L.1 L.2 w C .dequeue) := by
    funext L
    rw [MemoryQueue.memMethods_dequeue]
    congr 1
    funext a
    cases a with
    | some v => rfl
    | none =>
      change (Stack.Memory.size L.2).bind (fun n =>
        (link (Stack.Memory.pairMethods L.1 L.2 w C) (Queue.transfer n)).bind
          (fun _ => Stack.Memory.pop L.1)) = _
      congr 1
      funext n
      rw [MemoryQueue.transfer_eq_iterate]
      simp only [PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
  simp only [PFunctor.FreeM.bind_eq_bind, pure_bind] at h hprogram
  rw [hprogram] at h
  apply h.consequence
  · intro w L s hwords _ ⟨hL, hInv, hnext⟩
    have h1 : Fits w 1 := hL.count_length ▸ hwords 1
    refine ⟨⟨hL, hInv⟩, trivial, ?_⟩
    cases ha : (Memory.spec 0).clientResult s (Stack.Memory.pop L.1) with
    | some v =>
      change (if 1 = 0 then _ else True)
      trivial
    | none =>
      simp only [ha] at hnext
      change afterSizeSafe w L (dequeueFuel L s)
        ((Memory.spec 0).clientState ((Memory.spec 0).clientState s (Stack.Memory.pop L.1))
          (Stack.Memory.size L.2))
      exact ⟨h1, hnext.1, hL, hnext.2⟩
  · intro L s
    unfold dequeueWork
    cases ha : (Memory.spec 0).clientResult s (Stack.Memory.pop L.1) with
    | some v =>
      change 19 + (1 + (4 + 2) + 1) + 1 ≤ 28
      omega
    | none =>
      change 19 + (1 + (40 * dequeueFuel L s + 45 + 2) + 1) + 1 ≤
        40 * dequeueFuel L s + 69
      omega

end Cslib.WordRAM.Realization.MemoryQueueDispatch
