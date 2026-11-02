/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueMethod
public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueFrame
public import Complexity.Computability.WordRAM.Realization.Client.MemoryQueueInit
public import Complexity.Computability.WordRAM.Realization.Module

/-!
# A framed native queue from the memory-client kernel

The existing semantic queue invariant discharges the complete native method's actual-state
domains. The global emitter consumes runtime layouts and the typed operation, so its code,
register count, scratch and exchange factor precede the queue's base, capacity and word width.
The result representation uses a presence tag and an unshifted word, including the largest
fitting payload.

`implementation` fills the existing `SubroutineBase` and `WordRAM.StateTransitionImpl` APIs.
Its representation adds bounded native data and persistent layout registers to the original
M1a queue representation. Finite-block support, argument encoding, typed decoding, fresh
initialization and the full method memory footprint are proved at this boundary.

The certified method work satisfies `G ≤ 7 M + 80` on queue states. Scaling the existing
nine-memory-unit queue inequality gives an amortized native body charge `153 * factor` and a
potential
`48 * factor * rearCount`. The existing flat-call API adds its trailing halt separately.
Register argument delivery follows that API's `prepareRegs` convention; arbitrary host-client
pure computations are not part of this operation-sequence clock.

Initialization reserves `2 * (C + 1)` cells at an arbitrary base. Its fresh native body costs
thirteen steps under the existing zero-block hypothesis. The reusable dirty-clear body costs
at most `4 * space + 19`; it zeros the entire owned block. These local framed initializers are
separate from the source `allocLayout` sequence, which clears only count cells and reserves
dirty item arrays. No whole-client allocation cost is absorbed into the method charge.

## Main definitions

* `frontLayout`, `rearLayout`, `space`: the consecutive two-stack storage layout.
* `program`: one global native code body and register ABI.
* `implementation`: the existing framed queue certificate, with explicit initialization bounds.

## Main results

* `dequeue_safe`, `method_safe`: existing invariants discharge actual runtime domains.
* `method_work_bound`, `method_pay`: all memory, glue, dispatch and result-staging work is paid.
* `implementation_rep_iff`: the precise local representation and persistent register condition.
* `implementation_charge`, `implementation_initTime`, `implementation_decode_dequeue`: usable
  resource and typed-result facts without unfolding private certificate plumbing.

## References

The semantic programs and their queue potential are reused unchanged from the two-stack queue
of [CLRS2009], Exercise 10.1-6 and Chapter 17. The native composition and its explicit local-work
accounting are original infrastructure over those existing programs.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueAdapter

open Cslib.DataStructure

/-- The front count cell and item array, relative to the queue's runtime base. -/
def frontLayout (base C : ℕ) : Stack.Memory.Layout := ⟨⟨base, 1⟩, ⟨base + 1, C⟩⟩

/-- The rear follows the complete front layout. -/
def rearLayout (base C : ℕ) : Stack.Memory.Layout :=
  ⟨⟨base + 1 + C, 1⟩, ⟨base + 1 + C + 1, C⟩⟩

/-- The two count cells and two capacity-sized arrays. -/
def space (C : ℕ) : ℕ := 2 * (C + 1)

/-- A fitting end address supplies the capacity fit and two disjoint well-formed layouts. -/
theorem layouts_valid {w base C : ℕ} (hf : Fits w (base + space C)) :
    (frontLayout base C).Valid w C ∧ (rearLayout base C).Valid w C ∧
      Disjoint (frontLayout base C).footprint (rearLayout base C).footprint := by
  have hC : Fits w C := hf.of_le (by unfold space; omega)
  refine ⟨⟨rfl, ?_, rfl, hC⟩, ⟨rfl, ?_, rfl, hC⟩, ?_⟩
  · simp [frontLayout, Block.Owns]
  · simp [rearLayout, Block.Owns]
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Stack.Memory.Layout.footprint, frontLayout, rearLayout, Finset.mem_union,
      Block.mem_footprint, Block.Owns] at ha hb
    omega

/-- Exactly the existing single owned block is occupied by the two layouts. -/
theorem layouts_footprint (base C : ℕ) :
    (frontLayout base C).footprint ∪ (rearLayout base C).footprint =
      (Block.mk base (space C)).footprint := by
  ext a
  simp only [Stack.Memory.Layout.footprint, frontLayout, rearLayout, Finset.mem_union,
    Block.mem_footprint, Block.Owns, space]
  omega

/-- A zeroed owned queue span represents the empty queue. The proof reads only its count cells;
no global well-formedness assumption is required for an empty list. -/
theorem empty_rep {w base C : ℕ} (hf : Fits w (base + space C)) (e : Memory.State)
    (hfront : e.frontier = base + space C)
    (hzero : ∀ a ∈ (Block.mk base (space C)).footprint, e.mem a = 0) :
    (Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
      (layouts_valid hf).2.2).toModule.rep [] e := by
  have h₀ : e.mem base = 0 := hzero base (by
    simp only [Block.mem_footprint, Block.Owns, space]
    omega)
  have h₁ : e.mem (base + 1 + C) = 0 := hzero (base + 1 + C) (by
    simp only [Block.mem_footprint, Block.Owns, space]
    omega)
  have hi₀ : Stack.Memory.Inv (frontLayout base C) e := by
    refine ⟨?_, ?_, ?_⟩
    · change base + 1 ≤ e.frontier
      rw [hfront]
      unfold space
      omega
    · change base + 1 + C ≤ e.frontier
      rw [hfront]
      unfold space
      omega
    · change e.mem base ≤ C
      rw [h₀]
      exact Nat.zero_le C
  have hi₁ : Stack.Memory.Inv (rearLayout base C) e := by
    refine ⟨?_, ?_, ?_⟩
    · change base + 1 + C + 1 ≤ e.frontier
      rw [hfront]
      unfold space
      omega
    · change base + 1 + C + 1 + C ≤ e.frontier
      rw [hfront]
      unfold space
      omega
    · change e.mem (base + 1 + C) ≤ C
      rw [h₁]
      exact Nat.zero_le C
  have ha₀ : Stack.Memory.abs (frontLayout base C) e = [] := by
    simp only [Stack.Memory.abs, frontLayout, h₀, Block.entries_zero, List.reverse_nil]
  have ha₁ : Stack.Memory.abs (rearLayout base C) e = [] := by
    simp only [Stack.Memory.abs, rearLayout, h₁, Block.entries_zero, List.reverse_nil]
  change ((Stack.Memory.Inv (frontLayout base C) e ∧
    Stack.Memory.Inv (rearLayout base C) e) ∧
    Queue.Memory.Inv w C (Queue.WordRAM.contents
      (Stack.Memory.abs (frontLayout base C) e, Stack.Memory.abs (rearLayout base C) e))) ∧
    Queue.WordRAM.contents
      (Stack.Memory.abs (frontLayout base C) e, Stack.Memory.abs (rearLayout base C) e) = []
  refine ⟨⟨⟨hi₀, hi₁⟩, ?_⟩, ?_⟩
  · rw [ha₀, ha₁]
    exact ⟨by simp [Queue.WordRAM.contents], by simp [Queue.WordRAM.contents]⟩
  · rw [ha₀, ha₁]
    rfl

/-- Disjoint allocated stacks within total capacity satisfy the exact native dequeue domain.
On an empty front, its pop and the rear-size query preserve the state, and the generic transfer
invariant supplies both the reached loop domains and the final front-pop invariant. -/
theorem dequeue_safe {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    MemoryQueueDispatch.dequeueSafe w (L₁, L₂) s := by
  change L₁.Valid w L₁.items.length ∧ Stack.Memory.Inv L₁ s ∧ _
  refine ⟨by simpa only [h₁.items_length] using h₁, hs₁, ?_⟩
  by_cases h0 : s.mem L₁.count.base = 0
  · have hpop := Stack.Memory.runClient_pop_of_eq_zero (w := 0) L₁ s h0
    have hresult : (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) = none :=
      congrArg Prod.fst hpop
    rw [hresult]
    have hmid : (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s (Stack.Memory.pop L₁)) (Stack.Memory.size L₂) = s := by
      simp only [StateTransitionSpec.clientState, hpop, Stack.Memory.runClient_size]
    have hfuel : MemoryQueueDispatch.dequeueFuel (L₁, L₂) s = s.mem L₂.count.base := by
      simp only [MemoryQueueDispatch.dequeueFuel, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, hpop, Stack.Memory.runClient_size]
    rw [hmid, hfuel]
    obtain ⟨hsafe, _, hfront, _, _, _, _⟩ :=
      MemoryQueue.transfer_invariant h₁ h₂ hd hw hs₁ hs₂ rfl hlen
    refine ⟨hsafe, ?_⟩
    have hstate : (Memory.spec 0).clientState s
        (link (Stack.Memory.pairMethods L₁ L₂ 0 0) (Queue.transfer (s.mem L₂.count.base))) =
        (Memory.spec 0).clientState s
          (iterate MemoryQueue.transferBody (L₁, L₂) (s.mem L₂.count.base) true) := by
      rw [MemoryQueue.transfer_eq_iterate]
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
      rfl
    exact hstate.symm ▸ hfront
  · have hpop := Stack.Memory.runClient_pop_of_pos (w := 0) L₁ s h0
    have hresult : (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) =
        some (s.mem (L₁.items.base + (s.mem L₁.count.base - 1))) := congrArg Prod.fst hpop
    rw [hresult]
    trivial

/-- On the fallback path the complete source dequeue pays at least the six memory units for
each transferred rear item, in addition to its other queries. -/
theorem dequeue_cost_ge_transfer {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C)
    (h0 : s.mem L₁.count.base = 0) :
    6 * s.mem L₂.count.base ≤
      memoryCost (Queue.Memory.memMethods L₁ L₂ w C .dequeue) s := by
  have hpop := Stack.Memory.runClient_pop_of_eq_zero (w := 0) L₁ s h0
  have hresult : (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) = none :=
    congrArg Prod.fst hpop
  have hstate : (Memory.spec 0).clientState s (Stack.Memory.pop L₁) = s :=
    congrArg (fun t => t.2.1) hpop
  obtain ⟨_, _, _, _, _, _, hcost⟩ :=
    MemoryQueue.transfer_invariant h₁ h₂ hd hw hs₁ hs₂ rfl hlen
  rw [MemoryQueue.memMethods_dequeue]
  change _ ≤ memoryCost ((Stack.Memory.pop L₁).bind _) s
  rw [memoryCost_bind, hresult, hstate]
  change _ ≤ memoryCost (Stack.Memory.pop L₁) s + memoryCost
    ((Stack.Memory.size L₂).bind (fun n => (iterate MemoryQueue.transferBody
      (L₁, L₂) n true).bind (fun _ => Stack.Memory.pop L₁))) s
  rw [memoryCost_bind]
  change _ ≤ memoryCost (Stack.Memory.pop L₁) s +
    (memoryCost (Stack.Memory.size L₂) s + memoryCost ((iterate MemoryQueue.transferBody
      (L₁, L₂) (s.mem L₂.count.base) true).bind (fun _ => Stack.Memory.pop L₁)) s)
  rw [memoryCost_bind, hcost]
  omega

/-- The dispatch's certified local work is paid by the actual source memory cost under the
queue storage invariants. The bound keeps the explicit constant for short and empty paths. -/
theorem dequeue_work_bound {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    MemoryQueueDispatch.dequeueWork (L₁, L₂) s ≤
      7 * memoryCost (Queue.Memory.memMethods L₁ L₂ w C .dequeue) s + 69 := by
  by_cases h0 : s.mem L₁.count.base = 0
  · have hpop := Stack.Memory.runClient_pop_of_eq_zero (w := 0) L₁ s h0
    have hcost := dequeue_cost_ge_transfer h₁ h₂ hd hw hs₁ hs₂ hlen h0
    change (match (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) with
      | some _ => 28
      | none => 40 * MemoryQueueDispatch.dequeueFuel (L₁, L₂) s + 69) ≤ _
    have hresult : (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) = none :=
      congrArg Prod.fst hpop
    rw [hresult]
    have hfuel : MemoryQueueDispatch.dequeueFuel (L₁, L₂) s = s.mem L₂.count.base := by
      simp only [MemoryQueueDispatch.dequeueFuel, StateTransitionSpec.clientResult,
        StateTransitionSpec.clientState, hpop, Stack.Memory.runClient_size]
    rw [hfuel]
    dsimp only
    nlinarith only [hcost]
  · have hpop := Stack.Memory.runClient_pop_of_pos (w := 0) L₁ s h0
    have hresult : (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) =
        some (s.mem (L₁.items.base + (s.mem L₁.count.base - 1))) := congrArg Prod.fst hpop
    change (match (Memory.spec 0).clientResult s (Stack.Memory.pop L₁) with
      | some _ => 28
      | none => 40 * MemoryQueueDispatch.dequeueFuel (L₁, L₂) s + 69) ≤ _
    rw [hresult]
    dsimp only
    omega

/-- The composite's storage invariant supplies the two component invariants and total count
bound. This unfolds only the existing composed refinement, not a replacement queue model. -/
theorem invariant_fields {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hi : (Queue.Memory.memRefinement h₁ h₂ hd).inv s) :
    Stack.Memory.Inv L₁ s ∧ Stack.Memory.Inv L₂ s ∧
      s.mem L₁.count.base + s.mem L₂.count.base ≤ C := by
  change (Stack.Memory.Inv L₁ s ∧ Stack.Memory.Inv L₂ s) ∧
    Queue.Memory.Inv w C (Queue.WordRAM.contents (Stack.Memory.abs L₁ s, Stack.Memory.abs L₂ s))
    at hi
  refine ⟨hi.1.1, hi.1.2, ?_⟩
  have h := hi.2.length_le
  simpa only [Queue.WordRAM.contents, List.length_append, List.length_reverse,
    Stack.Memory.length_abs] using h

/-- The existing composite queue invariant and an admissible operation discharge the domain of
one global native method certificate before any runtime layout is selected. -/
theorem method_safe {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hi : (Queue.Memory.memRefinement h₁ h₂ hd).inv s) (o : Queue.QueueOp ℕ)
    (hv : (Queue.WordRAM.spec w C).valid ((Queue.Memory.memRefinement h₁ h₂ hd).abs s) o) :
    MemoryQueueMethod.methodSafe w ((L₁, L₂), o) s := by
  obtain ⟨hs₁, hs₂, hlen⟩ := invariant_fields h₁ h₂ hd hi
  cases o with
  | enqueue v =>
    change ((Stack.Memory.abs L₁ s) ++ (Stack.Memory.abs L₂ s).reverse).length < C ∧ Fits w v
      at hv
    simp only [List.length_append, List.length_reverse, Stack.Memory.length_abs] at hv
    exact ⟨by simpa only [h₂.items_length] using h₂, hs₂,
      by simpa only [h₂.items_length] using (show s.mem L₂.count.base < C by omega)⟩
  | dequeue => exact dequeue_safe h₁ h₂ hd hw hs₁ hs₂ hlen

private theorem method_memoryCost (L₁ L₂ : Stack.Memory.Layout) (w C : ℕ) (o : Queue.QueueOp ℕ)
    (s : Memory.State) :
    memoryCost (MemoryQueueMethod.method ((L₁, L₂), o)) s =
      memoryCost (Queue.Memory.memMethods L₁ L₂ w C o) s := by
  rw [MemoryQueueMethod.method_source_eq ((L₁, L₂), o) w C]
  change memoryCost ((Queue.Memory.memMethods L₁ L₂ w C o).bind _) s = _
  rw [memoryCost_bind]
  rfl

/-- The global method's actual grading, including typed-result staging and operation dispatch,
is uniformly dominated on queue states. The constant 80 is retained on empty and short paths. -/
theorem method_work_bound {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hi : (Queue.Memory.memRefinement h₁ h₂ hd).inv s) (o : Queue.QueueOp ℕ) :
    MemoryQueueMethod.methodWork ((L₁, L₂), o) s ≤
      7 * memoryCost (MemoryQueueMethod.method ((L₁, L₂), o)) s + 80 := by
  obtain ⟨hs₁, hs₂, hlen⟩ := invariant_fields h₁ h₂ hd hi
  rw [method_memoryCost L₁ L₂ w C o s]
  cases o with
  | enqueue v => change 21 ≤ _; omega
  | dequeue =>
    have h := dequeue_work_bound h₁ h₂ hd hw hs₁ hs₂ hlen
    change MemoryQueueDispatch.dequeueWork (L₁, L₂) s + 11 ≤ _
    omega

private theorem totalCost_width (w : ℕ) (os : List Memory.Op) (s : Memory.State) :
    (Memory.spec w).totalCost Memory.charge s os =
      (Memory.spec 0).totalCost Memory.charge s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simpa only [StateTransitionSpec.totalCost_cons] using
      congrArg (Memory.charge s o + ·) (ih (Memory.step s o).1)

/-- The existing memory amortization lifts to the global native certificate's complete grading.
The factor is selected globally before runtime layouts; the resulting potential and charge
retain all memory, glue, result-staging and dispatch work. -/
theorem method_pay {L₁ L₂ : Stack.Memory.Layout} {w C : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hi : (Queue.Memory.memRefinement h₁ h₂ hd).inv s) (o : Queue.QueueOp ℕ)
    (hv : (Queue.WordRAM.spec w C).valid ((Queue.Memory.memRefinement h₁ h₂ hd).abs s) o)
    (factor : ℕ) :
    factor * (memoryCost (MemoryQueueMethod.method ((L₁, L₂), o)) s +
        MemoryQueueMethod.methodWork ((L₁, L₂), o) s + 1) +
        48 * factor * ((Memory.spec 0).clientState s
          (MemoryQueueMethod.method ((L₁, L₂), o))).mem L₂.count.base ≤
      153 * factor + 48 * factor * s.mem L₂.count.base := by
  let M := Queue.Memory.memRefinement h₁ h₂ hd
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    (M.valid o hi hv)
  have hpay := (Queue.Memory.mem_amortized h₁ h₂ hd).step o hi hv
    ((Memory.spec w).clientRun_canonical s _ hvalid)
  rw [StateTransitionSpec.totalCostTranscript_canonicalTranscript] at hpay
  change (Memory.spec w).totalCost Memory.charge s
      ((Memory.spec w).clientHistory s (M.methods o)) +
      6 * (Stack.Memory.abs L₂ ((Memory.spec w).clientState s (M.methods o))).length ≤
    9 + 6 * (Stack.Memory.abs L₂ s).length at hpay
  have hm : M.methods = Queue.Memory.memMethods L₁ L₂ w C :=
    Queue.Memory.memRefinement_methods h₁ h₂ hd
  rw [hm, clientState_width w] at hpay
  have hhistory : (Memory.spec w).clientHistory s (Queue.Memory.memMethods L₁ L₂ w C o) =
      (Memory.spec 0).clientHistory s (Queue.Memory.memMethods L₁ L₂ w C o) :=
    congrArg (fun t => t.2.2) (runClient_width w (Queue.Memory.memMethods L₁ L₂ w C o) s)
  rw [hhistory, totalCost_width w] at hpay
  change memoryCost (Queue.Memory.memMethods L₁ L₂ w C o) s +
      6 * (Stack.Memory.abs L₂ ((Memory.spec 0).clientState s
        (Queue.Memory.memMethods L₁ L₂ w C o))).length ≤
    9 + 6 * (Stack.Memory.abs L₂ s).length at hpay
  have hstate : (Memory.spec 0).clientState s (MemoryQueueMethod.method ((L₁, L₂), o)) =
      (Memory.spec 0).clientState s (Queue.Memory.memMethods L₁ L₂ w C o) := by
    rw [MemoryQueueMethod.method_source_eq ((L₁, L₂), o) w C]
    change (Memory.spec 0).clientState s ((Queue.Memory.memMethods L₁ L₂ w C o).bind _) = _
    simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
    rfl
  rw [← method_memoryCost L₁ L₂ w C o s, ← hstate] at hpay
  simp only [Stack.Memory.length_abs] at hpay
  have h := scaled_potential_pay
    (memoryCost (MemoryQueueMethod.method ((L₁, L₂), o)) s)
    (MemoryQueueMethod.methodWork ((L₁, L₂), o) s)
    (factor * (memoryCost (MemoryQueueMethod.method ((L₁, L₂), o)) s +
      MemoryQueueMethod.methodWork ((L₁, L₂), o) s + 1))
    (6 * s.mem L₂.count.base)
    (6 * ((Memory.spec 0).clientState s
      (MemoryQueueMethod.method ((L₁, L₂), o))).mem L₂.count.base)
    9 factor 7 80 le_rfl (method_work_bound h₁ h₂ hd hw hi o) hpay
  convert h using 1 <;> ring

/-- The register count is fixed by the global method certificate, before base, capacity or width. -/
noncomputable def registers : ℕ := 16 + (4 + MemoryQueueMethod.realizes_method.scratchSize + 1)

/-- The fixed ABI reserves the first sixteen registers; the global method's scratch follows. -/
noncomputable def register : Fin 16 ↪ Fin registers where
  toFun i := ⟨i.val, by have := i.isLt; unfold registers; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin registers => x.val) h

/-- Source registers are the fixed eleven-word global method ABI. -/
noncomputable def source : Fin 11 → Fin registers :=
  fun i => register (Fin.castLE (by decide) i)

/-- The complete output and scratch bank follows the persistent ABI and controls. -/
noncomputable def scratch :
    Fin (4 + MemoryQueueMethod.realizes_method.scratchSize + 1) → Fin registers :=
  fun i => ⟨16 + i.val, by have := i.isLt; unfold registers; omega⟩

/-- The four typed-label words occupy the first four result-bank registers. -/
noncomputable def outputRegister (i : Fin 4) : Fin registers :=
  scratch (Fin.castAdd (MemoryQueueMethod.realizes_method.scratchSize + 1) i)

/-- One fixed code body and initialization ABI for all runtime bases and capacities. The first
three operation words alone are caller inputs; all eight layout words are persistent state. -/
noncomputable def program : SubroutineCode .exact registers 1 where
  allocSpan := MemoryQueueInit.spanCode register
  initSetup := MemoryQueueInit.setupCode register
  code := MemoryQueueMethod.realizes_method.code (register 11) source scratch
  frontierReg := register 11
  baseReg := register 12
  initParams _ := register 3
  curReg := register 13
  zeroReg := register 14
  oneReg := register 15
  incCur := .exactBin .add (register 13) (register 13) (register 15)
  input i := decide (8 ≤ i.val ∧ i.val < 11)
  output := outputRegister 3

private def semanticModule (w base C : ℕ) (hf : Fits w (base + space C)) :
    Module (Queue.WordRAM.spec w C) (Memory.spec w) :=
  (Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
    (layouts_valid hf).2.2).toModule

private noncomputable def layoutMatch (base C : ℕ) (regs : Fin registers → ℕ) : Prop :=
  ∀ i : Fin 8, regs (register (Fin.castLE (by decide) i)) =
    MemoryQueue.layoutWords (frontLayout base C, rearLayout base C) i

private noncomputable def representation (w base C : ℕ) (hf : Fits w (base + space C))
    (q : List ℕ) (x : Data registers) : Prop :=
  x.Bounded w ∧ layoutMatch base C x.regs ∧
    (semanticModule w base C hf).rep q (memoryState (register 11) x)

private noncomputable def operationMatch (o : Queue.QueueOp ℕ) (regs : Fin registers → ℕ) : Prop :=
  ∀ i : Fin 3, regs (register (Fin.natAdd 8 i |>.castLE (by decide))) =
    MemoryQueueMethod.opWords o i

private noncomputable def encode (o : Queue.QueueOp ℕ) (i : Fin registers) : ℕ :=
  if h : 8 ≤ i.val ∧ i.val < 11 then
    MemoryQueueMethod.opWords o ⟨i.val - 8, by omega⟩ else 0

private noncomputable def decode : (o : Queue.QueueOp ℕ) →
    (Fin registers → ℕ) → Option ((Queue.WordRAM.spec 0 0).Result o)
  | .enqueue _, _ => some ()
  | .dequeue, regs =>
      some (if regs (outputRegister 2) = 0 then none else some (regs (outputRegister 3)))

private theorem scratch_injective : Function.Injective scratch := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  change 16 + i.val = 16 + j.val at this
  omega

private theorem source_scratch (i : Fin 11) (j) : source i ≠ scratch j := by
  intro h
  have := congrArg Fin.val h
  change i.val = 16 + j.val at this
  have := i.isLt
  omega

private theorem scratch_frontier (j) : scratch j ≠ register 11 := by
  intro h
  have := congrArg Fin.val h
  change 16 + j.val = 11 at this
  omega

private theorem source_frontier (i : Fin 11) : source i ≠ register 11 := by
  intro h
  have := congrArg Fin.val h
  change i.val = 11 at this
  have := i.isLt
  omega

private theorem layoutWords_relative (base C : ℕ) :
    MemoryQueue.layoutWords (frontLayout base C, rearLayout base C) =
      ![base, 1, base + 1, C, base + 1 + C, 1, base + 1 + C + 1, C] := by
  funext i
  fin_cases i <;> rfl

private theorem op_words_fit {w C : ℕ} {q : List ℕ} (h1 : Fits w 1) (o : Queue.QueueOp ℕ)
    (hv : (Queue.WordRAM.spec w C).valid q o) (i : Fin 3) :
    Fits w (MemoryQueueMethod.opWords o i) := by
  cases o with
  | enqueue v => fin_cases i <;> first | exact fits_zero w | exact hv.2
  | dequeue => fin_cases i <;> first | exact h1 | exact fits_zero w

private noncomputable def baseCertificate (w base C : ℕ) (hf : Fits w (base + space C)) :
    SubroutineBase program (Queue.WordRAM.spec w C).Result (Queue.WordRAM.spec w C).valid
      w base (fun _ => C) [] where
  space := space C
  spanTime := 6
  setupTime := 7
  initPotential := 0
  charge _ _ := 153 * MemoryQueueMethod.realizes_method.factor
  rep := representation w base C hf
  potential x := 48 * MemoryQueueMethod.realizes_method.factor * x.mem (base + 1 + C)
  encode := encode
  argMatch := operationMatch
  decode := decode
  bounded hr := hr.1
  arguments_fit := by
    intro q o hv i hi
    change decide (8 ≤ i.val ∧ i.val < 11) = true at hi
    have hh := of_decide_eq_true hi
    change Fits w (if h : 8 ≤ i.val ∧ i.val < 11 then
      MemoryQueueMethod.opWords o ⟨i.val - 8, by omega⟩ else 0)
    rw [dite_eq_left hh]
    exact op_words_fit (hf.of_le (by unfold space; omega)) o hv _
  encode_matches := by
    intro o regs i
    fin_cases i <;> simp [program, encode, register]
  rep_supported := by
    intro q x x' hregs hmem hbound hr
    rcases hr with ⟨hx, hLayout, hM⟩
    have hf' : (memoryState (register 11) x).frontier ≤
        (memoryState (register 11) x').frontier := by
      have h := hregs (register 11) (by simp [program, register])
      change x.regs (register 11) ≤ x'.regs (register 11)
      omega
    have hm' : ∀ a ∈ (frontLayout base C).footprint ∪ (rearLayout base C).footprint,
        (memoryState (register 11) x').mem a = (memoryState (register 11) x).mem a := by
      intro a ha
      rw [layouts_footprint] at ha
      exact hmem a ha
    have hInv := MemoryQueueFrame.inv_congr (layouts_valid hf).1 (layouts_valid hf).2.1
      (layouts_valid hf).2.2 hM.1 hm' hf'
    have hAbs := MemoryQueueFrame.abs_congr (layouts_valid hf).1 (layouts_valid hf).2.1
      (layouts_valid hf).2.2 hM.1 hm'
    refine ⟨hbound, ?_, hInv, hAbs.trans hM.2⟩
    intro i
    exact (hregs _ (by
      simp only [program]
      apply decide_eq_false_iff_not.mpr
      change ¬(8 ≤ i.val ∧ i.val < 11)
      have := i.isLt
      omega)).trans (hLayout i)
  potential_supported := by
    intro q x x' _ hmem _
    have h := hmem (base + 1 + C) (by
      simp only [Block.mem_footprint, Block.Owns, space]
      omega)
    rw [h]
  clear_nodup := by simp [program, register]
  params_not_clear j := by simp [program, register]
  incCur_eval := by
    intro x ho hfit
    change x.regs (register 15) = 1 at ho
    change Fits w (x.regs (register 13) + 1) at hfit
    change (Op.exactBin .add (register 13) (register 13) (register 15)).eval w x =
      some (x.set (register 13) (x.regs (register 13) + 1))
    rw [Op.eval_exactBin, ho]
    exact Data.put_of_fits hfit
  span_exec := by
    intro x hx hfront hparam
    have hcap : x.regs (register 3) = C := hparam 0
    obtain ⟨y, he, hm, _, hb, hfr, hc, _, _⟩ :=
      MemoryQueueInit.span_exec register w base C x hx hfront hcap hf
    exact ⟨y, he, hm, hb, hfr, fun _ => hc⟩
  setup_exec := by
    intro x hx hbase hfront hparam hzero
    have hcap : x.regs (register 3) = C := hparam 0
    obtain ⟨y, he, hm, hy, hLayout, hfr, _, _, _⟩ :=
      MemoryQueueInit.setup_exec register w base C x hx hbase hcap hf
    have hfrontY : y.regs (register 11) = base + space C := hfr.trans hfront
    have hzeroY : ∀ a ∈ (Block.mk base (space C)).footprint, y.mem a = 0 := by
      intro a ha
      rw [hm]
      exact hzero a ha
    have hM := empty_rep hf (memoryState (register 11) y) hfrontY hzeroY
    have hlayout : layoutMatch base C y.regs := by
      intro i
      rw [layoutWords_relative]
      exact hLayout i
    refine ⟨y, he, hfrontY, ⟨hy, hlayout, hM⟩, ?_, ?_⟩
    · have hcount := hzeroY (base + 1 + C) (by
        simp only [Block.mem_footprint, Block.Owns, space]
        omega)
      simp only [hcount, Nat.mul_zero, Nat.zero_le]
    · intro a _
      exact congrFun hm a

/-- A framed native implementation of the bounded FIFO queue, with one globally selected code
body for every runtime base, capacity and word width. Initialization uses the existing fresh
zero-block contract; `initClear` has its explicit linear cost on dirty owned memory. -/
@[no_expose] noncomputable def implementation (w base C : ℕ) (hf : Fits w (base + space C)) :
    DataStructure.WordRAM.StateTransitionImpl program (Queue.WordRAM.spec w C)
      w base (fun _ => C) [] := by
  let M := semanticModule w base C hf
  refine Realizes.toStateTransitionImplWithArgs M MemoryQueueMethod.realizes_method
    (fun o => ((frontLayout base C, rearLayout base C), o)) ?_
    (register 11) source scratch scratch_injective source_scratch scratch_frontier source_frontier
    (baseCertificate w base C hf) rfl ?_ ?_ ?_ ?_ ?_
  · intro o
    rw [MemoryQueueMethod.method_source_eq _ w C]
    change _ = (do
      let a ← (Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
        (layouts_valid hf).2.2).methods o
      pure (⟨o, a⟩ : (Queue.queue ℕ).Label))
    rw [Queue.Memory.memRefinement_methods]
  · intro q x o hr hv ha
    change representation w base C hf q x at hr
    refine ⟨?_, ?_, hr.2.2⟩
    · funext i
      refine Fin.addCases (motive := fun i => x.regs (source i) =
        MemoryQueueMethod.methodWords ((frontLayout base C, rearLayout base C), o) i)
        (fun j : Fin 8 => ?_) (fun j : Fin 3 => ?_) i
      · have hidx : (Fin.castLE (by decide : 11 ≤ 16) (Fin.castAdd 3 j) : Fin 16) =
            Fin.castLE (by decide : 8 ≤ 16) j := Fin.ext rfl
        have hsrc : source (Fin.castAdd 3 j) = register (Fin.castLE (by decide) j) :=
          congrArg register hidx
        have hj := hr.2.1 j
        rw [← hsrc] at hj
        simpa [MemoryQueueMethod.methodWords, Fin.appendEquiv] using hj
      · simpa [MemoryQueueMethod.methodWords, Fin.appendEquiv, source] using ha j
    · apply method_safe (layouts_valid hf).1 (layouts_valid hf).2.1 (layouts_valid hf).2.2
        (wellFormed_memoryState hr.1) hr.2.2.1 o
      simpa only [hr.2.2.2] using hv
  · intro o a regs hout
    cases o with
    | enqueue v => cases a; rfl
    | dequeue =>
      have htag := hout 2
      have hval := hout 3
      cases a with
      | none =>
        change regs (outputRegister 2) = 0 at htag
        change some (if regs (outputRegister 2) = 0 then none else
          some (regs (outputRegister 3))) = some none
        rw [htag]
        rfl
      | some v =>
        change regs (outputRegister 2) = 1 at htag
        change regs (outputRegister 3) = v at hval
        change some (if regs (outputRegister 2) = 0 then none else
          some (regs (outputRegister 3))) = some (some v)
        simp only [htag, hval, one_ne_zero, ↓reduceIte]
  · intro q q' x y o a hr _ _ _ hM hy hframe
    change representation w base C hf q x at hr
    change representation w base C hf q' y
    refine ⟨hy, ?_, hM⟩
    intro i
    have he := hframe (register (Fin.castLE (by decide) i)) (by
      intro h
      have := congrArg Fin.val h
      change i.val = 11 at this
      have := i.isLt
      omega) (by
        intro j h
        have := congrArg Fin.val h
        change 16 + j.val = i.val at this
        have := i.isLt
        omega)
    exact he.trans (hr.2.1 i)
  · intro q e o hr hv
    change (Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
      (layouts_valid hf).2.2).toModule.rep q e at hr
    have hv' : (Queue.WordRAM.spec w C).valid
        ((Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
          (layouts_valid hf).2.2).abs e) o := by simpa only [hr.2] using hv
    have h := MemoryQueueFrame.modifies_methods (layouts_valid hf).1 (layouts_valid hf).2.1
      (layouts_valid hf).2.2 o hr.1 hv'
    rw [layouts_footprint] at h
    change Modifies (Block.mk base (space C)).footprint e.mem ((Memory.spec w).clientState e
      ((Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
        (layouts_valid hf).2.2).methods o)).mem
    rw [Queue.Memory.memRefinement_methods]
    exact h.1
  · intro q q' x y o a hr hv _ _ _ hm _
    change representation w base C hf q x at hr
    have hv' : (Queue.WordRAM.spec w C).valid
        ((Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
          (layouts_valid hf).2.2).abs (memoryState (register 11) x)) o := by
      simpa only [hr.2.2.2] using hv
    have hp := method_pay (layouts_valid hf).1 (layouts_valid hf).2.1 (layouts_valid hf).2.2
      (wellFormed_memoryState hr.1) hr.2.2.1 o hv' MemoryQueueMethod.realizes_method.factor
    have hs : (Memory.spec 0).clientState (memoryState (register 11) x)
        (MemoryQueueMethod.method ((frontLayout base C, rearLayout base C), o)) =
        memoryState (register 11) y := by
      have hw' := (clientState_width w
        (MemoryQueueMethod.method ((frontLayout base C, rearLayout base C), o))
        (memoryState (register 11) x)).symm
      apply hw'.trans
      rw [MemoryQueueMethod.method_source_eq _ w C]
      change (Memory.spec w).clientState (memoryState (register 11) x)
        ((Queue.Memory.memMethods (frontLayout base C) (rearLayout base C) w C o).bind _) = _
      have htag : (Memory.spec w).clientState (memoryState (register 11) x)
          ((Queue.Memory.memMethods (frontLayout base C) (rearLayout base C) w C o).bind
            (fun a => pure (⟨o, a⟩ : (Queue.queue ℕ).Label))) =
          (Memory.spec w).clientState (memoryState (register 11) x)
            (Queue.Memory.memMethods (frontLayout base C) (rearLayout base C) w C o) := by
        simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
        rfl
      rw [htag]
      change _ = (memoryState (register 11) y)
      change memoryState (register 11) y = (Memory.spec w).clientState
        (memoryState (register 11) x) ((Queue.Memory.memRefinement (layouts_valid hf).1
          (layouts_valid hf).2.1 (layouts_valid hf).2.2).methods o) at hm
      rw [Queue.Memory.memRefinement_methods] at hm
      exact hm.symm
    rw [hs] at hp
    exact hp

private theorem implementation_data (w base C : ℕ) (hf : Fits w (base + space C)) :
    (implementation w base C hf).space = space C ∧
    (implementation w base C hf).initTime = 13 ∧
    (implementation w base C hf).initPotential = 0 ∧
    (∀ q o, (implementation w base C hf).charge q o =
      153 * MemoryQueueMethod.realizes_method.factor) ∧
    (∀ x, (implementation w base C hf).potential x =
      48 * MemoryQueueMethod.realizes_method.factor * x.mem (base + 1 + C)) ∧
    (∀ v regs, (implementation w base C hf).decode (.enqueue v) regs = some ()) ∧
    (∀ regs, (implementation w base C hf).decode .dequeue regs =
      some (if regs (outputRegister 2) = 0 then none else some (regs (outputRegister 3)))) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

@[simp] theorem implementation_space (w base C : ℕ) (hf : Fits w (base + space C)) :
    (implementation w base C hf).space = space C := (implementation_data w base C hf).1

@[simp] theorem implementation_initTime (w base C : ℕ) (hf : Fits w (base + space C)) :
    (implementation w base C hf).initTime = 13 := (implementation_data w base C hf).2.1

@[simp] theorem implementation_initPotential (w base C : ℕ) (hf : Fits w (base + space C)) :
    (implementation w base C hf).initPotential = 0 := (implementation_data w base C hf).2.2.1

@[simp] theorem implementation_charge (w base C : ℕ) (hf : Fits w (base + space C))
    (q : List ℕ) (o : Queue.QueueOp ℕ) :
    (implementation w base C hf).charge q o = 153 * MemoryQueueMethod.realizes_method.factor :=
  (implementation_data w base C hf).2.2.2.1 q o

@[simp] theorem implementation_potential (w base C : ℕ) (hf : Fits w (base + space C))
    (x : Data registers) :
    (implementation w base C hf).potential x =
      48 * MemoryQueueMethod.realizes_method.factor * x.mem (base + 1 + C) :=
  (implementation_data w base C hf).2.2.2.2.1 x

/-- The local native representation is the original semantic queue representation plus bounded
native data and the persistent layout ABI. It does not equate globally different memories. -/
theorem implementation_rep_iff (w base C : ℕ) (hf : Fits w (base + space C))
    (q : List ℕ) (x : Data registers) :
    (implementation w base C hf).rep q x ↔
      x.Bounded w ∧
        (∀ i : Fin 8, x.regs (register (Fin.castLE (by decide) i)) =
          MemoryQueue.layoutWords (frontLayout base C, rearLayout base C) i) ∧
        (Queue.Memory.memRefinement (layouts_valid hf).1 (layouts_valid hf).2.1
          (layouts_valid hf).2.2).toModule.rep q (memoryState (register 11) x) := Iff.rfl

@[simp] theorem implementation_decode_enqueue (w base C : ℕ) (hf : Fits w (base + space C))
    (v : ℕ) (regs : Fin registers → ℕ) :
    (implementation w base C hf).decode (.enqueue v) regs = some () :=
  (implementation_data w base C hf).2.2.2.2.2.1 v regs

@[simp] theorem implementation_decode_dequeue (w base C : ℕ) (hf : Fits w (base + space C))
    (regs : Fin registers → ℕ) :
    (implementation w base C hf).decode .dequeue regs =
      some (if regs (outputRegister 2) = 0 then none else some (regs (outputRegister 3))) :=
  (implementation_data w base C hf).2.2.2.2.2.2 regs

end Cslib.WordRAM.Realization.MemoryQueueAdapter
