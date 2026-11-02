/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Queue.Memory

/-!
# Finite support of preallocated memory-queue methods

The existing two-stack queue methods modify only their two layout footprints and preserve the
allocation frontier. Their abstraction and invariant depend on these cells; increasing the
frontier preserves allocation. These facts reuse the existing stack frame, pair refinement and
`Modifies` relation, without changing the memory model or the queue implementation.

This leaf supplies support facts for native queue adapters. It proves no native execution or
resource bound and does not allocate the layouts.

## Main results

* `modifies_methods`: a valid queue operation preserves all cells outside its two layouts and
  leaves the frontier unchanged.
* `abs_congr`: agreement on the layouts preserves the queue abstraction.
* `inv_congr`: the same agreement and a nondecreasing frontier preserve the invariant.

## References

These are original support lemmas for the existing memory-queue implementation.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueueFrame

open Cslib.DataStructure

variable {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout}

private theorem pair_method_frame (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) {s : Memory.State}
    (o : (Queue.Memory.boundedStacks w C).Op)
    (hv : (Queue.Memory.boundedStacks w C).valid
      ((Stack.Memory.pairRefinement h₁ h₂ hd).abs s) o) :
    Modifies (L₁.footprint ∪ L₂.footprint) s.mem
        ((Memory.spec w).clientState s ((Stack.Memory.pairRefinement h₁ h₂ hd).methods o)).mem ∧
      ((Memory.spec w).clientState s
        ((Stack.Memory.pairRefinement h₁ h₂ hd).methods o)).frontier = s.frontier := by
  cases o with
  | inl o =>
    obtain ⟨hm, hf⟩ := Stack.Memory.modifies_methods h₁ o hv
    exact ⟨fun a ha => hm a (fun h => ha (Finset.mem_union_left _ h)), hf⟩
  | inr o =>
    obtain ⟨hm, hf⟩ := Stack.Memory.modifies_methods h₂ o hv
    exact ⟨fun a ha => hm a (fun h => ha (Finset.mem_union_right _ h)), hf⟩

private theorem pair_link_frame {α : Type} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) (p : (Queue.Memory.boundedStacks w C).Client α)
    {s s' : Memory.State} {a : α} {tr : (Memory.spec w).Transcript}
    (hs : (Stack.Memory.pairRefinement h₁ h₂ hd).inv s)
    (hv : (Queue.Memory.boundedStacks w C).DemonicValid
      ((Stack.Memory.pairRefinement h₁ h₂ hd).abs s) p)
    (hrun : (Memory.spec w).ClientRun s
      (link (Stack.Memory.pairRefinement h₁ h₂ hd).methods p) a s' tr) :
    Modifies (L₁.footprint ∪ L₂.footprint) s.mem s'.mem ∧ s'.frontier = s.frontier := by
  let M := Stack.Memory.pairRefinement h₁ h₂ hd
  induction p generalizing s tr with
  | pure b =>
    change (Memory.spec w).ClientRun s (.pure b) a s' tr at hrun
    have hstate := ((Memory.spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    have heq : s' = s := hstate.2.2.1
    subst s'
    exact ⟨Modifies.refl _ _, rfl⟩
  | liftBind o k ih =>
    obtain ⟨hv₁, hvk⟩ :=
      ((Queue.Memory.boundedStacks w C).demonicValid_liftBind_iff _ o k).mp hv
    change (Memory.spec w).ClientRun s
      ((M.methods o).bind (fun v => link M.methods (k v))) a s' tr at hrun
    obtain ⟨v, s₁, tr₁, tr₂, hr₁, hr₂, rfl⟩ := (Memory.spec w).clientRun_bind_iff.mp hrun
    obtain ⟨hstep, hs₁⟩ := M.correct o hs hv₁ hr₁
    obtain ⟨hm₂, hf₂⟩ := ih v hs₁ (hvk _ _ hstep) hr₂
    have hstate := ((Memory.spec w).clientRun_iff_runClient _ _ _ _ _).mp hr₁
    have hfirst := pair_method_frame h₁ h₂ hd o hv₁
    rw [← hstate.2.2.1] at hfirst
    exact ⟨fun a ha => (hm₂ a ha).trans (hfirst.1 a ha), hf₂.trans hfirst.2⟩

/-- An admissible queue method writes only its preallocated layouts and never allocates.
The method expression is independent of the proofs about layout validity and disjointness. -/
theorem modifies_methods (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) {s : Memory.State}
    (o : (Queue.WordRAM.spec w C).Op) (hs : (Queue.Memory.memRefinement h₁ h₂ hd).inv s)
    (hv : (Queue.WordRAM.spec w C).valid ((Queue.Memory.memRefinement h₁ h₂ hd).abs s) o) :
    Modifies (L₁.footprint ∪ L₂.footprint) s.mem
        ((Memory.spec w).clientState s (Queue.Memory.memMethods L₁ L₂ w C o)).mem ∧
      ((Memory.spec w).clientState s (Queue.Memory.memMethods L₁ L₂ w C o)).frontier =
        s.frontier := by
  have hvp := (Queue.Memory.refinement w C).valid o hs.2 hv
  have hvE := ((Stack.Memory.pairRefinement h₁ h₂ hd).simulates_demonic
    (Queue.methods o) hs.1 hvp).1
  have hr := (Memory.spec w).clientRun_canonical s _
    (((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp hvE)
  have h := pair_link_frame h₁ h₂ hd (Queue.methods o) hs.1 hvp hr
  rw [Stack.Memory.pairRefinement_methods] at h
  exact h

/-- Agreement on the two layout footprints preserves the queue abstraction. Cells outside the
layouts may differ arbitrarily; the frontier need not agree. -/
theorem abs_congr (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) {s s' : Memory.State}
    (hs : (Queue.Memory.memRefinement h₁ h₂ hd).inv s)
    (hmem : ∀ a ∈ L₁.footprint ∪ L₂.footprint, s'.mem a = s.mem a) :
    (Queue.Memory.memRefinement h₁ h₂ hd).abs s' =
      (Queue.Memory.memRefinement h₁ h₂ hd).abs s := by
  change Queue.WordRAM.contents (Stack.Memory.abs L₁ s', Stack.Memory.abs L₂ s') =
    Queue.WordRAM.contents (Stack.Memory.abs L₁ s, Stack.Memory.abs L₂ s)
  rw [Stack.Memory.abs_congr h₁ hs.1.1 (fun a ha => hmem a (Finset.mem_union_left _ ha)),
    Stack.Memory.abs_congr h₂ hs.1.2 (fun a ha => hmem a (Finset.mem_union_right _ ha))]

/-- The composite queue invariant depends on the two layouts and survives a growing frontier. -/
theorem inv_congr (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) {s s' : Memory.State}
    (hs : (Queue.Memory.memRefinement h₁ h₂ hd).inv s)
    (hmem : ∀ a ∈ L₁.footprint ∪ L₂.footprint, s'.mem a = s.mem a)
    (hf : s.frontier ≤ s'.frontier) : (Queue.Memory.memRefinement h₁ h₂ hd).inv s' := by
  refine ⟨⟨hs.1.1.congr h₁ (fun a ha => hmem a (Finset.mem_union_left _ ha)) hf,
    hs.1.2.congr h₂ (fun a ha => hmem a (Finset.mem_union_right _ ha)) hf⟩, ?_⟩
  change Queue.Memory.Inv w C ((Queue.Memory.memRefinement h₁ h₂ hd).abs s')
  rw [abs_congr h₁ h₂ hd hs hmem]
  exact hs.2

end Cslib.WordRAM.Realization.MemoryQueueFrame
