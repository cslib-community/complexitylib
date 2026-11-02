/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.While
public import Complexity.DataStructure.Queue.Memory

/-!
# Early-exit transfer for the memory queue

The remaining number of rear elements is explicit loop state. A rear pop returning `none`
sets it to zero, so the shared bounded while loop stops immediately. The source equalities
preserve the original linked queue program, including its operation history.

## Main definitions

* `transferBody`: one rear pop and, when successful, one front push.

## Main results

* `transfer_eq_boundedWhile`: the existing transfer program is the shared early-exit loop.
* `run_eq_allocPair_bind`: allocation followed by the original linked queue client.
* `transfer_invariant`: the existing framed product preserves both stacks and moves the rear.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.Memory

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure.Memory

/-- Pop one rear element. An empty rear stops the loop; a successful move decreases the
explicit remaining count. The loop guard excludes a zero count from this body. -/
def transferBody (d : (Stack.Memory.Layout × Stack.Memory.Layout) × ℕ) : Prog ℕ := do
  let a ← Stack.Memory.pop d.1.2
  match a with
  | none => pure 0
  | some v => do
      Stack.Memory.push d.1.1 v
      pure (d.2 - 1)

/-- Forgetting the loop's remaining count leaves exactly one step of the original transfer. -/
theorem transferBody_forget (L₁ L₂ : Stack.Memory.Layout) (w C r : ℕ) :
    (transferBody ((L₁, L₂), r)).bind (fun _ => pure ()) =
      link (Methods.prod (Stack.Memory.methods L₁ w C) (Stack.Memory.methods L₂ w C))
        (Queue.transfer 1) := by
  simp only [transferBody, Queue.transfer, link, Methods.prod, Stack.Memory.methods,
    PFunctor.FreeM.liftM, PFunctor.FreeM.bind_eq_bind, bind_assoc]
  congr 1
  funext a
  cases a <;> simp [PFunctor.FreeM.liftM, Methods.prod, Stack.Memory.methods]

/-- The bounded while has exactly the original source program, with no inactive tail queries
or extra memory operations after an early empty pop. The cutoff bounds the remaining count. -/
theorem transfer_eq_boundedWhile (L₁ L₂ : Stack.Memory.Layout) (w C fuel n : ℕ)
    (hn : n ≤ fuel) :
    link (Methods.prod (Stack.Memory.methods L₁ w C) (Stack.Memory.methods L₂ w C))
        (Queue.transfer n) =
      (boundedWhile (fun _ r => 0 < r) transferBody (L₁, L₂) fuel n).bind
        (fun _ => pure ()) := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst n
    rfl
  | succ fuel ih =>
    cases n with
    | zero => simp [Queue.transfer, boundedWhile, link]
    | succ n =>
      simp only [Queue.transfer, link, PFunctor.FreeM.liftM, Methods.prod,
        Stack.Memory.methods, boundedWhile, Nat.zero_lt_succ, ↓reduceIte, transferBody,
        Nat.add_sub_cancel, PFunctor.FreeM.bind_eq_bind, bind_assoc]
      congr 1
      funext a
      cases a with
      | none => simp [boundedWhile_of_not]
      | some v =>
        simp only [PFunctor.FreeM.liftM]
        exact congrArg (fun p => (Stack.Memory.push L₁ v).bind (fun _ => p))
          (ih n (by omega))

/-- The current allocator allocates its two stack handles and then links the unchanged queue
methods through their product. This is equality of programs, before selecting a memory state. -/
theorem run_eq_allocPair_bind (w C : ℕ) {α : Type}
    (p : (Queue.WordRAM.spec w C).Client α) :
    run w C p = (Allocator.allocPair (Stack.Memory.allocator w C)
      (Stack.Memory.allocator w C)).bind (fun L => link ((allocator w C).methods L) p) := rfl

/-- The source transfer preserves the two existing storage invariants and reverses the rear
into the front. The generic framed product supplies noninterference; no replacement invariant
or instruction-level proof is needed. -/
theorem transfer_invariant {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : State} (hw : WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    let p := link (Methods.prod (Stack.Memory.methods L₁ w C)
      (Stack.Memory.methods L₂ w C)) (Queue.transfer n)
    let s' := (spec w).clientState s p
    (spec w).ValidHistory s ((spec w).clientHistory s p) ∧
      WellFormed w s' ∧ Stack.Memory.Inv L₁ s' ∧ Stack.Memory.Inv L₂ s' ∧
      s'.mem L₂.count.base = 0 ∧ s'.mem L₁.count.base = s.mem L₁.count.base + n ∧
      Stack.Memory.abs L₁ s' = (Stack.Memory.abs L₂ s).reverse ++ Stack.Memory.abs L₁ s := by
  let M := (Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)
  have hi : M.inv s := ⟨hs₁, hs₂, hd, by
    change Cslib.WordRAM.Fits w (s.frontier + (0 + 0))
    simpa only [Nat.add_zero] using hw.frontier_fits⟩
  have hn' : n = (Stack.Memory.abs L₂ s).length := by
    rw [Stack.Memory.length_abs, hn]
  have hv : (boundedStacks w C).ValidHistory (M.abs s)
      ((boundedStacks w C).clientHistory (M.abs s) (Queue.transfer n)) := by
    rw [clientHistory_boundedStacks, hn']
    change (boundedStacks w C).ValidHistory (Stack.Memory.abs L₁ s, Stack.Memory.abs L₂ s)
      ((stackPair ℕ).runClient (Stack.Memory.abs L₁ s, Stack.Memory.abs L₂ s)
        (Queue.transfer (Stack.Memory.abs L₂ s).length)).2.2
    rw [Queue.transfer_run]
    apply validHistory_transferTrace
    · simpa only [Stack.Memory.length_abs] using hlen
    · intro v hv
      simp only [Stack.Memory.abs, List.mem_reverse, Cslib.WordRAM.Block.entries,
        List.mem_map] at hv
      obtain ⟨i, _, rfl⟩ := hv
      exact hw.mem_fits _
  obtain ⟨hvE, _, habs, hsE⟩ := M.toRefinement.simulates_client (Queue.transfer n) hi hv
  have habs' : M.abs ((spec w).clientState s (link M.methods (Queue.transfer n))) =
      ((Stack.Memory.abs L₂ s).reverse ++ Stack.Memory.abs L₁ s, []) := by
    rw [habs, clientState_boundedStacks, hn']
    exact congrArg (fun t => t.2.1) (Queue.transfer_run (Stack.Memory.abs L₁ s)
      (Stack.Memory.abs L₂ s))
  let s' := (spec w).clientState s (link (Methods.prod (Stack.Memory.methods L₁ w C)
    (Stack.Memory.methods L₂ w C)) (Queue.transfer n))
  have hfront : Stack.Memory.abs L₁ s' =
      (Stack.Memory.abs L₂ s).reverse ++ Stack.Memory.abs L₁ s := congrArg Prod.fst habs'
  have hrear : Stack.Memory.abs L₂ s' = [] := congrArg Prod.snd habs'
  have hfrontLength := congrArg List.length hfront
  have hrearLength := congrArg List.length hrear
  simp only [Stack.Memory.length_abs, List.length_append, List.length_reverse,
    List.length_nil, hn] at hfrontLength hrearLength
  refine ⟨hvE, ?_, hsE.1, hsE.2.1, hrearLength, ?_, hfront⟩
  · rw [← (spec w).run_runClient]
    exact hw.run hvE
  · simpa only [Nat.add_comm] using hfrontLength

end Cslib.DataStructure.Queue.Memory
