/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Loop
public import Complexity.Computability.WordRAM.Realization.Bind
public import Complexity.Computability.WordRAM.Realization.Reindex
public import Complexity.Computability.WordRAM.Realization.GlueVector
public import Complexity.Computability.WordRAM.Realization.Grade
public import Complexity.Computability.WordRAM.Realization.Client.MemoryStack
public import Complexity.DataStructure.Queue.Memory

/-!
# Native consumption of the two-stack memory queue

The existing source transfer stops when a rear pop returns `none`. A bounded native loop keeps
an explicit active flag: after that result, remaining iterations return the flag without
queries. Their local work remains charged. One uniform emitter consumes complete runtime
layouts, the flag and the fuel; it is fixed before the layouts' allocation addresses.

The body composes the existing memory-stack certificates. Both native branches, result copies,
binds and loop control contribute to the explicit grading. The source program remains the
queue's linked `transfer`; the domain and cost proofs reuse its storage invariants. A separate
operation dispatcher and local framed adapter can consume this transfer certificate.

## Main definitions

* `transferBody`, `transferSafe`: one iteration and its actual intermediate memory domains.
* `layoutWords`, `bodyWords`, `transferWords`: faithful runtime layouts, flag and fuel encodings.

## Main results

* `transfer_eq_iterate`: exact source equality, including early termination.
* `memMethods_enqueue`, `memMethods_dequeue`: the existing queue methods' source decompositions.
* `realizes_transferBody`, `realizes_source_transfer`: native certificates with explicit work.
* `transfer_invariant`: the storage invariants discharge every reached iteration's domain.
* `source_transfer_cost`, `source_transfer_work_bound`: six memory units per item and a separate
  envelope paying the certified local work when the fuel is the actual rear count.

## References

The two-stack queue and its semantic potential argument are reused from
[Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Exercise 10.1-6 and
Chapter 17][CLRS2009]. The native realization and local-work grading here are original
infrastructure over those existing programs.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryQueue

open Cslib.DataStructure

/-- One active transfer iteration moves a rear item to the front. Once inactive, the remaining
bounded iterations perform no memory operation. Both layouts are runtime data. -/
def transferBody (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Bool) : Memory.Prog Bool :=
  if d.2 then do
    let a ← Stack.Memory.pop d.1.2
    match a with
    | none => pure false
    | some v => do
        Stack.Memory.push d.1.1 v
        pure true
  else pure false

/-- Inactive tail iterations issue no memory query and leave the source program pure. -/
theorem iterate_inactive (L : Stack.Memory.Layout × Stack.Memory.Layout) (n : ℕ) :
    iterate transferBody L n false = pure false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [iterate, transferBody] using ih

/-- The source's early stop is represented exactly, rather than replaced by repeated pops on an
empty rear stack. Inactive native iterations are paid by the loop-work ledger. -/
theorem transfer_eq_iterate (L₁ L₂ : Stack.Memory.Layout) (w C n : ℕ) :
    link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n) =
      (iterate transferBody (L₁, L₂) n true).bind (fun _ => pure ()) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Queue.transfer, link, PFunctor.FreeM.liftM, iterate, transferBody]
    simp only [Stack.Memory.pairMethods, Stack.Memory.methods, ↓reduceIte,
      PFunctor.FreeM.bind_eq_bind, bind_assoc]
    congr 1
    funext a
    cases a with
    | none => simp [iterate_inactive]
    | some v =>
      simp only [PFunctor.FreeM.liftM]
      exact congrArg (fun p => (Stack.Memory.push L₁ v).bind (fun _ => p)) ih

/-- Enqueue uses the rear stack's existing push program unchanged. -/
theorem memMethods_enqueue (L₁ L₂ : Stack.Memory.Layout) (w C v : ℕ) :
    Queue.Memory.memMethods L₁ L₂ w C (.enqueue v) = Stack.Memory.push L₂ v := by
  simp only [Queue.Memory.memMethods, Queue.methods, link, PFunctor.FreeM.liftM,
    Stack.Memory.pairMethods, Stack.Memory.methods]
  change (Stack.Memory.push L₂ v).bind pure = _
  exact PFunctor.FreeM.bind_pure _

/-- The existing dequeue dispatches between an immediate front pop and a runtime-sized transfer.
All layout values and the rear count remain ordinary runtime data. -/
theorem memMethods_dequeue (L₁ L₂ : Stack.Memory.Layout) (w C : ℕ) :
    Queue.Memory.memMethods L₁ L₂ w C .dequeue = (do
      let a ← Stack.Memory.pop L₁
      match a with
      | some v => pure (some v)
      | none => do
          let n ← Stack.Memory.size L₂
          let _ ← iterate transferBody (L₁, L₂) n true
          Stack.Memory.pop L₁) := by
  simp only [Queue.Memory.memMethods, Queue.methods, link, PFunctor.FreeM.liftM,
    Stack.Memory.pairMethods, Stack.Memory.methods]
  congr 1
  funext a
  cases a with
  | some v => rfl
  | none =>
    simp only [PFunctor.FreeM.liftM, Stack.Memory.pairMethods, Stack.Memory.methods]
    congr 1
    funext n
    change ℕ at n
    rw [PFunctor.FreeM.liftM_bind]
    change (link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n)).bind _ = _
    rw [transfer_eq_iterate]
    simp only [PFunctor.FreeM.liftM, Stack.Memory.pairMethods, Stack.Memory.methods,
      PFunctor.FreeM.bind_eq_bind, bind_assoc, pure_bind]
    change (iterate transferBody (L₁, L₂) n true).bind
      (fun _ => (Stack.Memory.pop L₁).bind pure) = _
    rw [PFunctor.FreeM.bind_pure]
    rfl

/-- Both complete runtime stack layouts, front followed by rear. -/
def layoutWords : (Stack.Memory.Layout × Stack.Memory.Layout) ↪ (Fin 8 → ℕ) :=
  (MemoryStack.layoutWords.prodMap MemoryStack.layoutWords).trans
    (Fin.appendEquiv 4 4).toEmbedding

/-- The two layouts followed by the active Boolean's tag and retained zero word. -/
def bodyWords : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) ↪ (Fin 10 → ℕ) :=
  (layoutWords.prodMap boolWords).trans (Fin.appendEquiv 8 2).toEmbedding

private def replyWords : (((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) × Option ℕ) ↪
    (Fin 12 → ℕ) :=
  (bodyWords.prodMap optionWords).trans (Fin.appendEquiv 10 2).toEmbedding

private theorem body_test (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Bool) :
    test (.eq 8 9) (bodyWords d) ↔ d.2 = false := by
  change d.2.toNat = 0 ↔ d.2 = false
  cases d.2 <;> decide

private theorem reply_test
    (d : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) × Option ℕ) :
    test (.eq 10 9) (replyWords d) ↔ d.2 = none := by
  change optionWords d.2 0 = 0 ↔ d.2 = none
  cases d.2 <;> simp [optionWords]

private theorem returnFlag {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) (b : Bool) :
    Realizes .exact (fun _ => pure b) input boolWords
      (fun w _ _ => Fits w b.toNat) (fun _ _ => 4) := by
  let g : Fin 2 → (Fin k → ℕ) → ℕ := fun i _ => boolWords b i
  have h := Realizes.glueVector (B := .exact) input boolWords (fun _ => b) g g (fun _ => 1)
    (fun _ _ => rfl) (P := fun _ => True)
    (fun _ => GlueComputes.const _ (fun _ _ => le_rfl))
  apply h.consequence (hwork := fun _ _ => by simp)
  intro w d s _ _ hb
  refine ⟨trivial, fun i => ?_⟩
  fin_cases i
  · exact hb
  · exact fits_zero w

private theorem returnInactive {δ : Type} {k : ℕ} (input : δ ↪ (Fin k → ℕ)) :
    Realizes .exact (fun _ => pure false) input boolWords
      (fun _ _ _ => True) (fun _ _ => 4) :=
  (returnFlag input false).consequence
    (fun w _ _ _ _ _ => fits_zero w) (fun _ _ => le_rfl)

/-- The visible domains of the actual pop/branch/push composition, at the actual intermediate
memory. The inactive path has no stack precondition; the true result tag must fit when pushed. -/
def transferSafe (w : ℕ) (d : (Stack.Memory.Layout × Stack.Memory.Layout) × Bool)
    (s : Memory.State) : Prop :=
  if d.2 then
    d.1.2.Valid w d.1.2.items.length ∧ Stack.Memory.Inv d.1.2 s ∧
      match (Memory.spec 0).clientResult s (Stack.Memory.pop d.1.2) with
      | none => True
      | some _ =>
          d.1.1.Valid w d.1.1.items.length ∧
            Stack.Memory.Inv d.1.1 ((Memory.spec 0).clientState s (Stack.Memory.pop d.1.2)) ∧
            ((Memory.spec 0).clientState s (Stack.Memory.pop d.1.2)).mem d.1.1.count.base <
              d.1.1.items.length ∧ Fits w 1
  else True

/-- The transfer body consumes the already certified stack methods. Its constant local-work
allowance includes pop/push glue, both native conditionals, result copies and every bind. -/
theorem realizes_transferBody :
    Realizes .exact transferBody bodyWords boolWords transferSafe (fun _ _ => 39) := by
  have hpop := MemoryStack.realizes_pop.reindex
    (fun d : (Stack.Memory.Layout × Stack.Memory.Layout) × Bool => d.1.2)
    bodyWords ![4, 5, 6, 7] (by intro d i; fin_cases i <;> rfl)
  have hpush := MemoryStack.realizes_push.reindex
    (fun d : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) × Option ℕ =>
      (d.1.1.1, d.2.getD 0)) replyWords ![0, 1, 2, 3, 11] (by
        intro d i
        fin_cases i <;> try rfl
        rcases d with ⟨d, a⟩
        cases a <;> rfl)
  let pushInput := (replyWords.prodMap
    (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding).trans
      (Fin.appendEquiv 12 0).toEmbedding
  have hsome := (hpush.bind (returnFlag pushInput true)).consequence
    (safe' := fun w d s => d.1.1.1.Valid w d.1.1.1.items.length ∧
      Stack.Memory.Inv d.1.1.1 s ∧ s.mem d.1.1.1.count.base < d.1.1.1.items.length ∧ Fits w 1)
    (work' := fun _ _ => 15)
    (fun _ _ _ _ _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩)
    (fun _ _ => le_rfl)
  have hreply := Realizes.branch (.eq 10 9) (returnInactive replyWords) hsome
  have hreply_program :
      (fun d => if test (.eq 10 9) (replyWords d) then (pure false : Memory.Prog Bool)
        else (Stack.Memory.push d.1.1.1 (d.2.getD 0)).bind (fun _ => pure true)) =
      (fun d : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) × Option ℕ =>
        match d.2 with
        | none => pure false
        | some v => (Stack.Memory.push d.1.1.1 v).bind (fun _ => pure true)) := by
    funext d
    rcases d with ⟨⟨⟨L₁, L₂⟩, active⟩, a⟩
    simp only [reply_test]
    cases a <;> rfl
  rw [hreply_program] at hreply
  have hactive := hpop.bind hreply
  have houter := Realizes.branch (.eq 8 9) (returnInactive bodyWords) hactive
  have houter_program :
      (fun d => if test (.eq 8 9) (bodyWords d) then (pure false : Memory.Prog Bool)
        else (Stack.Memory.pop d.1.2).bind (fun a => match a with
          | none => pure false
          | some v => (Stack.Memory.push d.1.1 v).bind (fun _ => pure true))) =
      transferBody := by
    funext d
    rcases d with ⟨⟨L₁, L₂⟩, active⟩
    simp only [body_test]
    cases active <;> rfl
  rw [houter_program] at houter
  apply houter.consequence
  · intro w d s _ _ h
    rcases d with ⟨⟨L₁, L₂⟩, active⟩
    simp only [body_test]
    cases active
    · trivial
    · change (L₂.Valid w L₂.items.length ∧ Stack.Memory.Inv L₂ s) ∧ _
      refine ⟨⟨h.1, h.2.1⟩, ?_⟩
      cases ha : (Memory.spec 0).clientResult s (Stack.Memory.pop L₂) with
      | none => simp only [reply_test, ↓reduceIte]
      | some v =>
        simpa only [reply_test, ha, reduceCtorEq, ↓reduceIte] using h.2.2
  · intro d s
    split
    · omega
    · split <;> omega

/-- Runtime layout words, a constant active tag/zero pair, and runtime transfer fuel. -/
def transferWords {k : ℕ}
    (input : (Stack.Memory.Layout × Stack.Memory.Layout) ↪ (Fin k → ℕ)) :
    ((Stack.Memory.Layout × Stack.Memory.Layout) × ℕ) ↪ (Fin (k + 2 + 1) → ℕ) :=
  (⟨fun d => ((d.1, true), d.2), by
    intro a b h
    have hL := congrArg (fun d => d.1.1) h
    have hn := congrArg Prod.snd h
    exact Prod.ext hL hn⟩ :
      ((Stack.Memory.Layout × Stack.Memory.Layout) × ℕ) ↪
        (((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) × ℕ)).trans
    (((((input.prodMap boolWords).trans (Fin.appendEquiv k 2).toEmbedding).prodMap
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
        (Fin.appendEquiv (k + 2) 1).toEmbedding))

/-- A single uniform body certificate gives the complete existing early-stop transfer program.
The loop and the final bind are both charged, even on the no-query path. -/
theorem realizes_transfer {k : ℕ}
    (input : (Stack.Memory.Layout × Stack.Memory.Layout) ↪ (Fin k → ℕ))
    {safe : ℕ → ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) → Memory.State → Prop}
    {work : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) → Memory.State → ℕ}
    (hbody : Realizes .exact transferBody
      ((input.prodMap boolWords).trans (Fin.appendEquiv k 2).toEmbedding)
      boolWords safe work) (w C : ℕ) :
    Realizes .exact
      (fun d => link (Stack.Memory.pairMethods d.1.1 d.1.2 w C) (Queue.transfer d.2))
      (transferWords input) (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => iterationSafe transferBody safe w d.1 d.2 true s)
      (fun d s => iterationWork transferBody work d.1 d.2 true s + 1) := by
  let hloop := (Realizes.iterateRuntime input boolWords hbody).reindex
    (fun d : (Stack.Memory.Layout × Stack.Memory.Layout) × ℕ => ((d.1, true), d.2))
    (transferWords input) id (fun _ _ => rfl)
  let nextInput := ((transferWords input).prodMap boolWords).trans
    (Fin.appendEquiv (k + 2 + 1) 2).toEmbedding
  have hunit : Realizes .exact (fun _ => (pure () : Memory.Prog Unit)) nextInput
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun _ _ _ => True) (fun _ _ => 0) := by
    have h := Realizes.glueVector (B := .exact) nextInput
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding (fun _ => ())
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (P := fun _ => True) (fun _ i => Fin.elim0 i) (fun i => Fin.elim0 i)
    simpa using h
  have h := hloop.bind hunit
  simpa only [hloop, transfer_eq_iterate, and_true, Nat.add_zero] using h

/-- The loop ledger charges every iteration, including pure inactive iterations. -/
private theorem transfer_work_le (work : ((Stack.Memory.Layout × Stack.Memory.Layout) × Bool) →
    Memory.State → ℕ) (K : ℕ) (hwork : ∀ d s, work d s ≤ K)
    (L : Stack.Memory.Layout × Stack.Memory.Layout) (n : ℕ) (active : Bool) (s : Memory.State) :
    iterationWork transferBody work L n active s ≤ (K + 1) * n := by
  induction n generalizing active s with
  | zero => simp [iterationWork]
  | succ n ih =>
    rw [iterationWork]
    have hnext := ih ((Memory.spec 0).clientResult s (transferBody (L, active)))
      ((Memory.spec 0).clientState s (transferBody (L, active)))
    have hbody := hwork (L, active) s
    nlinarith

/-- The actual source transfer has one uniform native emitter before its runtime layouts and
fuel. Forty local units per iteration pay the certified body and loop control; the final bind
costs one more. The visible safety predicate follows exactly the reached semantic states. -/
theorem realizes_source_transfer (w C : ℕ) :
    Realizes .exact
      (fun d => link (Stack.Memory.pairMethods d.1.1 d.1.2 w C) (Queue.transfer d.2))
      (transferWords layoutWords) (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => iterationSafe transferBody transferSafe w d.1 d.2 true s)
      (fun d _ => 40 * d.2 + 1) := by
  apply (realizes_transfer layoutWords realizes_transferBody w C).consequence
  · intro _ _ _ _ _ h
    exact h
  · intro d s
    exact Nat.add_le_add_right
      (transfer_work_le (fun _ _ => 39) 39 (fun _ _ => le_rfl) d.1 d.2 true s) 1

private theorem stack_inv_step {L : Stack.Memory.Layout} {w C : ℕ} (hL : L.Valid w C)
    {s : Memory.State} (hs : Stack.Memory.Inv L s) (o : Queue.StackOp ℕ)
    (hv : (Stack.WordRAM.spec w C).valid (Stack.Memory.abs L s) o) :
    (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (Stack.Memory.methods L w C o)) ∧
      Stack.Memory.Inv L ((Memory.spec 0).clientState s (Stack.Memory.methods L w C o)) := by
  let M := Stack.Memory.refinement hL
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    (M.valid o hs hv)
  have hcorrect := M.correct o hs hv ((Memory.spec w).clientRun_canonical s _ hvalid)
  have hinv := hcorrect.2
  change Stack.Memory.Inv L ((Memory.spec w).clientState s (Stack.Memory.methods L w C o)) at hinv
  rw [clientState_width w] at hinv
  exact ⟨hvalid, hinv⟩

private theorem client_wellFormed {w : ℕ} {α : Type} {s : Memory.State} (hw : Memory.WellFormed w s)
    (p : Memory.Prog α)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  have h := hw.run hv
  rw [StateTransitionSpec.run_runClient] at h
  rw [clientState_width w] at h
  exact h

private theorem transfer_step {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n + 1)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    let p := transferBody ((L₁, L₂), true)
    let s' := (Memory.spec 0).clientState s p
    transferSafe w ((L₁, L₂), true) s ∧
      Memory.WellFormed w s' ∧ Stack.Memory.Inv L₁ s' ∧ Stack.Memory.Inv L₂ s' ∧
      s'.mem L₂.count.base = n ∧ s'.mem L₁.count.base = s.mem L₁.count.base + 1 ∧
      (Memory.spec 0).clientResult s p = true ∧ memoryCost p s = 6 := by
  have hne : s.mem L₂.count.base ≠ 0 := by omega
  let a := (Memory.spec 0).clientState s (Stack.Memory.pop L₂)
  let v := s.mem (L₂.items.base + (s.mem L₂.count.base - 1))
  let b := (Memory.spec 0).clientState a (Stack.Memory.push L₁ v)
  have hpoprun := Stack.Memory.runClient_pop_of_pos (w := 0) L₂ s hne
  have ha : a = ⟨Function.update s.mem L₂.count.base n, s.frontier⟩ := by
    change ((Memory.spec 0).runClient s (Stack.Memory.pop L₂)).2.1 = _
    rw [hpoprun]
    simp only [hn, Nat.add_sub_cancel]
  have hanswer : (Memory.spec 0).clientResult s (Stack.Memory.pop L₂) = some v := by
    change ((Memory.spec 0).runClient s (Stack.Memory.pop L₂)).1 = _
    rw [hpoprun]
  have hc : L₁.count.base ≠ L₂.count.base :=
    ne_of_mem_of_not_mem (L₁.count_mem_footprint h₁.count_length)
      (Finset.disjoint_right.mp hd (L₂.count_mem_footprint h₂.count_length))
  have hcountA : a.mem L₁.count.base = s.mem L₁.count.base := by
    rw [ha]
    exact Function.update_of_ne hc _ _
  have hspare : a.mem L₁.count.base < C := by omega
  obtain ⟨hvp, hInvRearA⟩ := stack_inv_step h₂ hs₂ .pop trivial
  have hframeA := Stack.Memory.frame h₂ h₁ hd.symm hs₁ .pop trivial
  rw [clientState_width w] at hframeA
  have hInvFrontA : Stack.Memory.Inv L₁ a := hframeA.2
  have hvpush : (Stack.WordRAM.spec w C).valid (Stack.Memory.abs L₁ a) (.push v) := by
    exact ⟨by simpa only [Stack.Memory.length_abs] using hspare, hw.mem_fits _⟩
  obtain ⟨hvq, hInvFrontB⟩ := stack_inv_step h₁ hInvFrontA (.push v) hvpush
  have hframeB := Stack.Memory.frame h₁ h₂ hd hInvRearA (.push v) hvpush
  rw [clientState_width w] at hframeB
  have hInvRearB : Stack.Memory.Inv L₂ b := hframeB.2
  have hrear : b.mem L₂.count.base = n := by
    have h := congrArg List.length hframeB.1
    simp only [Stack.Memory.length_abs] at h
    change b.mem L₂.count.base = a.mem L₂.count.base at h
    rw [h, ha]
    exact Function.update_self _ _ _
  have hfront : b.mem L₁.count.base = s.mem L₁.count.base + 1 := by
    change ((Memory.spec 0).runClient a (Stack.Memory.push L₁ v)).2.1.mem L₁.count.base = _
    rw [Stack.Memory.runClient_push]
    simpa only [Function.update_self] using congrArg (· + 1) hcountA
  have hwb : Memory.WellFormed w b :=
    client_wellFormed (client_wellFormed hw _ hvp) _ hvq
  have h1 : Fits w 1 := hw.frontier_fits.of_le (by
    have h := hs₂.count_allocated
    change L₂.count.base + L₂.count.length ≤ s.frontier at h
    rw [h₂.count_length] at h
    omega)
  have hsafe : transferSafe w ((L₁, L₂), true) s := by
    change L₂.Valid w L₂.items.length ∧ Stack.Memory.Inv L₂ s ∧ _
    refine ⟨by simpa only [h₂.items_length] using h₂, hs₂, ?_⟩
    rw [hanswer]
    exact ⟨by simpa only [h₁.items_length] using h₁, hInvFrontA,
      by simpa only [h₁.items_length] using hspare, h1⟩
  have hbodyResult : (Memory.spec 0).clientResult s (transferBody ((L₁, L₂), true)) = true := by
    change ((Memory.spec 0).runClient s ((Stack.Memory.pop L₂).bind _)).1 = true
    rw [StateTransitionSpec.runClient_bind]
    change ((Memory.spec 0).runClient a
      (match (Memory.spec 0).clientResult s (Stack.Memory.pop L₂) with
      | none => pure false
      | some v => (Stack.Memory.push L₁ v).bind (fun _ => pure true))).1 = true
    rw [hanswer]
    rfl
  have hbodyState : (Memory.spec 0).clientState s (transferBody ((L₁, L₂), true)) = b := by
    change ((Memory.spec 0).runClient s ((Stack.Memory.pop L₂).bind _)).2.1 = b
    rw [StateTransitionSpec.runClient_bind]
    change ((Memory.spec 0).runClient a
      (match (Memory.spec 0).clientResult s (Stack.Memory.pop L₂) with
      | none => pure false
      | some v => (Stack.Memory.push L₁ v).bind (fun _ => pure true))).2.1 = b
    rw [hanswer]
    rfl
  have hpopcost : memoryCost (Stack.Memory.pop L₂) s = 3 := by
    simp [memoryCost, StateTransitionSpec.clientHistory, hpoprun]
  have hpushcost : memoryCost (Stack.Memory.push L₁ v) a = 3 := by
    simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.runClient_push]
  have hcost : memoryCost (transferBody ((L₁, L₂), true)) s = 6 := by
    change memoryCost ((Stack.Memory.pop L₂).bind _) s = 6
    rw [memoryCost_bind, hanswer]
    change memoryCost (Stack.Memory.pop L₂) s +
      memoryCost ((Stack.Memory.push L₁ v).bind (fun _ => pure true)) a = 6
    rw [memoryCost_bind, hpopcost, hpushcost]
    rfl
  exact ⟨hsafe, hbodyState.symm ▸ hwb, hbodyState.symm ▸ hInvFrontB,
    hbodyState.symm ▸ hInvRearB, hbodyState.symm ▸ hrear, hbodyState.symm ▸ hfront,
    hbodyResult, hcost⟩

/-- Disjoint allocated stacks within the combined capacity discharge the native transfer's
actual intermediate domains. Transferring the rear count performs exactly six memory units per
item, retains both storage invariants and moves every rear item into the front. -/
theorem transfer_invariant {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    let p := iterate transferBody (L₁, L₂) n true
    let s' := (Memory.spec 0).clientState s p
    iterationSafe transferBody transferSafe w (L₁, L₂) n true s ∧
      Memory.WellFormed w s' ∧ Stack.Memory.Inv L₁ s' ∧ Stack.Memory.Inv L₂ s' ∧
      s'.mem L₂.count.base = 0 ∧ s'.mem L₁.count.base = s.mem L₁.count.base + n ∧
      memoryCost p s = 6 * n := by
  induction n generalizing s with
  | zero => exact ⟨trivial, hw, hs₁, hs₂, hn, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hsafe, hw₁, hi₁, hi₂, hn₁, hf₁, hresult, hcost₁⟩ :=
      transfer_step h₁ h₂ hd hw hs₁ hs₂ hn hlen
    let s₁ := (Memory.spec 0).clientState s (transferBody ((L₁, L₂), true))
    have hlen₁ : s₁.mem L₁.count.base + s₁.mem L₂.count.base ≤ C := by
      rw [hn₁, hf₁]
      omega
    obtain ⟨hsafe', hw', hi₁', hi₂', hn', hf', hcost'⟩ := ih hw₁ hi₁ hi₂ hn₁ hlen₁
    have hstate : (Memory.spec 0).clientState s (iterate transferBody (L₁, L₂) (n + 1) true) =
        (Memory.spec 0).clientState s₁ (iterate transferBody (L₁, L₂) n true) := by
      change (Memory.spec 0).clientState s ((transferBody ((L₁, L₂), true)).bind
        (iterate transferBody (L₁, L₂) n)) = _
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
      change (Memory.spec 0).clientState s₁
        (iterate transferBody (L₁, L₂) n ((Memory.spec 0).clientResult s
          (transferBody ((L₁, L₂), true)))) = _
      rw [hresult]
    have hfront : ((Memory.spec 0).clientState s₁ (iterate transferBody (L₁, L₂) n true)).mem
        L₁.count.base = s.mem L₁.count.base + (n + 1) := by
      rw [hf', hf₁]
      omega
    refine ⟨⟨hsafe, ?_⟩, hstate.symm ▸ hw', hstate.symm ▸ hi₁', hstate.symm ▸ hi₂',
      hstate.symm ▸ hn', hstate.symm ▸ hfront, ?_⟩
    · simpa only [hresult] using hsafe'
    · change memoryCost ((transferBody ((L₁, L₂), true)).bind
        (iterate transferBody (L₁, L₂) n)) s = _
      rw [memoryCost_bind, hresult, hcost₁, hcost']
      omega

/-- The existing linked transfer has the same six-units-per-item memory history as the certified
bounded loop. This statement counts memory units; the next lemma pays the actual local work. -/
theorem source_transfer_cost {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    memoryCost (link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n)) s = 6 * n := by
  obtain ⟨_, _, _, _, _, _, hcost⟩ := transfer_invariant h₁ h₂ hd hw hs₁ hs₂ hn hlen
  rw [transfer_eq_iterate, memoryCost_bind]
  change memoryCost (iterate transferBody (L₁, L₂) n true) s + 0 = _
  exact hcost

/-- The explicit native loop grading is dominated by memory charge only when the fuel is the
actual rear count and the storage invariants hold. Oversized inactive tails are not free. -/
theorem source_transfer_work_bound {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    40 * n + 1 ≤ 7 * memoryCost
      (link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n)) s + 1 := by
  rw [source_transfer_cost h₁ h₂ hd hw hs₁ hs₂ hn hlen]
  omega

/-- A concrete combined-currency envelope for the actual transfer certificate. Its local work
is the grading supplied by `realizes_source_transfer`, with the same invariant assumptions. -/
theorem source_transfer_combined_bound {L₁ L₂ : Stack.Memory.Layout} {w C n : ℕ}
    (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint)
    {s : Memory.State} (hw : Memory.WellFormed w s)
    (hs₁ : Stack.Memory.Inv L₁ s) (hs₂ : Stack.Memory.Inv L₂ s)
    (hn : s.mem L₂.count.base = n)
    (hlen : s.mem L₁.count.base + s.mem L₂.count.base ≤ C) :
    combinedCost (link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n))
        (fun _ => 40 * n + 1) s ≤
      8 * memoryCost (link (Stack.Memory.pairMethods L₁ L₂ w C) (Queue.transfer n)) s + 1 := by
  have h := source_transfer_work_bound h₁ h₂ hd hw hs₁ hs₂ hn hlen
  simp only [combinedCost]
  omega

end Cslib.WordRAM.Realization.MemoryQueue
