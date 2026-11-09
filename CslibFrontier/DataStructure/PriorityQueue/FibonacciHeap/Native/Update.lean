/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Memory
import CslibFrontier.DataStructure.Memory.RecordLink
import CslibFrontier.Computability.WordRAM.Realization.Reindex
import CslibFrontier.Tactic.Realize

/-!
# Native updates of the indexed Fibonacci heap

The original linked record source is compiled through the existing realization rules. The
lexicographic priority test is distributed into ordinary word comparisons using `ite_or` and
`ite_and`, without changing the program. The certificate retains its intrinsic source-history
admissibility contract; the existing heap refinement supplies that contract for indexed-queue
clients. These blocks do not constitute a complete native method family.

## Main definitions

* `cutSafe`: the native cut's arithmetic and reached-state splice conditions.

## Main results

* `realizes_addRoot`: a uniform runtime `[capacity, base, handle]` root insertion certificate.
* `realizes_insert`: the original complete insertion from `[capacity, base, handle, key]`.
* `realizes_unlink`: the original child-list unlink, with its positive-degree domain explicit.
* `realizes_setKey`: store a lowered key and update the minimum using the original priority test.
* `realizes_toRoot`: the original root splice with explicit pointer and subtraction domains.
* `realizes_cut`: compose unlinking and the root splice at the actual intermediate memory.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- Compile the existing lexicographic priority predicate as native word comparisons. The
same normalization applies to record and memory source branches. -/
theorem priority_if {α : Type} (u ku p kp : ℕ) (yes no : α) :
    (if IndexedMinPQ.RawPrioLT (u, ku) (p, kp) then yes else no) =
      if ku < kp then yes else if ku = kp then if u < p then yes else no else no := by
  change (if ku < kp ∨ ku = kp ∧ u < p then yes else no) = _
  rw [ite_or, ite_and]

private theorem bind_if (P : Prop) [Decidable P] (yes no : Prog Unit) (k : Unit → Prog Unit) :
    (if P then yes else no) >>= k = if P then yes >>= k else no >>= k :=
  apply_ite (fun p : Prog Unit => p >>= k) _ _ _

/-- Execute the original root-list insertion with paid arithmetic and priority comparisons.
The emitter is fixed before capacity, base, handle, width or memory. -/
private theorem realizes_addRoot_history : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (addRoot (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (addRoot (d 2))))) (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    arg 2
    simp only [addRoot, spliceAfter]
    simp only [priority_if]
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.bind_eq_bind, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift,
      PFunctor.FreeM.liftM_pure, pure_bind, Record.lift_ite, bind_if, Record.Layout.methods, layout]
  realize
  all_goals try simp only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult,
    StateTransitionSpec.clientState,
    StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_lift_bind',
    Memory.read, Memory.write, Memory.step_read, Memory.step_write] at *
  all_goals try first
    | exact h.1.of_le (by have := h.2.1; omega)
    | omega
  all_goals
    have hv := h.2.2
    simp only [DataStructure.link, addRoot, spliceAfter, rd, wr,
      PFunctor.FreeM.liftM_bind, Record.Layout.lift_read, Record.Layout.lift_write,
      Record.lift_ite, priority_if, layout] at hv
    simp only [StateTransitionSpec.clientHistory, bind_assoc,
      StateTransitionSpec.runClient_lift_bind', Memory.read, Memory.write,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.step_read,
      Memory.valid] at hv
    have hfit := h.1
    have hlt := h.2.1
    clear h
    simp_all only [ite_true, ite_false, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.runClient_lift, StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.validHistory_nil, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.step_write, Memory.valid]
  all_goals
    have hfront := hmem.frontier_fits
    simp only [Fits] at hv hfront ⊢
    omega

/-- The original root-list insertion, retaining the certificate's intrinsic admissible-history
contract. Capacity, base and handle are runtime words, and the local work is absorbed. -/
theorem realizes_addRoot : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (addRoot (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) :=
  realizes_addRoot_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h.1, h.2, hv⟩)

private def insertPrefix (d : Fin 4 → ℕ) : Memory.Prog Unit :=
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) do
    wr (.key (d 2)) (d 3)
    wr (.par (d 2)) 0
    wr (.child (d 2)) 0
    wr (.deg (d 2)) 0
    wr (.mark (d 2)) 0
    wr (.inHeap (d 2)) 1

private theorem realizes_insertPrefix : Realizes .exact insertPrefix
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) := by
  unfold insertPrefix
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, wr, Record.write, PFunctor.FreeM.liftM_bind,
      PFunctor.FreeM.liftM_lift, Record.Layout.methods, layout]
  realize
  all_goals exact h.1.of_le (by have := h.2; omega)

private def incrementSize (d : Fin 4 → ℕ) : Memory.Prog Unit :=
  DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0) do
    let c ← rd .sz
    wr .sz (c + 1)

private theorem realizes_incrementSize_history : Realizes .exact incrementSize
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => (Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (incrementSize d)))
    (fun _ _ => 0) := by
  unfold incrementSize
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift, Record.Layout.methods, layout]
  realize
  all_goals try exact h.1.1.of_le (by have := h.1.2; omega)
  all_goals
    have hv := h.2
    change _ ∧ (_ ∧ Fits w (s.mem (d 1 + 9 * d 0 + 4) + 1)) ∧ True at hv
    exact hv.2.1.2

private theorem realizes_incrementSize : Realizes .exact incrementSize
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) :=
  realizes_incrementSize_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Compose the existing node writes, root-list insertion and size increment. Runtime words
select data and addresses, while one emitter precedes all capacities, widths and memories. -/
theorem realizes_insert : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (insert (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) := by
  have hr := realizes_addRoot.reindex
    (fun d : (Fin 4 → ℕ) × Unit => ![d.1 0, d.1 1, d.1 2])
    (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
    ![0, 1, 2] (by intro d i; fin_cases i <;> rfl)
  have hs := realizes_incrementSize.reindex
    (fun d : (Fin 4 → ℕ) × Unit => d.1)
    (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
    ![0, 1, 2, 3] (by intro d i; fin_cases i <;> rfl)
  refine ((realizes_insertPrefix.bind₀ hr).bind₀ hs).congr (fun d => ?_) |>.consequence ?_
    (fun _ _ => le_rfl)
  · simp only [insertPrefix, incrementSize, DataStructure.link, insert,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.bind_eq_bind, bind_assoc,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · intro w d s _ _ h
    exact ⟨⟨h, h⟩, h⟩

private theorem realizes_unlink_history : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (unlink (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s =>
      (Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧ d 3 < d 0 ∧
        1 ≤ s.mem (d 1 + 5 * d 0 + d 3)) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (unlink (d 2) (d 3))))) (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, unlink, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift, Record.lift_ite,
      Record.Layout.methods, layout]
  realize
  all_goals try simp only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult,
    StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift, Memory.read, Memory.write,
    Memory.step_read, Memory.step_write] at *
  all_goals try first
    | exact h.1.1.of_le (by have := h.1.2.1; have := h.1.2.2.1; omega)
    | exact h.1.2.2.2
    | omega
  all_goals
    have hv := h.2
    have hdeg := h.1.2.2.2
    clear h
    simp only [DataStructure.link, unlink, rd, wr, PFunctor.FreeM.liftM_bind,
      Record.Layout.lift_read, Record.Layout.lift_write, Record.lift_ite, layout] at hv
    simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.runClient_lift, StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.validHistory_nil, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid, ite_false]
  all_goals
    have hfront := hmem.frontier_fits
    simp only [Fits] at hv hfront ⊢
    omega

/-- Unlink a child using runtime `[capacity, base, child, parent]`. Exact subtraction uses
the existing positive-parent-degree premise; this certificate does not assert a valid cut
from arbitrary memory. The original source history remains an intrinsic execution premise. -/
theorem realizes_unlink : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (unlink (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧ d 3 < d 0 ∧
      1 ≤ s.mem (d 1 + 5 * d 0 + d 3)) (fun _ _ => 0) :=
  realizes_unlink_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem realizes_setKey_history : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (setKey (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s =>
      (Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
        1 ≤ s.mem (d 1 + 9 * d 0 + 1)) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (setKey (d 2) (d 3))))) (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    arg 2
    simp only [setKey, priority_if]
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift, PFunctor.FreeM.liftM_pure,
      Record.lift_ite, Record.Layout.methods, layout]
  realize
  all_goals
    have haddr : d 1 + 9 * d 0 + 1 ≠ d 1 + d 2 := by have := h.1.2.1; omega
    try simp only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
      Memory.read, Memory.write, Memory.step_read, Memory.step_write,
      Function.update_of_ne haddr] at *
  all_goals try first
    | exact h.1.1.of_le (by have := h.1.2.1; omega)
    | exact h.1.2.2
    | omega
  all_goals
    have hv := h.2
    clear h
    simp only [DataStructure.link, setKey, rd, wr, priority_if,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure, Record.Layout.lift_read,
      Record.Layout.lift_write,
      Record.lift_ite, layout] at hv
    simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid,
      Function.update_of_ne haddr]
  all_goals
    have hfront := hmem.frontier_fits
    simp only [Fits] at hv hfront ⊢
    omega

/-- Store the runtime key and perform the original minimum-root priority comparison. The
positive minimum pointer makes exact subtraction defined; heap correctness supplies this
domain when decreasing a present key. This is a source block, not a complete decrease-key. -/
theorem realizes_setKey : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (setKey (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
      1 ≤ s.mem (d 1 + 9 * d 0 + 1)) (fun _ _ => 0) :=
  realizes_setKey_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private theorem realizes_toRoot_history : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (toRoot (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s =>
      (Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
        1 ≤ s.mem (d 1 + 9 * d 0 + 1) ∧ s.mem (d 1 + 9 * d 0 + 1) ≤ d 0 ∧
        s.mem (d 1 + 4 * d 0 + (s.mem (d 1 + 9 * d 0 + 1) - 1)) < d 0 ∧
        s.mem (d 1 + 6 * d 0 + d 2) ≤ s.mem (d 1 + 9 * d 0 + 3)) ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (toRoot (d 2))))) (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, toRoot, spliceAfter, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift, Record.Layout.methods, layout]
  realize
  all_goals
    rcases h with ⟨⟨hfit, hz, hmpos, hmn, hr, hmark⟩, hv⟩
    try simp only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
      StateTransitionSpec.runClient_lift_bind', Memory.read, Memory.write,
      Memory.step_read, Memory.step_write] at *
    try simp (disch := omega) only [Function.update_of_ne] at *
  all_goals try first
    | exact hfit.of_le (by omega)
    | exact hmpos
    | exact hmark
    | omega
  all_goals
    simp only [DataStructure.link, toRoot, spliceAfter, rd, wr, PFunctor.FreeM.liftM_bind,
      Record.Layout.lift_read, Record.Layout.lift_write, layout] at hv
    simp (disch := omega) only [StateTransitionSpec.clientHistory, bind_assoc,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.runClient_lift,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read,
      Memory.step_write, Memory.valid, Function.update_of_ne] at hv
    simp_all only []

/-- Move the detached handle into the root list using its original memory source. The minimum
and its right neighbour are actual handle words; the mark/count inequality makes exact
subtraction defined. These are reached-state obligations for a cut, not a new heap model. -/
theorem realizes_toRoot : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (toRoot (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
      1 ≤ s.mem (d 1 + 9 * d 0 + 1) ∧ s.mem (d 1 + 9 * d 0 + 1) ≤ d 0 ∧
      s.mem (d 1 + 4 * d 0 + (s.mem (d 1 + 9 * d 0 + 1) - 1)) < d 0 ∧
      s.mem (d 1 + 6 * d 0 + d 2) ≤ s.mem (d 1 + 9 * d 0 + 3)) (fun _ _ => 0) :=
  realizes_toRoot_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- Arithmetic and root-list domains of the native cut. The intermediate state is the actual
original unlink run. This records compilation side conditions, not a replacement for the
forest invariant or for the certificate's intrinsic source-history admissibility premise. -/
@[expose] def cutSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧ d 3 < d 0 ∧
    1 ≤ s.mem (d 1 + 5 * d 0 + d 3) ∧
    let s' := (Memory.spec 0).clientState s
      (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
        (unlink (d 2) (d 3)))
    1 ≤ s'.mem (d 1 + 9 * d 0 + 1) ∧ s'.mem (d 1 + 9 * d 0 + 1) ≤ d 0 ∧
    s'.mem (d 1 + 4 * d 0 + (s'.mem (d 1 + 9 * d 0 + 1) - 1)) < d 0 ∧
    s'.mem (d 1 + 6 * d 0 + d 2) ≤ s'.mem (d 1 + 9 * d 0 + 3)

/-- The original cut is the composition of its two native source blocks. Its root-list and
mark/count obligations concern the memory actually reached by unlinking. Transport from the
existing forest invariants remains a separate proof obligation. No native loop nontruncation
or complete decrease-key is asserted by this block certificate. -/
theorem realizes_cut : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cut (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) cutSafe (fun _ _ => 0) := by
  unfold cutSafe
  have ht := realizes_toRoot.reindex
    (fun d : (Fin 4 → ℕ) × Unit => ![d.1 0, d.1 1, d.1 2])
    (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
    ![0, 1, 2] (by intro d i; fin_cases i <;> rfl)
  refine (realizes_unlink.bind₀ ht).congr (fun d => ?_) |>.consequence ?_
    (fun _ _ => le_rfl)
  · simp only [DataStructure.link, cut, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.bind_eq_bind,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · intro w d s _ _ h
    exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
      h.1, h.2.1, h.2.2.2.2⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
