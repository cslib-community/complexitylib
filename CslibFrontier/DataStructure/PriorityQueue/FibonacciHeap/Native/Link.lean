/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Update
import CslibFrontier.Tactic.Realize
import CslibFrontier.DataStructure.Memory.RecordLink

/-!
# Native consolidation links

The existing root-linking source runs through the shared realization rules. The native domain
retains the positive child pointer required by exact subtraction; the source forest supplies
it for real consolidation clients. Other query and write bounds retain intrinsic source-history
admissibility. These blocks alone do not realize the whole extraction operation.

## Main definitions

* `linkAsSafe`: handle and child-pointer domains for the original child-list insertion.

## Main results

* `realizes_linkAs`: native child-list insertion with uniform runtime capacity and layout.
* `realizes_link`: the original priority-selected root and its full child-list memory effect.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- Compilation conditions for the original root attachment. A nonempty child list must have
its original positive pointer; no extra assumption is made in the empty-child branch. -/
@[expose] def linkAsSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧ d 3 < d 0 ∧
    (s.mem (d 1 + 5 * d 0 + d 2) ≠ 0 → 1 ≤ s.mem (d 1 + 2 * d 0 + d 2))

private theorem realizes_linkAs_history : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (linkAs (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d s => linkAsSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (linkAs (d 2) (d 3))))) (fun _ _ => 0) := by
  conv =>
    arg 2
    ext d
    arg 2
    simp only [linkAs, spliceAfter]
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.bind_eq_bind, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift,
      PFunctor.FreeM.liftM_pure,
      Record.lift_ite,
      Record.Layout.methods, layout]
  realize
  all_goals
    have hu := h.1.2.1
    have hx := h.1.2.2.1
    try simp (disch := omega) only [Record.Layout.lift_read, Record.Layout.lift_write,
      StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_lift, Memory.read, Memory.write,
      Memory.step_read, Memory.step_write, Function.update_of_ne] at *
  all_goals try first
    | exact h.1.1.of_le (by have := h.1.2.1; have := h.1.2.2.1; omega)
    | exact h.1.2.2.2 (by assumption)
    | omega
  all_goals
    have hv := h.2
    have hfit := h.1.1
    clear h
    simp only [DataStructure.link, linkAs, spliceAfter, rd, wr, PFunctor.FreeM.liftM_bind,
      Record.Layout.lift_read, Record.Layout.lift_write, Record.lift_ite, layout] at hv
    simp (disch := omega) only [StateTransitionSpec.clientHistory, bind_assoc,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.runClient_lift,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.validHistory_nil,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read,
      Memory.step_write, Memory.valid, Function.update_of_ne, hc, ite_false] at hv
    have hfront := hmem.frontier_fits
    simp only [Fits] at hv hfront ⊢
    omega

/-- The original child-list source, keeping its native subtraction domain and intrinsic source
admissibility. Code is selected before every runtime heap and word width. -/
theorem realizes_linkAs : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (linkAs (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := Unit)) linkAsSafe (fun _ _ => 0) :=
  realizes_linkAs_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

private def linkBody (d : Fin 4 → ℕ) : Memory.Prog ℕ := do
  let ka ← Memory.read (d 1 + d 2)
  let kb ← Memory.read (d 1 + d 3)
  if IndexedMinPQ.RawPrioLT (d 3, kb) (d 2, ka) then
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (linkAs (d 3) (d 2))
    pure (d 3)
  else
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (linkAs (d 2) (d 3))
    pure (d 2)

private theorem linkBody_eq (d : Fin 4 → ℕ) : linkBody d =
    DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
      (FibonacciHeap.link (d 2) (d 3)) := by
  simp only [linkBody, FibonacciHeap.link, DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1
  funext ka
  congr 1
  funext kb
  by_cases hlt : IndexedMinPQ.RawPrioLT (d 3, kb) (d 2, ka) <;>
    simp only [hlt, ite_true, ite_false, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure]

/-- Both roots have admissible attachment domains, so either result of their original priority
comparison can be used without an extra branch-dependent representation. -/
@[expose] def linkSafe (w : ℕ) (d : Fin 4 → ℕ) (s : Memory.State) : Prop :=
  linkAsSafe w d s ∧ linkAsSafe w ![d 0, d 1, d 3, d 2] s

private theorem realizes_linkBody : Realizes .exact linkBody (.refl _)
    (WordEncoding.encode (α := ℕ)) linkSafe (fun _ _ => 0) := by
  have hRet : Realizes .exact (fun d : (Fin 4 → ℕ) × Unit => pure (d.1 2))
      (appendWords (.refl _) (WordEncoding.encode (α := Unit)))
      (WordEncoding.encode (α := ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
    realize
  have hAttach := (realizes_linkAs.bind₀ hRet).reindex
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => ![d.1.1.1, d.1.1.2, d.1.2, d.2])
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) ![0, 1, 2, 3]
    (by intro d i; fin_cases i <;> rfl)
  change Realizes .exact
    (fun d : ((ℕ × ℕ) × ℕ) × ℕ => do
      DataStructure.link (E := Memory.spec 0) ((layout d.1.1.1 d.1.1.2).methods 0)
        (linkAs d.1.2 d.2)
      pure d.1.2)
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w d s => linkAsSafe w ![d.1.1.1, d.1.1.2, d.1.2, d.2] s ∧ True)
    (fun _ _ => 0) at hAttach
  conv =>
    arg 2
    ext d
    simp only [linkBody, priority_if]
  realize
  all_goals first
    | exact h.1.1.of_le (by have := h.1.2.1; have := h.1.2.2.1; omega)
    | exact h.1
    | exact h.2

/-- Compile the original two-root link and return its actual priority-selected root. The
native source retains both key reads and the complete child-list memory effect. -/
theorem realizes_link : Realizes .exact
    (fun d : Fin 4 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (FibonacciHeap.link (d 2) (d 3)))
    (.refl _) (WordEncoding.encode (α := ℕ)) linkSafe (fun _ _ => 0) :=
  realizes_linkBody.congr linkBody_eq

/-- A real source root has the positive child pointer needed by the native attachment branch. -/
theorem linkAsSafe_of_validRoot {n w base : ℕ} {mem : Memory.State} {T : FHTree n}
    (x : Fin n) (hfit : Fits w (base + (9 * n + 5)))
    (h : ValidRoot (view n ((layout n base).abs mem)) none T) :
    linkAsSafe w ![n, base, T.root.val, x.val] mem := by
  change Fits w (base + (9 * n + 5)) ∧ T.root.val < n ∧ x.val < n ∧ _
  refine ⟨hfit, T.root.isLt, x.isLt, ?_⟩
  intro hd
  change mem.mem (base + 5 * n + T.root.val) ≠ 0 at hd
  have hd' : (view n ((layout n base).abs mem)).deg T.root ≠ 0 := by
    simpa only [view, Record.Layout.abs, Cell.ok, T.root.isLt, ite_true, layout] using hd
  obtain ⟨c, _, hc, _⟩ := ValidSubtree.exists_child h.1 hd'
  have hc' : mem.mem (base + 2 * n + T.root.val) = c.val + 1 := by
    simpa only [view, Record.Layout.abs, Cell.ok, T.root.isLt, ite_true, layout] using hc
  change 1 ≤ mem.mem (base + 2 * n + T.root.val)
  omega

/-- The individual source roots supply both native attachment domains. Disjointness and equal
degrees belong to the source consolidation theorem, not to this compiler-domain fact. -/
theorem linkSafe_of_validRoots {n w base : ℕ} {mem : Memory.State} {T S : FHTree n}
    (hfit : Fits w (base + (9 * n + 5)))
    (hT : ValidRoot (view n ((layout n base).abs mem)) none T)
    (hS : ValidRoot (view n ((layout n base).abs mem)) none S) :
    linkSafe w ![n, base, T.root.val, S.root.val] mem :=
  ⟨linkAsSafe_of_validRoot S.root hfit hT, linkAsSafe_of_validRoot T.root hfit hS⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
