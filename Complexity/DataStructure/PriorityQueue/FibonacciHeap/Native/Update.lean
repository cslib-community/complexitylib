/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Memory
import Complexity.Computability.WordRAM.Realization.Reindex
import Complexity.Tactic.Realize

/-!
# Native updates of the indexed Fibonacci heap

The original linked record source is compiled through the existing realization rules. The
lexicographic priority test is distributed into ordinary word comparisons using `ite_or` and
`ite_and`, without changing the program. The certificate retains its intrinsic source-history
admissibility contract; the existing heap refinement supplies that contract for indexed-queue
clients. These blocks do not constitute a complete native method family.

## Main results

* `realizes_addRoot`: a uniform runtime `[capacity, base, handle]` root insertion certificate.
* `realizes_insert`: the original complete insertion from `[capacity, base, handle, key]`.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization

private theorem lift_read {ok : Cell → Prop} (L : Record.Layout ok) (i : Cell) :
    (PFunctor.FreeM.liftM (L.methods 0) (Record.read i) : Memory.Prog ℕ) =
      Memory.read (L.addr i) := rfl

private theorem lift_write {ok : Cell → Prop} (L : Record.Layout ok) (i : Cell) (k : ℕ) :
    (PFunctor.FreeM.liftM (L.methods 0) (Record.write i k) : Memory.Prog Unit) =
      Memory.write (L.addr i) k := rfl

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
  have hbranch (u ku p kp : ℕ) (yes no : Prog Unit) :
      (if IndexedMinPQ.RawPrioLT (u, ku) (p, kp) then yes else no) =
        if ku < kp then yes else if ku = kp then if u < p then yes else no else no := by
    change (if ku < kp ∨ ku = kp ∧ u < p then yes else no) = _
    rw [ite_or, ite_and]
  -- Specializing distribution avoids permuting nested conditionals with an unrestricted
  -- `apply_ite` simp rule.
  have hmapIf (interp : (o : Record.Op Cell) → Memory.Prog (Record.Op.Result o))
      (P : Prop) [Decidable P] (yes no : Prog Unit) :
      (PFunctor.FreeM.liftM interp (if P then yes else no) : Memory.Prog Unit) =
        if P then PFunctor.FreeM.liftM interp yes else PFunctor.FreeM.liftM interp no :=
    apply_ite _ _ _ _
  have hbindIf (P : Prop) [Decidable P] (yes no : Prog Unit) (k : Unit → Prog Unit) :
      (if P then yes else no) >>= k = if P then yes >>= k else no >>= k :=
    apply_ite (fun p : Prog Unit => p >>= k) _ _ _
  conv =>
    arg 2
    ext d
    arg 2
    simp only [addRoot, spliceAfter]
    simp only [hbranch]
  conv =>
    arg 2
    ext d
    simp only [DataStructure.link, rd, wr, Record.read, Record.write,
      PFunctor.FreeM.bind_eq_bind, PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_lift,
      PFunctor.FreeM.liftM_pure, pure_bind, hmapIf, hbindIf, Record.Layout.methods, layout]
  realize
  all_goals try simp only [lift_read, lift_write, StateTransitionSpec.clientResult,
    StateTransitionSpec.clientState,
    StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_lift_bind',
    Memory.read, Memory.write, Memory.step_read, Memory.step_write] at *
  all_goals try first
    | exact h.1.of_le (by have := h.2.1; omega)
    | omega
  all_goals
    have hv := h.2.2
    simp only [DataStructure.link, addRoot, spliceAfter, rd, wr,
      PFunctor.FreeM.liftM_bind, lift_read, lift_write, hmapIf, hbranch, layout] at hv
    simp only [StateTransitionSpec.clientHistory, bind_assoc,
      StateTransitionSpec.runClient_lift_bind', Memory.read, Memory.write,
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.step_read,
      Memory.valid] at hv
    have hfit := h.1
    have hlt := h.2.1
    clear h hbranch hmapIf hbindIf
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

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
