/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Resource
public import Mathlib.Data.List.TakeDrop

/-!
# Timeline editing by reset and replay

This is the elementary rebuilding transformation motivated by retroactive data structures
[Demaine, Iacono, and Langerman][DIL2007]. A timeline edit is followed by an explicit reset and
replay of the edited history. It is not an efficient rollback algorithm or a historical-query
interface. Editing an admissible timeline can make later operations invalid, so admissibility
checks the entire edited history.

## Main definitions

* `TimelineEdit`: insertion and deletion by position.
* `Retroactive.spec`: the abstract timeline-editing specification.
* `Retroactive.backend`: an interface exposing edit, reset, and ordinary operations.
* `Retroactive.implementation`: the reusable rebuilding module.

## Main results

* `Retroactive.replay_run`: replay has exactly the ordinary history's state and operations.
* `Retroactive.operation_charge`: costs include editing, reset, and the entire replay.
* `Retroactive.realized_bound`: the same bound transports to every backend realization.
* `Retroactive.realized_linear_bound`: an ordinary-operation bound gives linear replay overhead.

The edit primitive includes storing the timeline and exposing the edited list to its caller.
A backend must certify this primitive's resource weight; list copying is not assumed constant
time. Like all `Spec.Client` results, the resource claims count explicit backend operations and
leave pure Lean controller computation uncharged. There is no fixed Word-RAM compiler here.

## References

* [E. D. Demaine, J. Iacono, and S. Langerman, *Retroactive Data Structures*][DIL2007]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

open Cslib.Stateful

/-- An edit position names a gap for insertion and an existing entry for deletion. -/
inductive TimelineEdit (Op : Type) where
  | insert (position : Nat) (operation : Op)
  | erase (position : Nat)

namespace TimelineEdit

variable {Op : Type}

/-- Edit the operation sequence. `Valid` excludes out-of-range positions. -/
def apply (e : TimelineEdit Op) (os : List Op) : List Op :=
  match e with
  | .insert i o => os.take i ++ o :: os.drop i
  | .erase i => os.take i ++ os.drop (i + 1)

/-- Insertion allows the final gap; deletion requires an existing entry. -/
def Valid (e : TimelineEdit Op) (os : List Op) : Prop :=
  match e with
  | .insert i _ => i ≤ os.length
  | .erase i => i < os.length

/-- A valid insertion increases the timeline length by one. -/
theorem length_insert (os : List Op) (i : Nat) (o : Op) (hi : i ≤ os.length) :
    ((TimelineEdit.insert i o).apply os).length = os.length + 1 := by
  simp only [apply, List.length_append, List.length_take, List.length_cons,
    List.length_drop, Nat.min_eq_left hi]
  omega

/-- A valid deletion removes exactly one operation. -/
theorem length_erase (os : List Op) (i : Nat) (hi : i < os.length) :
    ((TimelineEdit.erase i).apply os).length + 1 = os.length := by
  simp only [apply, List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left (Nat.le_of_lt hi)]
  omega

end TimelineEdit

namespace Retroactive

variable (D : Spec.{0, 0, 0}) (initial : D.State)

/-- A dynamic specification of admissible timeline edits. -/
abbrev spec : Spec where
  State := List D.Op
  Op := TimelineEdit D.Op
  Result := fun _ => Unit
  step os e := (e.apply os, ())
  valid os e := e.Valid os ∧ D.ValidHistory initial (e.apply os)

/-- Primitive operations required by rebuilding; editing returns the entire new timeline. -/
inductive BackendOp (Op : Type) where
  | edit (change : TimelineEdit Op)
  | reset
  | execute (operation : Op)

/-- The rebuilding backend tracks the stored timeline and current ordinary state separately. -/
abbrev backend : Spec where
  State := List D.Op × D.State
  Op := BackendOp D.Op
  Result
    | .edit _ => List D.Op
    | .reset => Unit
    | .execute o => D.Result o
  step s
    | .edit e => ((e.apply s.1, s.2), e.apply s.1)
    | .reset => ((s.1, initial), ())
    | .execute o => let r := D.step s.2 o; ((s.1, r.1), r.2)
  valid s
    | .edit e => e.Valid s.1 ∧ D.ValidHistory initial (e.apply s.1)
    | .reset => True
    | .execute o => D.valid s.2 o

/-- Replay ordinary operations through explicitly charged backend calls. -/
def replay : List D.Op → (backend D initial).Client Unit
  | [] => .pure ()
  | o :: os => .liftBind (.execute o) fun _ => replay os

/-- Editing, reset, and replay are distinct calls in the interface client. -/
def methods : Methods (spec D initial) (backend D initial) :=
  fun e => .liftBind (.edit e) fun os => .liftBind .reset fun _ => replay D initial os

/-- Replay preserves the stored timeline and has precisely the original operation trace. -/
theorem replay_run (timeline os : List D.Op) (s : D.State) :
    (backend D initial).runClient (timeline, s) (replay D initial os) =
      ((), (timeline, (D.run s os).1), os.map BackendOp.execute) := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp [replay, backend, ih]

/-- Every admissible ordinary history is admissible when executed through the backend. -/
theorem replay_valid (timeline os : List D.Op) (s : D.State)
    (h : D.ValidHistory s os) :
    (backend D initial).ValidHistory (timeline, s) (os.map BackendOp.execute) := by
  induction os generalizing s with
  | nil => trivial
  | cons o os ih => exact ⟨h.1, ih _ h.2⟩

/-- Rebuilding correctness is independent of the implementation of reset, edit, and execution. -/
def implementation : Module (spec D initial) (backend D initial) where
  methods := methods D initial
  rep os s := s.1 = os ∧ s.2 = (D.run initial os).1
  valid {s e} o hr hv := by
    obtain ⟨timeline, state⟩ := e
    obtain ⟨ht, hs⟩ := hr
    dsimp only at ht hs
    subst timeline
    change (backend D initial).ValidHistory (s, state)
      (.edit o :: .reset ::
        ((backend D initial).runClient (o.apply s, initial) (replay D initial (o.apply s))).2.2)
    rw [replay_run]
    exact ⟨hv, trivial, replay_valid D initial _ _ _ hv.2⟩
  correct {s e} o hr _ := by
    obtain ⟨timeline, state⟩ := e
    obtain ⟨ht, hs⟩ := hr
    dsimp only at ht hs
    subst timeline
    simp only [methods, Spec.runClient_liftBind, backend]
    rw [replay_run]
    exact ⟨trivial, rfl, rfl⟩

/-- Separate charges for timeline editing, resetting, and ordinary operations. -/
def primitiveCharge (editCharge : List D.Op → TimelineEdit D.Op → Nat)
    (resetCharge : Nat) (ordinaryCharge : D.State → D.Op → Nat)
    (s : (backend D initial).State) : (backend D initial).Op → Nat
  | .edit e => editCharge s.1 e
  | .reset => resetCharge
  | .execute o => ordinaryCharge s.2 o

/-- Charges for replay are exactly the charges for the ordinary history. -/
private theorem replay_charge (editCharge : List D.Op → TimelineEdit D.Op → Nat)
    (resetCharge : Nat) (ordinaryCharge : D.State → D.Op → Nat)
    (timeline os : List D.Op) (s : D.State) :
    (backend D initial).totalCost (primitiveCharge D initial editCharge resetCharge ordinaryCharge)
      (timeline, s) (os.map BackendOp.execute) = D.totalCost ordinaryCharge s os := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, Spec.totalCost_cons, primitiveCharge, backend, ih]

/-- The full operation charge retains both editing and resetting overhead. -/
theorem operation_charge (editCharge : List D.Op → TimelineEdit D.Op → Nat)
    (resetCharge : Nat) (ordinaryCharge : D.State → D.Op → Nat)
    (timeline : List D.Op) (state : D.State) (e : TimelineEdit D.Op) :
    (backend D initial).totalCost (primitiveCharge D initial editCharge resetCharge ordinaryCharge)
      (timeline, state)
      ((backend D initial).runClient (timeline, state) (methods D initial e)).2.2 =
      editCharge timeline e + resetCharge +
        D.totalCost ordinaryCharge initial (e.apply timeline) := by
  simp only [methods, Spec.runClient_liftBind, backend]
  rw [replay_run]
  change editCharge timeline e + (resetCharge +
    (backend D initial).totalCost
      (primitiveCharge D initial editCharge resetCharge ordinaryCharge)
      (e.apply timeline, initial) ((e.apply timeline).map BackendOp.execute)) = _
  rw [replay_charge, Nat.add_assoc]

/-- Resource bounds transport to any realization of the backend interface.
This certificate then composes across arbitrary admissible timeline edits via `Bound.client`. -/
theorem realized_bound {C Trace : Type} {exec : Execution (backend D initial) C Trace}
    (R : Realization (backend D initial) exec) (weight : Trace → Nat)
    (editCharge : List D.Op → TimelineEdit D.Op → Nat) (resetCharge : Nat)
    (ordinaryCharge : D.State → D.Op → Nat)
    (B : Bound R weight (primitiveCharge D initial editCharge resetCharge ordinaryCharge)) :
    Bound ((implementation D initial).realize R) (total weight)
      (fun os e => editCharge os e + resetCharge +
        D.totalCost ordinaryCharge initial (e.apply os)) := by
  apply (implementation D initial).bound R B
  intro s e o hr hv
  obtain ⟨timeline, state⟩ := e
  obtain ⟨ht, _⟩ := hr
  dsimp only at ht
  subst timeline
  exact (operation_charge D initial editCharge resetCharge ordinaryCharge s state o).le

/-- A uniform ordinary-operation bound gives linear replay overhead. Editing and resetting
remain explicit, and the resulting certificate applies to every concrete operation execution. -/
theorem realized_linear_bound {C Trace : Type} {exec : Execution (backend D initial) C Trace}
    (R : Realization (backend D initial) exec) (weight : Trace → Nat)
    (editCharge : List D.Op → TimelineEdit D.Op → Nat) (resetCharge : Nat)
    (ordinaryCharge : D.State → D.Op → Nat)
    (B : Bound R weight (primitiveCharge D initial editCharge resetCharge ordinaryCharge))
    (T : Nat) (hT : ∀ s o, D.valid s o → ordinaryCharge s o ≤ T) :
    Bound ((implementation D initial).realize R) (total weight)
      (fun os e => editCharge os e + resetCharge + (e.apply os).length * T) := by
  apply (implementation D initial).bound R B
  intro s e o hr hv
  obtain ⟨timeline, state⟩ := e
  obtain ⟨ht, _⟩ := hr
  dsimp only at ht
  subst timeline
  calc
    _ = editCharge s o + resetCharge + D.totalCost ordinaryCharge initial (o.apply s) :=
      operation_charge D initial editCharge resetCharge ordinaryCharge s state o
    _ ≤ _ := Nat.add_le_add_left
      (D.totalCost_le_length_mul ordinaryCharge T hT hv.2) _

end Retroactive
end Cslib.Algorithms.Lean
