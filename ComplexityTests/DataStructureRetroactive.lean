/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Retroactive

/-!
# Reset-and-replay contract tests

A counter admits decrement only when nonzero. This makes history admissibility nontrivial:
deleting an increment can invalidate a later decrement. The concrete test backend executes
mathematical state transitions and records primitive operation tags. Weight one counts those
calls; it does not assert that editing an arbitrary list or resetting storage takes constant
machine time.
-/

@[expose] public section

namespace ComplexityTests.DataStructureRetroactive

open Cslib.Stateful Cslib.Algorithms.Lean

/-- `true` increments; `false` decrements a positive counter. -/
abbrev counter : Spec :=
  Spec.ofFn (State := Nat) (Op := Bool) (Result := fun _ => Unit)
    (fun n op => (if op then n + 1 else n - 1, ()))
    (fun n op => if op then True else 0 < n)

/-- The primitive interface manages the operation timeline and the counter. -/
abbrev lower : Spec := Retroactive.backend counter 0

/-- Direct mathematical execution with the actual primitive operation as its event. -/
def execution : Execution lower lower.State lower.Op :=
  fun c o a c' event => (c', a) = lower.stepFn c o ∧ event = o

/-- A nonempty realization of every primitive contract. -/
def realization : Realization lower execution :=
  Realization.ofFn Eq
    (fun o hr _ => by
      subst hr
      exact ⟨(lower.stepFn _ o).2, (lower.stepFn _ o).1, o, rfl, rfl⟩)
    (fun hr _ he => by
      subst hr
      exact ⟨congrArg Prod.snd he.1, (congrArg Prod.fst he.1).symm⟩)

/-- The trace records one event per primitive call. -/
theorem primitive_calls : Bound realization (fun _ => 1)
    (Retroactive.primitiveCharge counter 0 (fun _ _ => 1) 1 (fun _ _ => 1)) :=
  fun {_ _ o _ _ _} _ _ _ => by cases o <;> exact Nat.le_refl 1

/-- Insertions retain both incremental and decremental operations. -/
example : (Retroactive.spec counter 0).ValidHistory []
    [.insert 0 true, .insert 1 false] := by
  simp [TimelineEdit.apply, TimelineEdit.Valid, counter]

/-- Deleting the increment makes the retained decrement inadmissible. -/
example : ¬ (Retroactive.spec counter 0).valid [true, false] (.erase 0) := by
  simp [TimelineEdit.apply, TimelineEdit.Valid, counter]

/-- Deleting the decrement remains admissible. -/
example : (Retroactive.spec counter 0).valid [true, false] (.erase 1) := by
  simp [TimelineEdit.apply, TimelineEdit.Valid, counter]

/-- The composed realization inherits correctness without reproving counter semantics. -/
def rebuilt := (Retroactive.implementation counter 0).realize realization

/-- This edit client creates a valid increment/decrement timeline and then removes the decrement. -/
def edits : (Retroactive.spec counter 0).Client Unit :=
  .liftBind (.insert 0 true) fun _ =>
    .liftBind (.insert 1 false) fun _ => .liftBind (.erase 1) fun _ => .pure ()

/-- Every edit sequence below includes its edit call, reset call, and full replay. -/
example : (lower.runClient ([], 0)
    (link (Retroactive.methods counter 0) edits)).2.2.length = 10 := rfl

/-- The linked execution and stored ordinary state are both certified by module substitution. -/
theorem edits_execute :
    ∃ c' traces, Executes execution (link (Retroactive.methods counter 0) edits)
      ([], 0) () c' traces ∧ rebuilt.rep [true] c' := by
  obtain ⟨c', chunks, he, hr⟩ := rebuilt.exists_executes edits
    ⟨([], 0), ⟨rfl, rfl⟩, rfl⟩ (by
      change (Retroactive.spec counter 0).ValidHistory []
        [.insert 0 true, .insert 1 false, .erase 1]
      simp [TimelineEdit.apply, TimelineEdit.Valid, counter])
  exact ⟨c', chunks.flatten, link_exec _ _ he, hr⟩

/-- The same resource certificate bounds every supplied execution, not just a chosen run. -/
theorem edits_bound {c' : lower.State} {traces : List lower.Op}
    (he : Executes execution (link (Retroactive.methods counter 0) edits)
      ([], 0) () c' traces) : traces.length ≤ 10 := by
  obtain ⟨chunks, hc, ht⟩ := link_exec_decompose _ _ he
  have B : Bound rebuilt (total (fun _ : lower.Op => 1))
      (fun os e => 1 + 1 + counter.totalCost (fun _ _ => 1) 0 (e.apply os)) :=
    Retroactive.realized_bound counter 0 realization (fun _ => 1)
      (fun _ _ => 1) 1 (fun _ _ => 1) primitive_calls
  have hb := B.client (p := edits) (s := [])
    ⟨([], 0), ⟨rfl, rfl⟩, rfl⟩ (by
      change (Retroactive.spec counter 0).ValidHistory []
        [.insert 0 true, .insert 1 false, .erase 1]
      simp [TimelineEdit.apply, TimelineEdit.Valid, counter]) hc
  change total (total (fun _ : lower.Op => 1)) chunks ≤ 10 at hb
  rw [ht]
  rw [← total_flatten] at hb
  have hlen : ∀ xs : List lower.Op, total (fun _ => 1) xs = xs.length := by
    intro xs; induction xs <;> simp_all [Nat.add_comm]
  simpa only [hlen] using hb

/--
info: 'Cslib.Algorithms.Lean.Retroactive.implementation' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Retroactive.implementation
/--
info: 'Cslib.Algorithms.Lean.Retroactive.operation_charge' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Retroactive.operation_charge
/--
info: 'Cslib.Algorithms.Lean.Retroactive.realized_bound' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Retroactive.realized_bound
/--
info: 'ComplexityTests.DataStructureRetroactive.edits_execute' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureRetroactive.edits_execute
/--
info: 'ComplexityTests.DataStructureRetroactive.edits_bound' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureRetroactive.edits_bound

end ComplexityTests.DataStructureRetroactive
