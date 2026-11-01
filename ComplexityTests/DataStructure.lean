/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Semantics.Stateful.Hoare
import Complexity.Foundations.Semantics.Stateful.Amortized
import Complexity.Computability.WordRAM.Copy

namespace ComplexityTests.DataStructure

open Cslib.Stateful

/-- An addition interface whose result exposes the new state. -/
abbrev counter : Spec :=
  Spec.ofFn (State := Nat) (Op := Nat) (Result := fun _ => Nat) fun s n => (s + n, s + n)

/-- A backend operation records the requested increment. -/
def counterExec : Execution counter Nat Nat :=
  fun s n a s' trace => s' = s + n ∧ a = s' ∧ trace = n

/-- The counter has a concrete, inhabited realization independent of resource interpretation. -/
def counterRealization : Realization counter counterExec :=
  Realization.ofFn Eq (fun n hr _ => by subst hr; exact ⟨_, _, n, rfl, rfl, rfl⟩)
    (fun hr _ he => by
      subst hr
      exact ⟨he.2.1.trans he.1, he.1.symm⟩)

/-- Charge by increment magnitude. -/
theorem magnitude_bound : Bound counterRealization id (fun _ n => n) :=
  fun _ _ he => he.2.2.le

/-- The same realization also admits a call-count interpretation. -/
theorem call_bound : Bound counterRealization (fun _ => 1) (fun _ _ => 1) :=
  fun _ _ _ => le_rfl

/-- Native execution supports client results above the operation-answer universe. -/
example : Executes counterExec (.pure (ULift.up 7 : ULift.{1} Nat)) 0
    (ULift.up 7) 0 [] := .pure _ _

example : ∃ c' traces,
    Executes counterExec (.pure (ULift.up 7 : ULift.{1} Nat)) 0 (ULift.up 7) c' traces ∧
    counterRealization.rep 0 c' :=
  counterRealization.exists_executes (.pure (ULift.up 7 : ULift.{1} Nat)) rfl trivial

/-- Nonzero concrete-state credit is retained across future calls. -/
theorem counter_amortized :
    Amortized counterRealization id (fun _ c => c) (fun _ n => 2 * n) :=
  Amortized.ofFn fun _ _ he => by
    obtain ⟨hs, ha, ht⟩ := he
    dsimp only [id, counter, Spec.stepFn]
    omega

/-- The second increment depends on the first answer. -/
def adaptive : counter.Client Nat :=
  ((.liftBind (1 : Nat) fun n => .pure n) : counter.Client Nat).bind fun n =>
    .liftBind n fun a => .pure a

/-- A client contract can be proved compositionally, without exposing any backend. -/
example : counter.Hoare (fun s => s = 0) adaptive (fun a s => a = 2 ∧ s = 2) := by
  apply Spec.Hoare.bind (D := counter) (mid := fun a s => a = 1 ∧ s = 1)
  · apply Spec.Hoare.call_ofFn
    intro s hs
    subst s
    exact ⟨trivial, rfl, rfl⟩
  · intro a
    apply Spec.Hoare.call_ofFn
    rintro s ⟨rfl, rfl⟩
    exact ⟨trivial, rfl, rfl⟩

/-- The endpoint credit theorem has a non-vacuous adaptive instance. -/
example : ∃ c' traces, Executes counterExec adaptive 0 2 c' traces ∧
    c' = 2 ∧ total id traces + c' ≤ 4 := by
  obtain ⟨c', traces, he, hr, ht⟩ := counter_amortized.exists_executes adaptive (s := 0) rfl
    (counter.validHistory_of_forall_valid (fun _ _ => trivial) _ _)
  exact ⟨c', traces, he, hr.symm, ht⟩

/-- Composition hides the intermediate state even for a dependent-answer interface. -/
example : (Module.comp (Module.id counter) (Module.id counter)).rep 7 7 :=
  ⟨7, rfl, rfl⟩

example : eval counter
    (link ((Module.id counter).comp (Module.id counter)).methods adaptive) 0 = (2, 2) := rfl

/-- A low-level copy loop uses genuine Word-RAM steps, with length supplied in registers. -/
example {w : Nat} (x : Cslib.WordRAM.Data 7) (h1 : Cslib.WordRAM.Fits w 1)
    (hs : Cslib.WordRAM.Fits w (x.regs 0 + x.regs 2))
    (hd : Cslib.WordRAM.Fits w (x.regs 1 + x.regs 2))
    (hsep : x.regs 0 + x.regs 2 ≤ x.regs 1) :=
  Cslib.WordRAM.ArrayCopy.exec x h1 hs hd hsep

/--
info: 'Cslib.Stateful.Module.comp' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Module.comp
/--
info: 'Cslib.Stateful.Module.simulates_client' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Module.simulates_client
/--
info: 'Cslib.Stateful.Spec.Hoare.bind' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Spec.Hoare.bind
/--
info: 'Cslib.Stateful.Spec.Hoare.link' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Spec.Hoare.link
/--
info: 'Cslib.Stateful.Amortized.client' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Amortized.client

end ComplexityTests.DataStructure
