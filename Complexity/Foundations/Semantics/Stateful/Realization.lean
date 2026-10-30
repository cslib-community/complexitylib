/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Basic

/-!
# Native executions and semantic realizations

A backend chooses concrete states and native execution evidence. Realizations assert existence
of executions and correctness of every supplied terminating execution, independently of cost.
For nondeterministic backends existence is not demonic termination.

## Main definitions

* `Execution`: one native operation with typed answer and execution evidence.
* `Executes`: sequential adaptive execution, retaining native evidence in order.
* `Realization`: representation simulation and existence without resource assumptions.

## Main results

* `Realization.exists_executes`: admissible clients have correct executions.
* `Realization.correct_client`: every supplied client execution has the specified result.
* `executes_bind_iff`: sequential execution splits exactly at the intermediate state.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x y

variable {S : PFunctor.{v, w}} {D E : Spec.{u, v, w}} {C τ : Type x} {α β : Type y}

instance : Coe Spec.{u, v, w} PFunctor.{v, w} := ⟨Spec.signature⟩

/-- A backend chooses its own execution evidence, independently of a resource measure. -/
abbrev Execution (S : PFunctor.{v, w}) (C Trace : Type x) :=
  C → (o : S.A) → S.B o → C → Trace → Prop

/-- Clients collect native execution evidence in call order; no costs occur in this semantics. -/
inductive Executes (exec : Execution S C τ) : S.FreeM α → C → α → C → List τ → Prop
  | pure (a c) : Executes exec (.pure a) c a c []
  | call {o k c a c' trace b c'' traces} :
      exec c o a c' trace → Executes exec (k a) c' b c'' traces →
      Executes exec (.liftBind o k) c b c'' (trace :: traces)

/-- Functional correctness and existence of executions, without a resource claim.
For nondeterministic backends this is not a demonic termination assertion. -/
structure Realization (D : Spec.{u, v, w}) {C τ : Type x} (exec : Execution D C τ) where
  /-- The relation between mathematical states and concrete backend states. -/
  rep : D.State → C → Prop
  total : ∀ {s c} o, rep s c → D.valid s o → ∃ a c' trace, exec c o a c' trace
  correct : ∀ {s c o a c' trace}, rep s c → D.valid s o → exec c o a c' trace →
    a = (D.step s o).2 ∧ rep (D.step s o).1 c'

namespace Realization

variable {exec : Execution D C τ} (R : Realization D exec)

/-- From related states, a client whose history is admissible has a native execution that returns
the specified result and ends in a state related to the specified final state. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.runClient s p).2.2) :
    ∃ c' traces, Executes exec p c (D.runClient s p).1 c' traces ∧
      R.rep (D.runClient s p).2.1 c' := by
  induction p generalizing s c with
  | pure a => exact ⟨c, [], .pure a c, hr⟩
  | liftBind o k ih =>
    obtain ⟨a, c', trace, he⟩ := R.total o hr hv.1
    obtain ⟨ha, hr'⟩ := R.correct hr hv.1 he
    subst a
    obtain ⟨c'', traces, hes, hrs⟩ := ih (D.step s o).2 hr' hv.2
    exact ⟨c'', trace :: traces, .call he hes, hrs⟩

/-- From related states, every native execution of a client whose history is admissible returns
the specified result and ends in a state related to the specified final state. -/
theorem correct_client {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List τ} (hr : R.rep s c) (hv : D.ValidHistory s (D.runClient s p).2.2)
    (he : Executes exec p c a c' traces) :
    a = (D.runClient s p).1 ∧ R.rep (D.runClient s p).2.1 c' := by
  induction he generalizing s with
  | pure a c => exact ⟨rfl, hr⟩
  | call he hes ih =>
    obtain ⟨ha, hr'⟩ := R.correct hr hv.1 he
    subst ha
    exact ih hr' hv.2

end Realization


/-- Execution of a sequential composition splits its native trace at the call boundary. -/
theorem executes_bind_iff (exec : Execution S C τ) (p : S.FreeM α)
    (k : α → S.FreeM β) {c c' : C} {b : β} {ts : List τ} :
    Executes exec (p.bind k) c b c' ts ↔
      ∃ a mid front back, Executes exec p c a mid front ∧
        Executes exec (k a) mid b c' back ∧ ts = front ++ back := by
  induction p using PFunctor.FreeM.recOn generalizing c ts with
  | pure a =>
    constructor
    · intro h; exact ⟨a, c, [], ts, .pure a c, h, rfl⟩
    · rintro ⟨a', mid, front, back, hp, hk, ht⟩
      cases hp
      simpa only [ht, List.nil_append, PFunctor.FreeM.bind] using hk
  | liftBind o cont ih =>
    change Executes exec (.liftBind o (fun a => (cont a).bind k)) c b c' ts ↔ _
    constructor
    · intro h
      cases h with
      | call ho rest =>
        obtain ⟨a, mid, front, back, hp, hk, ht⟩ := (ih _).mp rest
        exact ⟨a, mid, _, back, .call ho hp, hk, by simp [ht]⟩
    · rintro ⟨a, mid, front, back, hp, hk, ht⟩
      cases hp with
      | call ho rest =>
        have hrest := (ih _).mpr ⟨a, mid, _, back, rest, hk, rfl⟩
        have h := Executes.call (k := fun a => (cont a).bind k) ho hrest
        simpa only [ht, List.cons_append] using h


end Cslib.Stateful
