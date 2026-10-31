/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Basic

/-!
# Native executions and semantic realizations

A backend chooses concrete states and native execution evidence. Realizations assert existence
of executions and angelic step correctness of every supplied terminating execution, independently of
cost:
* `total`: every represented state and admissible operation admits a native execution;
* `correct`: every native execution from a represented state on an admissible operation realizes
  *some* permitted abstract post-state `s'` with `D.step s o s' a ∧ rep s' c'`.

For deterministic specifications (`[D.HasStepFn f]`), `Realization.ofFn` constructs a `Realization`
from a functional step-correctness proof (`a = (D.stepFn s o).2 ∧ rep (D.stepFn s o).1 c'`), and
`Realization.exists_executes` and `Realization.correct_client` recover the functional `runClient`
characterizations directly.

## Main definitions

* `Execution`: one native operation with typed answer and execution evidence.
* `Executes`: sequential adaptive execution, retaining native evidence in order.
* `Realization`: angelic representation simulation and existence without resource assumptions.
* `Realization.ofFn`: constructor for deterministic specifications (`[D.HasStepFn f]`).

## Main results

* `Realization.correct_demonic`, `Realization.exists_demonic`: soundness and existence of native
  client executions under `D.DemonicValid`.
* `Realization.exists_executes`, `Realization.correct_client`: deterministic specializations for
  `[D.HasStepFn f]`.
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

/-- Angelic semantic realization of a relational specification `D : Spec`:
* `total`: every represented state and admissible operation admits a native execution;
* `correct`: every native execution from a represented state on an admissible operation realizes
  *some* permitted abstract post-state `s'` with `D.step s o s' a ∧ rep s' c'`. -/
structure Realization (D : Spec.{u, v, w}) {C τ : Type x} (exec : Execution D C τ) where
  /-- The relation between mathematical states and concrete backend states. -/
  rep : D.State → C → Prop
  /-- Existence of a native execution for every represented state and admissible operation. -/
  total : ∀ {s c} o, rep s c → D.valid s o → ∃ a c' trace, exec c o a c' trace
  /-- Angelic step correctness: every native execution realizes some permitted abstract step. -/
  correct : ∀ {s c o a c' trace}, rep s c → D.valid s o → exec c o a c' trace →
    ∃ s', D.step s o s' a ∧ rep s' c'

namespace Realization

variable {exec : Execution D C τ} (R : Realization D exec)

/-- Construct a `Realization` for a deterministic specification (`[D.HasStepFn f]`) from a
functional step-correctness proof. -/
abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (rep : D.State → C → Prop)
    (total : ∀ {s c} o, rep s c → D.valid s o → ∃ a c' trace, exec c o a c' trace)
    (correct : ∀ {s c o a c' trace}, rep s c → D.valid s o → exec c o a c' trace →
      a = (D.stepFn s o).2 ∧ rep (D.stepFn s o).1 c') :
    Realization D exec where
  rep := rep
  total := total
  correct {s _ o _ _ _} hr hv he := by
    obtain ⟨ha, hr'⟩ := correct hr hv he
    exact ⟨(D.stepFn s o).1, (D.step_iff_stepFn s o _ _).mpr (Prod.ext rfl ha), hr'⟩

/-- From related states, every native execution of a demonically admissible client realizes a
valid `ClientRun` ending in a related state. -/
theorem correct_demonic {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List τ} (hr : R.rep s c) (hv : D.DemonicValid s p)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ traces.length = tr.length := by
  induction he generalizing s with
  | pure a c =>
    exact ⟨s, [], .pure s a, hr, rfl⟩
  | @call o k c res c₁ trace b c₂ traces ho hes ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep, hr₁⟩ := R.correct hr hv_o ho
    obtain ⟨s₂, tr, hrun, hr₂, hlen⟩ := ih hr₁ (hv_k s₁ res hstep)
    exact ⟨s₂, ⟨o, res, s₁⟩ :: tr, .liftBind o k res hv_o hstep hrun, hr₂,
      congrArg (· + 1) hlen⟩

/-- From related states, every demonically admissible client admits a native execution realizing a
valid `ClientRun` ending in a related state. -/
theorem exists_demonic (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧ traces.length = tr.length := by
  induction p generalizing s c with
  | pure a =>
    exact ⟨a, c, [], s, [], .pure a c, .pure s a, hr, rfl⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨res, c₁, trace, ho⟩ := R.total o hr hv_o
    obtain ⟨s₁, hstep, hr₁⟩ := R.correct hr hv_o ho
    obtain ⟨b, c₂, traces, s₂, tr, hes, hrun, hr₂, hlen⟩ :=
      ih res hr₁ (hv_k s₁ res hstep)
    exact ⟨b, c₂, trace :: traces, s₂, ⟨o, res, s₁⟩ :: tr,
      .call ho hes, .liftBind o k res hv_o hstep hrun, hr₂, congrArg (· + 1) hlen⟩

section HasStepFn

variable {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

/-- On a deterministic specification (`[D.HasStepFn f]`), every native step returns
`(D.stepFn s o).2` and reaches `(D.stepFn s o).1`. -/
theorem correct_ofFn {s : D.State} {c c' : C} {o : D.Op} {a : D.Result o} {trace : τ}
    (hr : R.rep s c) (hv : D.valid s o) (he : exec c o a c' trace) :
    a = (D.stepFn s o).2 ∧ R.rep (D.stepFn s o).1 c' := by
  obtain ⟨s', hstep, hr'⟩ := R.correct hr hv he
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'
  exact ⟨ha, hr'⟩

/-- From related states, a client whose history is admissible has a native execution that returns
the specified result and ends in a state related to the specified final state. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ c' traces, Executes exec p c (D.clientResult s p) c' traces ∧
      R.rep (D.clientState s p) c' := by
  obtain ⟨a, c', traces, s', tr, he, hrun, hr', _⟩ :=
    R.exists_demonic p hr ((D.demonicValid_iff_validHistory_runClient s p).mpr hv)
  obtain ⟨_, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  exact ⟨c', traces, he, hr'⟩

/-- From related states, every native execution of a client whose history is admissible returns
the specified result and ends in a state related to the specified final state. -/
theorem correct_client {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List τ} (hr : R.rep s c) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes exec p c a c' traces) :
    a = D.clientResult s p ∧ R.rep (D.clientState s p) c' := by
  obtain ⟨s', tr, hrun, hr', _⟩ :=
    R.correct_demonic hr ((D.demonicValid_iff_validHistory_runClient s p).mpr hv) he
  obtain ⟨_, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  exact ⟨rfl, hr'⟩

end HasStepFn

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
