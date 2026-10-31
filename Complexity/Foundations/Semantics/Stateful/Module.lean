/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Realization

/-!
# Compositional semantic implementations

A module implements one interface using operations of another. Linking uses the upstream
free-monad interpreter. Behavior proofs neither choose a computational model nor assign costs.
Realization composes representation relations and hides intermediate states existentially.
Linking uses the upstream interpreter's common universe for operation answers and client
results. Native execution itself permits an independent universe for client results.

## Main definitions

* `Methods`: operation bodies over a lower interface.
* `Module`: demonic lower-call admissibility and angelic representation simulation for those
  bodies.
* `Module.ofFn`: constructor for deterministic upper and lower specifications.
* `link`: substitute lower method bodies into an adaptive client.

## Main results

* `Module.realize`: implement a module with any realization of its lower interface.
* `link_exec`, `link_exec_decompose`: exact correspondence of chunked and flattened executions.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w x

variable {D E : Spec.{u, v, w}} {C τ : Type x} {α β : Type w}

/-- Interface methods are programs over another interface. -/
abbrev Methods (D E : Spec.{u, v, w}) := (o : D.Op) → E.Client (D.Result o)

/-- Substitution reuses upstream free-monad interpretation. -/
def link (methods : Methods D E) (p : D.Client α) : E.Client α := p.liftM methods

/-- Purely semantic module correctness over relational specifications; neither an execution model
nor a cost appears. -/
structure Module (D E : Spec.{u, v, w}) where
  /-- Bodies implementing the upper interface using lower-interface calls. -/
  methods : Methods D E
  /-- The relation between upper and lower mathematical states. -/
  rep : D.State → E.State → Prop
  /-- Demonic admissibility of each method body from related states. -/
  valid : ∀ {s e} o, rep s e → D.valid s o → E.DemonicValid e (methods o)
  /-- Angelic correctness of each method body: every lower `ClientRun` realizes some permitted
  upper step `D.step s o s' a` maintaining `rep s' e'`. -/
  correct : ∀ {s e} o {a e' tr}, rep s e → D.valid s o →
    E.ClientRun e (methods o) a e' tr → ∃ s', D.step s o s' a ∧ rep s' e'

namespace Module

variable (M : Module D E) {exec : Execution E C τ}

/-- Construct a `Module D E` for deterministic specifications (`[D.HasStepFn fD]`,
`[E.HasStepFn fE]`) from functional `ValidHistory` and `runClient` obligations. -/
abbrev ofFn {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (methods : Methods D E)
    (rep : D.State → E.State → Prop)
    (valid : ∀ {s e} o, rep s e → D.valid s o →
      E.ValidHistory e (E.clientHistory e (methods o)))
    (correct : ∀ {s e} o, rep s e → D.valid s o →
      E.clientResult e (methods o) = (D.stepFn s o).2 ∧
        rep (D.stepFn s o).1 (E.clientState e (methods o))) :
    Module D E where
  methods := methods
  rep := rep
  valid {s e} o hr hv :=
    (E.demonicValid_iff_validHistory_runClient e (methods o)).mpr (valid o hr hv)
  correct {s e} o {a e' tr} hr hv hrun := by
    obtain ⟨_, rfl, rfl, _⟩ := (E.clientRun_iff_runClient e (methods o) a e' tr).mp hrun
    obtain ⟨ha, hr'⟩ := correct o hr hv
    exact ⟨(D.stepFn s o).1, (D.step_iff_stepFn s o _ _).mpr (Prod.ext rfl ha), hr'⟩

/-- Module realization hides the intermediate representation and composes at any backend. -/
def realize (R : Realization E exec) :
    Realization D (fun c o a c' ts => Executes exec (M.methods o) c a c' ts) where
  rep s c := ∃ e, M.rep s e ∧ R.rep e c
  total o hr hv := by
    obtain ⟨e, hM, hR⟩ := hr
    obtain ⟨a, c', traces, _, _, he, _, _, _⟩ :=
      R.exists_demonic (M.methods o) hR (M.valid o hM hv)
    exact ⟨a, c', traces, he⟩
  correct {s c o a c' ts} hr hv he := by
    obtain ⟨e, hM, hR⟩ := hr
    obtain ⟨e', tr, hrun, hR', _⟩ := R.correct_demonic hR (M.valid o hM hv) he
    obtain ⟨s', hstep, hM'⟩ := M.correct o hM hv hrun
    exact ⟨s', hstep, e', hM', hR'⟩

end Module

/-- Linking expands every module call and preserves the complete flattened backend trace. -/
theorem link_exec (methods : Methods D E) (exec : Execution E C τ)
    {p : D.Client α} {c c' : C} {a : α} {chunks : List (List τ)}
    (he : Executes (fun x o a y ts => Executes exec (methods o) x a y ts) p c a c' chunks) :
    Executes exec (link methods p) c a c' chunks.flatten := by
  induction he with
  | pure a c => exact .pure a c
  | call hm hk ih =>
    apply (executes_bind_iff exec _ _).mpr
    exact ⟨_, _, _, _, hm, ih, rfl⟩

/-- Every flattened execution also decomposes into executions of its individual method calls. -/
theorem link_exec_decompose (methods : Methods D E) (exec : Execution E C τ)
    {p : D.Client α} {c c' : C} {a : α} {ts : List τ}
    (he : Executes exec (link methods p) c a c' ts) :
    ∃ chunks,
      Executes (fun x o a y trace => Executes exec (methods o) x a y trace)
        p c a c' chunks ∧ ts = chunks.flatten := by
  induction p generalizing c ts with
  | pure b =>
    cases he
    exact ⟨[], .pure _ _, rfl⟩
  | liftBind o k ih =>
    obtain ⟨b, mid, front, back, hm, hk, ht⟩ := (executes_bind_iff exec _ _).mp he
    obtain ⟨chunks, hc, hts⟩ := ih b hk
    exact ⟨front :: chunks, .call hm hc, by simp [ht, hts]⟩

end Cslib.Stateful
