/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Resource

/-!
# Amortized resource certificates over native executions

Potential credit can depend on both the mathematical state and the hidden concrete state.
This layer attaches a potential inequality to an existing semantic implementation; it does not
modify execution or assign a machine cost to pure Lean computation. Endpoint credit is retained
on the left of the bound, avoiding truncated subtraction.

## Main definitions

* `Amortized`: an angelic native-resource potential certificate over a `StateTransitionImpl`.
* `Amortized.ofFn`: constructor for deterministic specifications (`[D.HasStepFn f]`).

## Main results

* `Amortized.demonic`, `Amortized.exists_demonic`: every demonically admissible adaptive execution
  satisfies the telescoping potential bound along its `ClientRun` transcript.
* `Amortized.client`, `Amortized.exists_executes`: deterministic specializations for
  `[D.HasStepFn f]`.
* `Amortized.client_const`, `Amortized.exists_executes_const`: specialization to uniform constant
  amortized charges.
* `Amortized.of_bound`, `Amortized.of_worstCase`: derive potential certificates from independent
  worst-case bounds.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w x y

variable {D : StateTransitionSpec.{u, v, w}} {C Trace : Type x} {α : Type y}
  {exec : Execution D C Trace}

/-- Angelic potential certificate over a `StateTransitionImpl`: every native operation execution
from a represented state on an admissible operation realizes some permitted abstract post-state `s'`
with `D.step s o s' a ∧ R.rep s' c'` and
`weight trace + potential s' c' ≤ charge s o + potential s c`. -/
structure Amortized (R : StateTransitionImpl D exec) (weight : Trace → Nat)
    (potential : D.State → C → Nat) (charge : D.State → D.Op → Nat) : Prop where
  /-- Angelic step correctness coupled with the potential inequality. -/
  step : ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    ∃ s', D.step s o s' a ∧ R.rep s' c' ∧
      weight trace + potential s' c' ≤ charge s o + potential s c

namespace Amortized

variable {R : StateTransitionImpl D exec} {weight : Trace → Nat} {potential : D.State → C → Nat}
  {charge : D.State → D.Op → Nat} (A : Amortized R weight potential charge)

/-- Construct an `Amortized` certificate on a deterministic specification (`[D.HasStepFn f]`) from
a single-step potential inequality at `(D.stepFn s o).1`. -/
theorem ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (hstep : ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
      weight trace + potential (D.stepFn s o).1 c' ≤ charge s o + potential s c) :
    Amortized R weight potential charge where
  step {s _ o _ _ _} hr hv he := by
    obtain ⟨ha, hr'⟩ := R.correct_ofFn hr hv he
    exact ⟨(D.stepFn s o).1, (D.step_iff_stepFn s o _ _).mpr (Prod.ext rfl ha), hr',
      hstep hr hv he⟩

include A in
/-- **Amortized telescoping along demonically admissible adaptive clients (`demonic`).**
For any demonically admissible client `p` and native execution `Executes exec p c a c' traces`,
there exist a final abstract state `s'` and transcript `tr` such that `D.ClientRun s p a s' tr`,
`R.rep s' c'`, and
`total weight traces + potential s' c' ≤ D.totalCostTranscript charge s tr + potential s c`. -/
theorem demonic {p : D.Client α} {s : D.State} {c c' : C} {a : α}
    {traces : List Trace} (hr : R.rep s c) (hv : D.DemonicValid s p)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces + potential s' c' ≤
        D.totalCostTranscript charge s tr + potential s c := by
  induction he generalizing s with
  | pure a c =>
    exact ⟨s, [], .pure s a, hr, rfl, Nat.le_refl _⟩
  | @call o k c res c₁ trace b c₂ traces ho hes ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep, hr₁, hpot₁⟩ := A.step hr hv_o ho
    obtain ⟨s₂, tr, hrun, hr₂, hlen, hpot₂⟩ := ih hr₁ (hv_k s₁ res hstep)
    refine ⟨s₂, ⟨o, res, s₁⟩ :: tr, .liftBind o k res hv_o hstep hrun, hr₂,
      congrArg (· + 1) hlen, ?_⟩
    simp only [total_cons, StateTransitionSpec.totalCostTranscript_cons]
    omega

include A in
/-- **Existence, correctness, and amortized bound (`exists_demonic`).**
From related initial states, every demonically admissible client `p` admits a native execution
satisfying `D.ClientRun`, `R.rep`, and the telescoping potential bound. -/
theorem exists_demonic (p : D.Client α) {s : D.State} {c : C}
    (hr : R.rep s c) (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces + potential s' c' ≤
        D.totalCostTranscript charge s tr + potential s c := by
  obtain ⟨a, c', traces, _, _, he, _, _, _⟩ := R.exists_demonic p hr hv
  obtain ⟨s', tr, hrun, hr', hlen, hpot⟩ := A.demonic hr hv he
  exact ⟨a, c', traces, s', tr, he, hrun, hr', hlen, hpot⟩

section HasStepFn

variable {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

include A in
/-- Adaptive clients retain both initial and final representation credit on deterministic
specifications. -/
theorem client {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes exec p c a c' traces) :
    total weight traces + potential (D.clientState s p) c' ≤
      D.totalCost charge s (D.clientHistory s p) + potential s c := by
  obtain ⟨s', tr, hrun, _, _, hpot⟩ :=
    A.demonic hr ((D.demonicValid_iff_validHistory_runClient s p).mpr hv) he
  obtain ⟨_, _, rfl, rfl⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  rwa [D.totalCostTranscript_canonicalTranscript] at hpot

include A in
/-- Existence and semantic correctness are inherited independently from the implementation. -/
theorem exists_executes (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ c' traces, Executes exec p c (D.clientResult s p) c' traces ∧
      R.rep (D.clientState s p) c' ∧
      total weight traces + potential (D.clientState s p) c' ≤
        D.totalCost charge s (D.clientHistory s p) + potential s c := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', A.client hr hv he⟩

/-- Adaptive client potential bound for a uniform constant per-operation amortized charge. -/
theorem client_const {K : Nat} (A : Amortized R weight potential (fun _ _ => K))
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes exec p c a c' traces) :
    total weight traces + potential (D.clientState s p) c' ≤
      (D.clientHistory s p).length * K + potential s c := by
  simpa only [StateTransitionSpec.totalCost_const] using A.client hr hv he

/-- Existence, correctness, and potential bound for a uniform constant amortized charge. -/
theorem exists_executes_const {K : Nat} (A : Amortized R weight potential (fun _ _ => K))
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ c' traces, Executes exec p c (D.clientResult s p) c' traces ∧
      R.rep (D.clientState s p) c' ∧
      total weight traces + potential (D.clientState s p) c' ≤
        (D.clientHistory s p).length * K + potential s c := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', A.client_const hr hv he⟩

/-- Worst-case certificates on deterministic specifications give potential certificates whenever
their charges satisfy the abstract potential inequality. -/
theorem of_bound {cost : D.State → D.Op → Nat} (B : Bound R weight cost)
    (potential : D.State → Nat) (charge : D.State → D.Op → Nat)
    (h : ∀ s o, D.valid s o →
      cost s o + potential (D.stepFn s o).1 ≤ charge s o + potential s) :
    Amortized R weight (fun s _ => potential s) charge :=
  Amortized.ofFn fun hr hv he => (Nat.add_le_add_right (B hr hv he) _).trans (h _ _ hv)

end HasStepFn

/-- Worst-case certificates give potential certificates whenever their charges satisfy the
relational abstract potential inequality across all permitted outcomes. -/
theorem of_bound_demonic {cost : D.State → D.Op → Nat} (B : Bound R weight cost)
    (potential : D.State → Nat) (charge : D.State → D.Op → Nat)
    (h : ∀ s o s' a, D.valid s o → D.step s o s' a →
      cost s o + potential s' ≤ charge s o + potential s) :
    Amortized R weight (fun s _ => potential s) charge where
  step hr hv he := by
    obtain ⟨s', hstep, hr'⟩ := R.correct hr hv he
    exact ⟨s', hstep, hr', (Nat.add_le_add_right (B hr hv he) _).trans (h _ _ s' _ hv hstep)⟩

/-- A worst-case bound is a zero-potential certificate. -/
theorem of_worstCase (B : Bound R weight charge) :
    Amortized R weight (fun _ _ => 0) charge where
  step hr hv he := by
    obtain ⟨s', hstep, hr'⟩ := R.correct hr hv he
    exact ⟨s', hstep, hr', by simpa using B hr hv he⟩

end Amortized
end Cslib.DataStructure
