/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Module

/-!
# Independent additive resource certificates

The same semantic implementation admits multiple resource interpretations. Additive measures of
native evidence compose exactly; this does not model peak live space or cache replacement.
Module potentials may depend on hidden intermediate representations, which are retained as
existential witnesses rather than silently exposed to the client.

## Main definitions

* `total`: additive interpretation of a native trace.
* `Bound`: a per-operation resource certificate, separate from semantic implementation.

## Main results

* `total_eq_sum_map`, `total_flatten`: `total` agrees with `(ts.map weight).sum` and distributes
  over flattened trace chunks.
* `Bound.demonic`, `Bound.exists_demonic`: relational resource bounds and existence along a
  demonically admissible adaptive client.
* `Bound.client`, `Bound.exists_executes`, `Bound.client_const`, `Bound.exists_executes_const`:
  deterministic specializations for `[D.HasStepFn f]`.
* `Module.bound_demonic`, `Module.bound`: transport worst-case bounds through a semantic module.
* `Module.amortized_demonic`, `Module.amortized_client`: telescope hidden-state potential through
  adaptive client executions.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w x y

variable {D E : StateTransitionSpec.{u, v, w}} {C τ : Type x} {α β : Type y}

/-- An additive interpretation of recorded native executions. Only additive resources use this. -/
def total (weight : τ → Nat) : List τ → Nat
  | [] => 0
  | t :: ts => weight t + total weight ts

/-- The empty native trace has zero total weight. -/
@[simp] theorem total_nil (weight : τ → Nat) : total weight [] = 0 := rfl

/-- Prepending a trace element adds its weight to the tail total. -/
@[simp] theorem total_cons (weight : τ → Nat) (t : τ) (ts : List τ) :
    total weight (t :: ts) = weight t + total weight ts := rfl

/-- `total` is the sum of the mapped weights. -/
theorem total_eq_sum_map (weight : τ → Nat) (ts : List τ) :
    total weight ts = (ts.map weight).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

/-- A resource certificate is separate from the implementation and can be supplied more than
once. -/
def Bound {exec : Execution D C τ} (R : StateTransitionImpl D exec)
    (weight : τ → Nat) (charge : D.State → D.Op → Nat) : Prop :=
  ∀ {s c o a c' trace}, R.rep s c → D.valid s o → exec c o a c' trace →
    weight trace ≤ charge s o

/-- Under a resource certificate, every native execution of a demonically admissible client
realizes a valid `ClientRun` transcript whose total charge bounds `total weight traces`. -/
theorem Bound.demonic {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.DemonicValid s p)
    (he : Executes exec p c a c' traces) :
    ∃ s' tr, D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces ≤ D.totalCostTranscript charge s tr := by
  induction he generalizing s with
  | pure a c =>
    exact ⟨s, [], .pure s a, hr, rfl, Nat.le_refl 0⟩
  | @call o k c res c₁ trace b c₂ traces ho hes ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨s₁, hstep, hr₁⟩ := R.correct hr hv_o ho
    have ht := B hr hv_o ho
    obtain ⟨s₂, tr, hrun, hr₂, hlen, hrest⟩ := ih hr₁ (hv_k s₁ res hstep)
    exact ⟨s₂, ⟨o, res, s₁⟩ :: tr, .liftBind o k res hv_o hstep hrun, hr₂,
      congrArg (· + 1) hlen, Nat.add_le_add ht hrest⟩

/-- Under a resource certificate, every demonically admissible client admits a native execution
meeting the total charge bound along its `ClientRun` transcript. -/
theorem Bound.exists_demonic {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.DemonicValid s p) :
    ∃ a c' traces s' tr, Executes exec p c a c' traces ∧
      D.ClientRun s p a s' tr ∧ R.rep s' c' ∧
      traces.length = tr.length ∧
      total weight traces ≤ D.totalCostTranscript charge s tr := by
  obtain ⟨a, c', traces, _, _, he, _, _, _⟩ := R.exists_demonic p hr hv
  obtain ⟨s', tr, hrun, hr', hlen, hb⟩ := B.demonic hr hv he
  exact ⟨a, c', traces, s', tr, he, hrun, hr', hlen, hb⟩

section HasStepFn

variable {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

/-- Under a resource certificate on a deterministic specification (`[D.HasStepFn f]`), every native
execution of a client whose history is admissible has total weight at most the total charge of the
specified history. -/
theorem Bound.client {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes exec p c a c' traces) :
    total weight traces ≤ D.totalCost charge s (D.clientHistory s p) := by
  obtain ⟨s', tr, hrun, _, _, hb⟩ :=
    B.demonic hr ((D.demonicValid_iff_validHistory_runClient s p).mpr hv) he
  obtain ⟨_, _, _, rfl⟩ := (D.clientRun_iff_runClient s p a s' tr).mp hrun
  rwa [D.totalCostTranscript_canonicalTranscript] at hb

/-- Existence and semantic correctness are inherited independently from the implementation. -/
theorem Bound.exists_executes {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {charge : D.State → D.Op → Nat} (B : Bound R weight charge)
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ c' traces, Executes exec p c (D.clientResult s p) c' traces ∧
      R.rep (D.clientState s p) c' ∧
      total weight traces ≤ D.totalCost charge s (D.clientHistory s p) := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', B.client hr hv he⟩

/-- Uniform constant per-operation bounds scale by the history length. -/
theorem Bound.client_const {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {K : Nat} (B : Bound R weight (fun _ _ => K))
    {p : D.Client α} {s : D.State} {c c' : C} {a : α} {traces : List τ}
    (hr : R.rep s c) (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes exec p c a c' traces) :
    total weight traces ≤ (D.clientHistory s p).length * K := by
  simpa only [StateTransitionSpec.totalCost_const] using B.client hr hv he

/-- Existence, correctness, and total cost for a uniform constant per-operation bound. -/
theorem Bound.exists_executes_const {exec : Execution D C τ} {R : StateTransitionImpl D exec}
    {weight : τ → Nat} {K : Nat} (B : Bound R weight (fun _ _ => K))
    (p : D.Client α) {s : D.State} {c : C} (hr : R.rep s c)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ c' traces, Executes exec p c (D.clientResult s p) c' traces ∧
      R.rep (D.clientState s p) c' ∧
      total weight traces ≤ (D.clientHistory s p).length * K := by
  obtain ⟨c', traces, he, hr'⟩ := R.exists_executes p hr hv
  exact ⟨c', traces, he, hr', B.client_const hr hv he⟩

end HasStepFn

namespace Module

variable (M : Module D E) {exec : Execution E C τ}

/-- Transport a worst-case resource bound through a relational semantic module. -/
theorem bound_demonic (R : StateTransitionImpl E exec) {weight : τ → Nat}
    {charge : E.State → E.Op → Nat} (B : Bound R weight charge)
    (budget : D.State → D.Op → Nat)
    (hbudget : ∀ {s e} o {a e' tr}, M.rep s e → D.valid s o →
      E.ClientRun e (M.methods o) a e' tr →
        E.totalCostTranscript charge e tr ≤ budget s o) :
    Bound (M.realize R) (total weight) budget := by
  intro s c o a c' ts hr hv he
  obtain ⟨e, hM, hR⟩ := hr
  obtain ⟨e', tr, hrun, _, _, hb⟩ := B.demonic hR (M.valid o hM hv) he
  exact hb.trans (hbudget o hM hv hrun)

/-- A resource interpretation is transported afterwards on deterministic lower specifications. -/
theorem bound
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o} [E.HasStepFn fE]
    (R : StateTransitionImpl E exec) {weight : τ → Nat}
    {charge : E.State → E.Op → Nat} (B : Bound R weight charge)
    (budget : D.State → D.Op → Nat)
    (hbudget : ∀ {s e} o, M.rep s e → D.valid s o →
      E.totalCost charge e (E.clientHistory e (M.methods o)) ≤ budget s o) :
    Bound (M.realize R) (total weight) budget := by
  intro s c o a c' ts hr hv he
  obtain ⟨e, hM, hR⟩ := hr
  have hv_hist : E.ValidHistory e (E.clientHistory e (M.methods o)) :=
    (E.demonicValid_iff_validHistory_runClient e (M.methods o)).mp (M.valid o hM hv)
  exact (B.client hR hv_hist he).trans (hbudget o hM hv)

/-- Hidden representation credit telescopes along an arbitrary demonically admissible upper client.
The intermediate abstract state remains existentially hidden in the conclusion. -/
theorem amortized_demonic (R : StateTransitionImpl E exec) {weight : τ → Nat}
    {lowerCharge : E.State → E.Op → Nat} (B : Bound R weight lowerCharge)
    (potential : D.State → E.State → Nat) (charge : D.State → D.Op → Nat)
    (hstep : ∀ {s e} o {a e' tr}, M.rep s e → D.valid s o →
      E.ClientRun e (M.methods o) a e' tr →
      ∃ s', D.step s o s' a ∧ M.rep s' e' ∧
        E.totalCostTranscript lowerCharge e tr + potential s' e' ≤
          charge s o + potential s e)
    {p : D.Client α} {s : D.State} {e : E.State} {c c' : C} {a : α}
    {chunks : List (List τ)} (hM : M.rep s e) (hR : R.rep e c)
    (hv : D.DemonicValid s p)
    (he : Executes (fun x o a y ts => Executes exec (M.methods o) x a y ts)
      p c a c' chunks) :
    ∃ s' tr_D e', D.ClientRun s p a s' tr_D ∧ M.rep s' e' ∧ R.rep e' c' ∧
      total (total weight) chunks + potential s' e' ≤
        D.totalCostTranscript charge s tr_D + potential s e := by
  induction he generalizing s e with
  | pure a c =>
    exact ⟨s, [], e, .pure s a, hM, hR, Nat.le_refl _⟩
  | @call o k c res c₁ ts b c₂ chunks hm hk ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    obtain ⟨e₁, tr₁, hrun₁, hR₁, _, hb₁⟩ := B.demonic hR (M.valid o hM hv_o) hm
    obtain ⟨s₁, hstep₁, hM₁, hpot₁⟩ := hstep o hM hv_o hrun₁
    obtain ⟨s₂, tr_D, e₂, hrun_D, hM₂, hR₂, hpot₂⟩ := ih hM₁ hR₁ (hv_k s₁ res hstep₁)
    refine ⟨s₂, ⟨o, res, s₁⟩ :: tr_D, e₂, .liftBind o k res hv_o hstep₁ hrun_D,
      hM₂, hR₂, ?_⟩
    simp only [total_cons, StateTransitionSpec.totalCostTranscript_cons]
    omega

/-- Hidden representation credit telescopes along an arbitrary adaptive upper client on
deterministic specifications. -/
theorem amortized_client
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (R : StateTransitionImpl E exec) {weight : τ → Nat}
    {lowerCharge : E.State → E.Op → Nat} (B : Bound R weight lowerCharge)
    (potential : D.State → E.State → Nat) (charge : D.State → D.Op → Nat)
    (hstep : ∀ {s e} o, M.rep s e → D.valid s o →
      E.totalCost lowerCharge e (E.clientHistory e (M.methods o)) +
        potential (D.stepFn s o).1 (E.clientState e (M.methods o)) ≤
          charge s o + potential s e)
    {p : D.Client α} {s : D.State} {e : E.State} {c c' : C} {a : α}
    {chunks : List (List τ)} (hM : M.rep s e) (hR : R.rep e c)
    (hv : D.ValidHistory s (D.clientHistory s p))
    (he : Executes (fun x o a y ts => Executes exec (M.methods o) x a y ts)
      p c a c' chunks) :
    ∃ e', M.rep (D.clientState s p) e' ∧ R.rep e' c' ∧
      total (total weight) chunks + potential (D.clientState s p) e' ≤
        D.totalCost charge s (D.clientHistory s p) + potential s e := by
  induction he generalizing s e with
  | pure a c => exact ⟨e, hM, hR, Nat.le_refl _⟩
  | @call o k c res c₁ ts b c₂ chunks hm hk ih =>
    have hv_E : E.ValidHistory e (E.clientHistory e (M.methods o)) :=
      (E.demonicValid_iff_validHistory_runClient e (M.methods o)).mp (M.valid o hM hv.1)
    obtain ⟨ha, hR'⟩ := R.correct_client hR hv_E hm
    have hrun_E := E.clientRun_canonical e (M.methods o) hv_E
    obtain ⟨s₁, hstep₁, hM'⟩ := M.correct o hM hv.1 hrun_E
    have heq₁ := (D.step_iff_stepFn s o s₁ _).mp hstep₁
    have hs₁ : s₁ = (D.stepFn s o).1 := congrArg Prod.fst heq₁
    have ha' : E.clientResult e (M.methods o) = (D.stepFn s o).2 := congrArg Prod.snd heq₁
    subst hs₁
    have ht := B.client hR hv_E hm
    have hp := hstep o hM hv.1
    have heq := ha.trans ha'
    subst heq
    obtain ⟨e', hMf, hRf, hbound⟩ := ih hM' hR' hv.2
    exact ⟨e', hMf, hRf, by
      simp only [total_cons, show D.clientHistory s (.liftBind o k) =
        o :: D.clientHistory (D.stepFn s o).1 (k (D.stepFn s o).2) from rfl,
        show D.clientState s (.liftBind o k) =
          D.clientState (D.stepFn s o).1 (k (D.stepFn s o).2) from rfl,
        StateTransitionSpec.totalCost_cons]
      omega⟩

end Module

/-- The total of a flattened list of chunks is the sum of the totals of the chunks. -/
theorem total_flatten (weight : τ → Nat) (chunks : List (List τ)) :
    total weight chunks.flatten = total (total weight) chunks := by
  induction chunks with
  | nil => rfl
  | cons xs xss ih =>
    rw [List.flatten_cons, total_cons, ← ih, total_eq_sum_map, total_eq_sum_map,
      total_eq_sum_map, List.map_append, List.sum_append]

end Cslib.DataStructure
