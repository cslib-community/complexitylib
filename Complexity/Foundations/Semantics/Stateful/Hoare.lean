/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Composition

/-!
# Compositional proof rules for stateful clients

These semantic Hoare rules generate demonic admissibility and postcondition obligations for pure
results, calls, sequential composition and consequence. They apply before choosing a backend;
realization transports their results to native execution. Resource obligations are separate.

## Main definitions

* `Spec.Hoare`: demonic Hoare triple asserting `D.DemonicValid s p` and `post v s'` for every
  valid `D.ClientRun s p v s' tr`.

## Main results

* `Spec.Hoare.pure`, `Spec.Hoare.call`, `Spec.Hoare.call_ofFn`, `Spec.Hoare.bind`,
  `Spec.Hoare.consequence`: compositional verification rules.
* `Spec.hoare_iff_ofFn`: equivalence with the functional `runClient` formulation on deterministic
  specifications (`[D.HasStepFn f]`).
* `Spec.Hoare.realize`: a semantic client proof transports through any realization.
* `Spec.Hoare.link`: transport a semantic client contract across an interface implementation.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful.Spec

universe u v w x y

variable {D : Spec.{u, v, w}} {α β : Type y}

/-- Demonic Hoare triple: from any state satisfying `pre s`, the client `p` is demonically
admissible (`D.DemonicValid s p`) and *every* valid `ClientRun` establishes `post v s'`. -/
def Hoare (pre : D.State → Prop) (p : D.Client α) (post : α → D.State → Prop) : Prop :=
  ∀ s, pre s → D.DemonicValid s p ∧ ∀ v s' tr, D.ClientRun s p v s' tr → post v s'

/-- On a deterministic specification (`[D.HasStepFn f]`), `D.Hoare` is equivalent to
`D.ValidHistory s (D.runClient s p).2.2 ∧ post (D.runClient s p).1 (D.runClient s p).2.1`. -/
theorem hoare_iff_ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (pre : D.State → Prop) (p : D.Client α) (post : α → D.State → Prop) :
    D.Hoare pre p post ↔
      ∀ s, pre s → D.ValidHistory s (D.runClient s p).2.2 ∧
        post (D.runClient s p).1 (D.runClient s p).2.1 := by
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  rw [demonicValid_iff_validHistory_runClient]
  constructor
  · rintro ⟨hv, hpost⟩
    exact ⟨hv, hpost _ _ _ (D.clientRun_canonical s p hv)⟩
  · rintro ⟨hv, hpost⟩
    refine ⟨hv, fun v s' tr hrun => ?_⟩
    obtain ⟨_, rfl, rfl, _⟩ := (D.clientRun_iff_runClient s p v s' tr).mp hrun
    exact hpost

namespace Hoare

/-- Returning a value leaves the represented state unchanged. -/
theorem pure (pre : D.State → Prop) (a : α) (post : α → D.State → Prop)
    (h : ∀ s, pre s → post a s) : Hoare pre (.pure a) post := by
  intro s hs
  refine ⟨.pure s a, fun v s' tr hrun => ?_⟩
  cases hrun
  exact h s hs

/-- Calling an operation requires `D.valid s o` and establishes `post a s'` for every permitted
outcome `D.step s o s' a`. -/
theorem call (pre : D.State → Prop) (o : D.Op) (post : D.Result o → D.State → Prop)
    (h : ∀ s, pre s → D.valid s o ∧ ∀ s' a, D.step s o s' a → post a s') :
    Hoare pre (.liftBind o fun a => .pure a) post := by
  intro s hs
  obtain ⟨hv, hpost⟩ := h s hs
  refine ⟨.liftBind o (fun a => .pure a) hv fun s' a _ => .pure s' a, ?_⟩
  intro v s' tr hrun
  cases hrun with
  | liftBind _ _ a _ hstep hrest =>
    cases hrest
    exact hpost s' v hstep

/-- On a deterministic specification (`[D.HasStepFn f]`), calling an operation requires its
precondition and exposes `(D.stepFn s o)`. -/
theorem call_ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (pre : D.State → Prop) (o : D.Op) (post : D.Result o → D.State → Prop)
    (h : ∀ s, pre s → D.valid s o ∧ post (D.stepFn s o).2 (D.stepFn s o).1) :
    Hoare pre (.liftBind o fun a => .pure a) post := by
  refine call pre o post fun s hs => ⟨(h s hs).1, fun s' a hstep => ?_⟩
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'; subst ha
  exact (h s hs).2

/-- Sequencing exposes only the intermediate abstract postcondition to its continuation. -/
theorem bind {pre : D.State → Prop} {mid : α → D.State → Prop}
    {post : β → D.State → Prop} {p : D.Client α} {k : α → D.Client β}
    (hp : Hoare pre p mid) (hk : ∀ a, Hoare (mid a) (k a) post) :
    Hoare pre (p.bind k) post := by
  intro s hs
  obtain ⟨hvp, hpost_p⟩ := hp s hs
  refine ⟨hvp.bind fun a s₁ tr₁ hrun₁ => (hk a s₁ (hpost_p a s₁ tr₁ hrun₁)).1, ?_⟩
  intro b s₂ tr hrun
  obtain ⟨a, s₁, tr₁, tr₂, hrun₁, hrun₂, _⟩ := clientRun_bind_iff.mp hrun
  exact (hk a s₁ (hpost_p a s₁ tr₁ hrun₁)).2 b s₂ tr₂ hrun₂

/-- Strengthen preconditions and weaken postconditions without reopening a client proof. -/
theorem consequence {pre pre' : D.State → Prop} {post post' : α → D.State → Prop}
    {p : D.Client α} (h : Hoare pre p post) (hp : ∀ s, pre' s → pre s)
    (hq : ∀ a s, post a s → post' a s) : Hoare pre' p post' := by
  intro s hs
  obtain ⟨hv, hpost⟩ := h s (hp s hs)
  exact ⟨hv, fun v s' tr hrun => hq v s' (hpost v s' tr hrun)⟩

/-- Every native execution of a verified client satisfies its abstract postcondition. -/
theorem realize {C Trace : Type x} {exec : Execution D C Trace} (R : Realization D exec)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    (h : Hoare pre p post) {s : D.State} {c c' : C} {a : α} {traces : List Trace}
    (hp : pre s) (hr : R.rep s c) (he : Executes exec p c a c' traces) :
    ∃ s', R.rep s' c' ∧ post a s' := by
  obtain ⟨hv, ht⟩ := h s hp
  obtain ⟨s', tr, hrun, hr', _⟩ := R.correct_demonic hr hv he
  exact ⟨s', hr', ht a s' tr hrun⟩

/-- Linking preserves a client contract while existentially hiding the module representation. -/
theorem link {α : Type w} {E : Spec.{u, v, w}} (M : Module D E)
    {pre : D.State → Prop} {post : α → D.State → Prop} {p : D.Client α}
    (h : Hoare pre p post) :
    Hoare (fun e => ∃ s, pre s ∧ M.rep s e) (Stateful.link M.methods p)
      (fun a e => ∃ s, post a s ∧ M.rep s e) := by
  rintro e ⟨s, hp, hr⟩
  obtain ⟨hv, ht⟩ := h s hp
  obtain ⟨hv_E, hcorr⟩ := M.simulates_demonic p hr hv
  refine ⟨hv_E, fun a e' tr_E hrun_E => ?_⟩
  obtain ⟨s', tr_D, hrun_D, hr'⟩ := hcorr a e' tr_E hrun_E
  exact ⟨s', ht a s' tr_D hrun_D, hr'⟩

end Hoare
end Cslib.Stateful.Spec
