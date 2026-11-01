/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Semantics.Stateful.Module

/-!
# Composing verified interface implementations

Modules compose by substituting method bodies and composing representation relations. The
intermediate state remains hidden, so callers need not depend on either representation.
This construction shares the same semantics across all backend and resource interpretations.

## Main definitions

* `Module.id`: the identity implementation of an interface.
* `Module.comp`: composition of two verified interface implementations.

## Main results

* `Module.simulates_demonic`: relational semantic refinement lifts through a demonically admissible
  adaptive client.
* `Module.simulates_client`: deterministic specialization of `simulates_demonic` for
  `[D.HasStepFn fD]` and `[E.HasStepFn fE]`.
* `link_comp`: composing methods agrees with consecutive linking.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.Stateful

universe u v w

variable {D E F : Spec.{u, v, w}} {α : Type w}

namespace Module

/-- Per-operation relational simulations lift to any demonically admissible adaptive client. -/
theorem simulates_demonic (M : Module D E) (p : D.Client α) {s : D.State} {e : E.State}
    (hr : M.rep s e) (hv : D.DemonicValid s p) :
    E.DemonicValid e (link M.methods p) ∧
      ∀ a e' tr_E, E.ClientRun e (link M.methods p) a e' tr_E →
        ∃ s' tr_D, D.ClientRun s p a s' tr_D ∧ M.rep s' e' := by
  induction p generalizing s e with
  | pure a =>
    refine ⟨.pure e a, fun v e' tr_E hrun => ?_⟩
    cases hrun
    exact ⟨s, [], .pure s a, hr⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff s o k).mp hv
    have hm := M.valid o hr hv_o
    have heq : link M.methods (.liftBind o k) =
        (M.methods o).bind (fun a => link M.methods (k a)) := rfl
    rw [heq]
    refine ⟨hm.bind fun a e₁ tr₁ hrun₁ => ?_, fun b e₂ tr_E hrun => ?_⟩
    · obtain ⟨s₁, hstep, hr₁⟩ := M.correct o hr hv_o hrun₁
      exact (ih a hr₁ (hv_k s₁ a hstep)).1
    · obtain ⟨a, e₁, tr₁, tr₂, hrun₁, hrun₂, _⟩ := E.clientRun_bind_iff.mp hrun
      obtain ⟨s₁, hstep, hr₁⟩ := M.correct o hr hv_o hrun₁
      obtain ⟨s₂, tr_D, hrun_D, hr₂⟩ :=
        (ih a hr₁ (hv_k s₁ a hstep)).2 b e₂ tr₂ hrun₂
      exact ⟨s₂, ⟨o, a, s₁⟩ :: tr_D, .liftBind o k a hv_o hstep hrun_D, hr₂⟩

/-- Per-operation semantic simulations lift to the whole answer-dependent client on deterministic
specifications. -/
theorem simulates_client
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (e : E.State) → (o : E.Op) → E.State × E.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE]
    (M : Module D E) (p : D.Client α) {s : D.State} {e : E.State}
    (hr : M.rep s e) (hv : D.ValidHistory s (D.clientHistory s p)) :
    E.ValidHistory e (E.clientHistory e (link M.methods p)) ∧
      E.clientResult e (link M.methods p) = D.clientResult s p ∧
      M.rep (D.clientState s p) (E.clientState e (link M.methods p)) := by
  have hv_dem : D.DemonicValid s p :=
    (D.demonicValid_iff_validHistory_runClient s p).mpr hv
  obtain ⟨hv_E, hcorr⟩ := M.simulates_demonic p hr hv_dem
  have hv_hist_E : E.ValidHistory e (E.clientHistory e (link M.methods p)) :=
    (E.demonicValid_iff_validHistory_runClient e (link M.methods p)).mp hv_E
  have hrun_E := E.clientRun_canonical e (link M.methods p) hv_hist_E
  obtain ⟨s', tr_D, hrun_D, hr'⟩ := hcorr _ _ _ hrun_E
  obtain ⟨_, ha, hs', _⟩ := (D.clientRun_iff_runClient s p _ s' tr_D).mp hrun_D
  subst hs'
  exact ⟨hv_hist_E, ha, hr'⟩

/-- Identity methods expose precisely one call and preserve the state representation. -/
def id (D : Spec.{u, v, w}) : Module D D where
  methods o := .liftBind o fun a => .pure a
  rep := Eq
  valid o hr hv := by
    subst hr
    exact .liftBind o (fun a => .pure a) hv fun s' a _ => .pure s' a
  correct {_ _} o {_ _ _} hr _ hrun := by
    subst hr
    cases hrun with
    | liftBind _ _ a _ hstep hrest =>
      cases hrest
      exact ⟨_, hstep, rfl⟩

/-- Compose implementation proofs while hiding the intermediate representation. -/
def comp (M : Module D E) (N : Module E F) : Module D F where
  methods o := link N.methods (M.methods o)
  rep s f := ∃ e, M.rep s e ∧ N.rep e f
  valid o hr hv := by
    obtain ⟨e, hm, hn⟩ := hr
    exact (N.simulates_demonic (M.methods o) hn (M.valid o hm hv)).1
  correct {_ _} o {_ _ _} hr hv hrun := by
    obtain ⟨e, hm, hn⟩ := hr
    obtain ⟨e', tr_E, hrun_E, hn'⟩ :=
      (N.simulates_demonic (M.methods o) hn (M.valid o hm hv)).2 _ _ _ hrun
    obtain ⟨s', hstep, hm'⟩ := M.correct o hm hv hrun_E
    exact ⟨s', hstep, e', hm', hn'⟩

end Module

/-- Consecutive linking is the same program as linking the composed method table. -/
theorem link_comp (f : Methods D E) (g : Methods E F) (p : D.Client α) :
    link g (link f p) = link (fun o => link g (f o)) p :=
  PFunctor.FreeM.liftM_comp p f g

end Cslib.Stateful
