/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Revealing a hidden sample along an experiment

A real experiment runs on states `a`. An ideal experiment first draws a hidden sample `k` and then
runs on smaller states that depend on it. The two are linked by a law `exp a` of the hidden sample
given the real state and by a representation `rep a`: the real state together with the explained
sample, `(exp a).map (·, rep a)`, has the law of the ideal pair. Lazy and eager sampling of a
random function are an example, where `exp` completes the table that a lazy state has not yet
sampled.

Such a link is preserved by a step that keeps it on reachable real states. The lemmas carry an
invariant of those states, so the local link need only hold where the invariant does. A trivial
hidden sample turns the link into a plain state representation, `(d.map rep)`.

## Main results

* `Cslib.Probability.PMF.bind_bind_comm_of_invariant`: one step preserves the link.
* `Cslib.Probability.PMF.map_bind_of_invariant`: one step preserves a state representation.
* `Cslib.Probability.PMF.iterate_bind_comm_of_invariant`,
  `Cslib.Probability.PMF.map_iterate_bind_of_invariant`: the same for a bounded chain of steps.
* `Cslib.Probability.PMF.iterate_bind_invariant`: reachable states of a chain satisfy a preserved
  invariant.
-/

public section

namespace Cslib.Probability.PMF

universe u v w x y

variable {α₁ : Type u} {β₁ : Type v} {α : Type w} {β : Type x} {γ : Type y}

/-- A step preserves the link `(exp a).map (·, rep a)` between real states and an ideal pair of a
hidden sample and a represented state. The ideal step may depend on the hidden sample. The local
link need only hold on reachable states satisfying `inv₁`, and the step preserves the invariant. -/
theorem bind_bind_comm_of_invariant
    (d₁ : PMF α₁) (exp₁ : α₁ → PMF γ) (rep₁ : α₁ → β₁) (d₂ : γ → PMF β₁) (inv₁ : α₁ → Prop)
    (exp₀ : PMF γ)
    (f₁ : α₁ → PMF α) (exp : α → PMF γ) (rep : α → β) (f₂ : γ → β₁ → PMF β) (inv : α → Prop)
    (hd : (d₁.bind fun a => (exp₁ a).map (·, rep₁ a)) =
        (exp₀.bind fun k => (d₂ k).map (k, ·)) ∧ ∀ a ∈ d₁.support, inv₁ a)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      ((f₁ a).bind fun b => (exp b).map (·, rep b)) =
        ((exp₁ a).bind fun k => (f₂ k (rep₁ a)).map (k, ·)) ∧
      ∀ b ∈ (f₁ a).support, inv b) :
    ((d₁.bind f₁).bind fun b => (exp b).map (·, rep b)) =
      (exp₀.bind fun k => ((d₂ k).bind (f₂ k)).map (k, ·)) ∧
    ∀ b ∈ (d₁.bind f₁).support, inv b := by
  refine ⟨?_, ?_⟩
  · rw [PMF.bind_bind]
    have hcongr : (d₁.bind fun a => (f₁ a).bind fun b => (exp b).map (·, rep b)) =
        (d₁.bind fun a => (exp₁ a).bind fun k => (f₂ k (rep₁ a)).map (k, ·)) :=
      bind_congr_on_support _ _ _ fun a ha => (hf a ha (hd.2 a ha)).1
    rw [hcongr]
    have h2 := congrArg (fun d => d.bind fun (k, b₁) => (f₂ k b₁).map (k, ·)) hd.1
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h2 ⊢
    rw [h2]
    refine bind_congr_on_support _ _ _ fun k _ => ?_
    simp only [PMF.map_bind]
  · intro b hb
    obtain ⟨a, ha, hmem⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    exact (hf a ha (hd.2 a ha)).2 b hmem

/-- A step preserves a state representation `rep₁` when it commutes with the representation on
reachable states satisfying `inv₁`, and it preserves the invariant. -/
theorem map_bind_of_invariant
    (d₁ : PMF α₁) (d₂ : PMF β₁) (rep₁ : α₁ → β₁) (inv₁ : α₁ → Prop)
    (f₁ : α₁ → PMF α) (f₂ : β₁ → PMF β) (rep : α → β) (inv : α → Prop)
    (hd : d₁.map rep₁ = d₂ ∧ ∀ a ∈ d₁.support, inv₁ a)
    (hf : ∀ a ∈ d₁.support, inv₁ a →
      (f₁ a).map rep = f₂ (rep₁ a) ∧ ∀ b ∈ (f₁ a).support, inv b) :
    (d₁.bind f₁).map rep = d₂.bind f₂ ∧ ∀ b ∈ (d₁.bind f₁).support, inv b := by
  have hmain := bind_bind_comm_of_invariant d₁ (fun _ => PMF.pure ()) rep₁ (fun _ => d₂)
    inv₁ (PMF.pure ()) f₁ (fun _ => PMF.pure ()) rep (fun _ => f₂) inv
    ⟨by rw [PMF.pure_bind, ← hd.1]; simp only [PMF.map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def], hd.2⟩
    fun a ha hia => by
      obtain ⟨heq, hinv⟩ := hf a ha hia
      refine ⟨?_, hinv⟩
      rw [PMF.pure_bind, ← heq]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  exact ⟨by simpa only [PMF.map, PMF.pure_bind, PMF.bind_pure, PMF.bind_bind,
    Function.comp_def] using congrArg (PMF.map Prod.snd) hmain.1, hmain.2⟩

/-- A chain of `m` steps preserves the link between real states and an ideal pair of a hidden
sample and a represented state, when each step keeps the link on states satisfying the invariant
`inv i` of its round `i` and preserves the invariant. The ideal chain may depend on the hidden
sample, drawn once from its law at the initial state. -/
theorem iterate_bind_comm_of_invariant
    (step₁ : α → PMF α) (step₂ : γ → β → PMF β)
    (exp : α → PMF γ) (rep : α → β) (inv : ℕ → α → Prop)
    (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a →
      ((step₁ a).bind fun a' => (exp a').map (·, rep a')) =
        ((exp a).bind fun k => (step₂ k (rep a)).map (k, ·)) ∧
      ∀ a' ∈ (step₁ a).support, inv (i + 1) a') :
    ((Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)).bind
        fun a => (exp a).map (·, rep a)) =
      ((exp init).bind fun k =>
        (Nat.iterate (fun d => d.bind (step₂ k)) m (PMF.pure (rep init))).map (k, ·)) ∧
      ∀ a ∈ (Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)).support, inv m a := by
  induction m with
  | zero =>
    refine ⟨?_, fun a ha => ?_⟩
    · simp only [Function.iterate_zero, id_eq, PMF.pure_bind, PMF.map, Function.comp_def]
    · obtain rfl := (PMF.mem_support_pure_iff _ _).mp ha
      exact hinit
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact bind_bind_comm_of_invariant _ exp rep _ (inv m) (exp init) step₁ exp rep step₂
      (inv (m + 1)) (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      fun a _ ha => hstep m (Nat.lt_succ_self m) a ha

/-- A chain of `m` steps preserves a state representation when each step commutes with it on
states satisfying the invariant `inv i` of its round `i` and preserves the invariant. -/
theorem map_iterate_bind_of_invariant
    (step₁ : α → PMF α) (step₂ : β → PMF β) (rep : α → β) (inv : ℕ → α → Prop)
    (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a →
      (step₁ a).map rep = step₂ (rep a) ∧ ∀ a' ∈ (step₁ a).support, inv (i + 1) a') :
    (Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)).map rep =
        Nat.iterate (fun d => d.bind step₂) m (PMF.pure (rep init)) ∧
      ∀ a ∈ (Nat.iterate (fun d => d.bind step₁) m (PMF.pure init)).support, inv m a := by
  induction m with
  | zero =>
    refine ⟨by simp only [Function.iterate_zero, id_eq, PMF.pure_map], fun a ha => ?_⟩
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp ha
    exact hinit
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact map_bind_of_invariant _ _ rep (inv m) step₁ step₂ rep (inv (m + 1))
      (ih fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      fun a _ ha => hstep m (Nat.lt_succ_self m) a ha

/-- Every reachable state of a chain of `m` steps satisfies an invariant indexed by the round,
when every possible step from a state satisfying the invariant of its round preserves it. -/
theorem iterate_bind_invariant
    (step : α → PMF α) (inv : ℕ → α → Prop) (m : ℕ) (init : α) (hinit : inv 0 init)
    (hstep : ∀ i < m, ∀ a, inv i a → ∀ a' ∈ (step a).support, inv (i + 1) a') :
    ∀ a ∈ (Nat.iterate (fun d => d.bind step) m (PMF.pure init)).support, inv m a :=
  (map_iterate_bind_of_invariant step (fun _ => PMF.pure ()) (fun _ => ()) inv m
    init hinit fun i hi a ha => ⟨by rw [PMF.map_const], hstep i hi a ha⟩).2

end Cslib.Probability.PMF
