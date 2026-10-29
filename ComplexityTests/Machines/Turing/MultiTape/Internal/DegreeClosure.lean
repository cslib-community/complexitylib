/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
import Lean.Elab.Command

/-! Independent-degree append controls, including degree zero on runtime-varying inputs. -/
open Turing.MultiTapeTM

example {α β γ δ : Type*} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {d : δ ↪ List Bool} {f : α → β} {g : α → γ} {h : α → δ}
    {d₁ e₁ d₂ e₂ : ℕ} (hf : ComputableInDegree f a b d₁ e₁)
    (hg : ComputableInDegree g a c d₂ e₂)
    (hh : ∀ x, d (h x) = b (f x) ++ c (g x))
    {f₀ g₀ _gBad : α → List Bool}
    (hf₀ : ComputableInDegree f₀ a (Function.Embedding.refl _) 0 0)
    (hg₀ : ComputableInDegree g₀ a (Function.Embedding.refl _) 0 0) :
    ComputableInDegree h a d (max d₁ d₂) (max e₁ e₂) ∧
    ComputableInDegree (fun x => f₀ x ++ g₀ x) a (Function.Embedding.refl _) 0 0 := by
  fail_if_success
    have : ComputableInDegree (fun x => f₀ x ++ _gBad x) a
        (Function.Embedding.refl _) 0 0 := by
      exact hf₀.append (by assumption) (fun _ => rfl)
  exact ⟨hf.append hg hh, hf₀.append hg₀ (fun _ => rfl)⟩

universe u
example {α β γ : Type u} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {p : β × γ ↪ List Bool} [PairEncoding b c p]
    {f : α → β} {g : α → γ} {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f a b d₁ e₁) (hg : ComputableInDegree g a c d₂ e₂)
    (hf₀ : ComputableInDegree f a b 0 0) (hg₀ : ComputableInDegree g a c 0 0)
    (hf₂ : ComputableInDegree f a b 2 0) (hg₃ : ComputableInDegree g a c 0 3) :
    ComputableInDegree (fun x => (f x, g x)) a p (max d₁ d₂) (max d₁ d₂) ∧
    ComputableInDegree (fun x => (f x, g x)) a (encPair b c) 0 0 ∧
    ComputableInDegree (fun x => (f x, g x)) a (encPair b c) 2 3 :=
  ⟨hf.pair hg, hf₀.prod hg₀, hf₂.prod hg₃⟩

example {α β : Type*} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {test : Bool ↪ List Bool} {c : α → Bool} {f g _fBad _gBad : α → β} {dc ec d₁ e₁ d₂ e₂ : ℕ}
    (hc : ComputableInDegree c a test dc ec)
    (hf : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans a) b d₁ e₁)
    (hg : ComputableInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans a) b d₂ e₂)
    (hc₀ : ComputableInDegree c a test 0 0)
    (hf₀ : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans a) b 0 0)
    (hg₀ : ComputableInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans a) b 0 0) :
    ComputableInDegree (fun x => if c x then f x else g x) a b
      (max dc (max d₁ d₂)) (max e₁ e₂) ∧
    ComputableInDegree (fun x => if c x then f x else g x) a b 0 0 := by
  fail_if_success
    have : ComputableInDegree (fun x => if c x then _fBad x else _gBad x) a b 0 0 := by
      apply hc₀.ite (d₁ := 0) (d₂ := 0) (e₁ := 0) (e₂ := 0) <;> assumption
  exact ⟨hc.ite hf hg, hc₀.ite hf₀ hg₀⟩

-- The linear encoding fields remain a temporary construction capability, not a higher calculus.
open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
