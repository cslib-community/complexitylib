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
    (hh : ∀ x, d (h x) = b (f x) ++ c (g x)) :
    ComputableInDegree h a d (max d₁ d₂) (max e₁ e₂) :=
  hf.append hg hh

example {α : Type*} (a : α ↪ List Bool) {f g : α → List Bool}
    (hf : ComputableInDegree f a (Function.Embedding.refl _) 0 0)
    (hg : ComputableInDegree g a (Function.Embedding.refl _) 0 0) :
    ComputableInDegree (fun x => f x ++ g x) a (Function.Embedding.refl _) 0 0 := by
  exact hf.append hg (fun _ => rfl)

example {α : Type*} (a : α ↪ List Bool) {f _g : α → List Bool}
    (_hf : ComputableInDegree f a (Function.Embedding.refl _) 0 0) : True := by
  fail_if_success
    have : ComputableInDegree (fun x => f x ++ _g x) a
        (Function.Embedding.refl _) 0 0 := by
      exact _hf.append (by assumption) (fun _ => rfl)
  trivial

universe u
example {α β γ : Type u} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {p : β × γ ↪ List Bool} [PairEncoding b c p]
    {f : α → β} {g : α → γ} {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f a b d₁ e₁) (hg : ComputableInDegree g a c d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) a p (max d₁ d₂) (max d₁ d₂) :=
  hf.pair hg

example {α β γ : Type u} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {f : α → β} {g : α → γ}
    (hf : ComputableInDegree f a b 0 0) (hg : ComputableInDegree g a c 0 0) :
    ComputableInDegree (fun x => (f x, g x)) a (encPair b c) 0 0 :=
  hf.prod hg

example {α β γ : Type u} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {c : γ ↪ List Bool} {f : α → β} {g : α → γ}
    (hf : ComputableInDegree f a b 2 0) (hg : ComputableInDegree g a c 0 3) :
    ComputableInDegree (fun x => (f x, g x)) a (encPair b c) 2 3 :=
  hf.prod hg

example {α β : Type*} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {test : Bool ↪ List Bool} {c : α → Bool} {f g : α → β} {dc ec d₁ e₁ d₂ e₂ : ℕ}
    (hc : ComputableInDegree c a test dc ec)
    (hf : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans a) b d₁ e₁)
    (hg : ComputableInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans a) b d₂ e₂) :
    ComputableInDegree (fun x => if c x then f x else g x) a b
      (max dc (max d₁ d₂)) (max e₁ e₂) :=
  hc.ite hf hg

example {α β : Type*} {a : α ↪ List Bool} {b : β ↪ List Bool}
    {test : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInDegree c a test 0 0)
    (hf : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans a) b 0 0)
    (hg : ComputableInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans a) b 0 0) :
    ComputableInDegree (fun x => if c x then f x else g x) a b 0 0 :=
  hc.ite hf hg

-- The linear encoding fields remain a temporary construction capability, not a higher calculus.
open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInBigO,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

example {α β : Type*} {_a : α ↪ List Bool} {_b : β ↪ List Bool}
    {_test : Bool ↪ List Bool} {_c : α → Bool} {_f _g : α → β}
    (_hc : ComputableInDegree _c _a _test 0 0) : True := by
  fail_if_success
    have : ComputableInDegree (fun x => if _c x then _f x else _g x) _a _b 0 0 := by
      apply _hc.ite (d₁ := 0) (d₂ := 0) (e₁ := 0) (e₂ := 0) <;> assumption
  trivial
