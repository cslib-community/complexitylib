/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Monad morphisms under private state

A monad morphism transforms a stateful computation by transforming its complete result/state
pair. It preserves sequencing without dropping or reinitializing the private state.

## Main results

* `Cslib.IsMonadHom.stateT`: lift a monad morphism pointwise under `StateT`.
* `StateT.foldlM_run`: running a list `foldlM` in `StateT σ m` folds the stateful step over pairs.
* `StateT.foldlM_run_except`: running a list `foldlM` in `StateT σ (Except ε)` is a pure
  `List.foldl` with `Except.bind`.

## References

Uses the upstream `Cslib.IsMonadHom` interface and Lean's `StateT`.
-/

@[expose] public section

namespace Cslib

universe u v w

/-- Transforming the underlying effect while retaining state is a monad morphism. -/
theorem IsMonadHom.stateT {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    {f : ∀ {α}, m α → n α} (hf : IsMonadHom m n f) (State : Type u) :
    IsMonadHom (StateT State m) (StateT State n)
      (fun program state => f (program state)) :=
  .mk' (fun _ => funext fun _ => hf.map_pure _)
    (fun program next => funext fun state => hf.map_bind (program state)
      (fun (a, state') => next a state'))

end Cslib

namespace StateT

universe u v

/-- Running a monadic left fold in `StateT σ m` folds the stateful step over value-state pairs. -/
theorem foldlM_run {m : Type u → Type v} [Monad m] {σ β γ : Type u}
    (g : β → γ → StateT σ m β) (l : List γ) (b : β) (s : σ) :
    (l.foldlM g b).run s = l.foldlM (fun p c => (g p.1 c).run p.2) (b, s) := by
  induction l generalizing b s with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldlM_cons, StateT.run_bind, List.foldlM_cons]
    exact bind_congr fun p => ih p.1 p.2

/-- Running a fold in the state-and-exception monad `StateT σ (Except ε)` is a pure `List.foldl`
chaining results with `Except.bind`. -/
theorem foldlM_run_except {σ ε β γ : Type u} (g : β → γ → StateT σ (Except ε) β) (l : List γ)
    (b : β) (s : σ) :
    (l.foldlM g b).run s =
      l.foldl (fun acc c => acc.bind fun p => (g p.1 c).run p.2) (.ok (b, s)) := by
  have hsplit (l : List γ) (x : Except ε (β × σ)) :
      l.foldl (fun acc c => acc.bind fun p => (g p.1 c).run p.2) x =
        x.bind fun p => l.foldl (fun acc c => acc.bind fun p => (g p.1 c).run p.2) (.ok p) := by
    induction l generalizing x with
    | nil => cases x <;> rfl
    | cons c l ih =>
      cases x with
      | error e => exact (ih (.error e)).trans rfl
      | ok p => rfl
  induction l generalizing b s with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldlM_cons, StateT.run_bind, List.foldl_cons]
    change _ = l.foldl _ ((g b c).run s)
    rw [hsplit]
    change Except.bind _ _ = Except.bind _ _
    congr 1
    funext p
    exact ih p.1 p.2

end StateT
