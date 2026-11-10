/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom
import all Init.Data.List.Control

/-!
# Monadic filtering with pure tests and under monad morphisms

Core `List.filterM p xs` runs the effectful test `p` once on each element of `xs`, from left to
right, and keeps the accepted elements in order. Core proves little about it. This module records
the two facts that let a program written with `List.filterM` be run purely and transported along
monad morphisms. Core defines `List.filterM` through the accumulator `List.filterAuxM` without
exposing the body, so this module imports `Init.Data.List.Control` with `import all`, as core's
own `Init.Data.List.Monadic` does.

## Main results

* `List.filterM_pure`: with pure tests, `List.filterM` is `List.filter`.
* `Cslib.IsMonadHom.map_filterM`: monad morphisms commute with `List.filterM`.
-/

public section

namespace List

private theorem filterAuxM_pure {α : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (p : α → Bool) (xs acc : List α) :
    filterAuxM (fun x => (pure (p x) : m Bool)) xs acc = pure ((xs.filter p).reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterAuxM, pure_bind, ih, filter_cons]
    cases p x <;> simp

/-- With pure tests, core `List.filterM` is `List.filter`. -/
@[simp] theorem filterM_pure {α : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (p : α → Bool) (xs : List α) :
    xs.filterM (fun x => (pure (p x) : m Bool)) = pure (xs.filter p) := by
  simp only [filterM, filterAuxM_pure, pure_bind, append_nil, reverse_reverse]

end List

namespace Cslib

private theorem IsMonadHom.map_filterAuxM {α : Type} {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f) (p : α → m Bool) (xs acc : List α) :
    f (List.filterAuxM p xs acc) = List.filterAuxM (fun x => f (p x)) xs acc := by
  induction xs generalizing acc with
  | nil => exact hf.map_pure _
  | cons x xs ih =>
    simp only [List.filterAuxM, hf.map_bind, ih]

/-- Monad morphisms commute with core `List.filterM`. -/
theorem IsMonadHom.map_filterM {α : Type} {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f) (p : α → m Bool) (xs : List α) :
    f (xs.filterM p) = xs.filterM (fun x => f (p x)) := by
  simp only [List.filterM, hf.map_bind, hf.map_filterAuxM, hf.map_pure]

end Cslib
