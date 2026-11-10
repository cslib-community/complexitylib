/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Vector.Basic

/-!
# Evaluation and cost of `List.Vector.mOfFn` in query programs

`List.Vector.mOfFn f` runs the programs `f 0, …, f (n - 1)` in order and collects their results
in a vector. Mathlib defines it by structural recursion on `n`, so concrete instances reduce in
the kernel and `decide` can check them. This module records how `FreeM.eval` and `FreeM.cost`
act on it: evaluation is pointwise, and cost is the sum of the costs of the `n` programs.

## Main results

* `Cslib.FreeM.eval_mOfFn`: `(mOfFn f).eval oracle = ofFn fun i => (f i).eval oracle`.
* `Cslib.FreeM.cost_mOfFn`: `(mOfFn f).cost oracle weight = ∑ i, (f i).cost oracle weight`.
-/

public section

namespace Cslib.FreeM

universe u v

variable {F : Type u → Type v} {α : Type u}

/-- Evaluating `List.Vector.mOfFn f` evaluates each program `f i`. -/
@[simp] theorem eval_mOfFn (oracle : {ι : Type u} → F ι → ι) {n : ℕ} (f : Fin n → FreeM F α) :
    (List.Vector.mOfFn f).eval oracle = List.Vector.ofFn fun i => (f i).eval oracle := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.Vector.mOfFn, eval_bind, eval_pure, ih, List.Vector.ofFn]

/-- The cost of `List.Vector.mOfFn f` is the total cost of the programs `f i`. -/
@[simp] theorem cost_mOfFn {T : Type*} [AddCommMonoid T] (oracle : {ι : Type u} → F ι → ι)
    (weight : {ι : Type u} → F ι → T) {n : ℕ} (f : Fin n → FreeM F α) :
    (List.Vector.mOfFn f).cost oracle weight = ∑ i, (f i).cost oracle weight := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.Vector.mOfFn, cost_bind, cost_pure, ih, Fin.sum_univ_succ, add_zero]

end Cslib.FreeM
