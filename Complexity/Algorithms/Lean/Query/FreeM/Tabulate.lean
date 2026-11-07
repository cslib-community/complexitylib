/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tabulation and folds in the free monad

`Cslib.FreeM.tabulate n f` runs the programs `f 0, …, f (n - 1)` in order and collects their
results as a function on `Fin n`; `Cslib.FreeM.tabulateMatrix` does the same for a matrix of
programs in row-major order. Their value is the pointwise value and their cost is the sum of the
costs. For monadic left folds, `Cslib.FreeM.eval_foldlM` and `Cslib.FreeM.cost_foldlM` compute the
value and the cost when every step has a known value and a constant cost.

## Main definitions

* `Cslib.FreeM.tabulate`, `Cslib.FreeM.tabulateMatrix`: run a family of programs in order.

## Main results

* `Cslib.FreeM.eval_tabulate`, `Cslib.FreeM.cost_tabulate`, `Cslib.FreeM.eval_tabulateMatrix`,
  `Cslib.FreeM.cost_tabulateMatrix`: value and cost of a tabulation.
* `Cslib.FreeM.eval_foldlM`, `Cslib.FreeM.cost_foldlM`: value and cost of a monadic left fold.
-/

public section

namespace Cslib.FreeM

variable {Q : Type → Type} {α : Type}

/-- Run the programs `f 0, …, f (n - 1)` in order and collect their results. -/
@[expose] def tabulate : (n : ℕ) → (Fin n → FreeM Q α) → FreeM Q (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
    let a ← f 0
    let rest ← tabulate n (fun i => f i.succ)
    return Fin.cons a rest

theorem eval_tabulate (oracle : {ι : Type} → Q ι → ι) :
    ∀ (n : ℕ) (f : Fin n → FreeM Q α), (tabulate n f).eval oracle = fun i => (f i).eval oracle
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
    simp only [tabulate, eval_bind, eval_pure, eval_tabulate oracle n]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem cost_tabulate {T : Type} [AddCommMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) :
    ∀ (n : ℕ) (f : Fin n → FreeM Q α),
      (tabulate n f).cost oracle weight = ∑ i, (f i).cost oracle weight
  | 0, f => by simp [tabulate]
  | n + 1, f => by
    simp only [tabulate, cost_bind, cost_pure, add_zero, cost_tabulate oracle weight n,
      Fin.sum_univ_succ]

/-- Run the entry programs `f i j` in row-major order and collect the resulting matrix. -/
@[expose] def tabulateMatrix (n : ℕ) (f : Fin n → Fin n → FreeM Q α) :
    FreeM Q (Matrix (Fin n) (Fin n) α) :=
  Matrix.of <$> tabulate n fun i => tabulate n (f i)

theorem eval_tabulateMatrix (oracle : {ι : Type} → Q ι → ι) (n : ℕ)
    (f : Fin n → Fin n → FreeM Q α) :
    (tabulateMatrix n f).eval oracle = Matrix.of fun i j => (f i j).eval oracle := by
  simp only [tabulateMatrix, eval_map, eval_tabulate]

theorem cost_tabulateMatrix {T : Type} [AddCommMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) (n : ℕ) (f : Fin n → Fin n → FreeM Q α) :
    (tabulateMatrix n f).cost oracle weight = ∑ i, ∑ j, (f i j).cost oracle weight := by
  simp only [tabulateMatrix, cost_map, cost_tabulate]

/-- The value of a monadic left fold whose steps have known values. -/
theorem eval_foldlM {β γ : Type} (oracle : {ι : Type} → Q ι → ι) (step : β → γ → FreeM Q β)
    (g : β → γ → β) (hstep : ∀ b c, (step b c).eval oracle = g b c) :
    ∀ (l : List γ) (b : β), (l.foldlM step b).eval oracle = l.foldl g b
  | [], b => rfl
  | c :: l, b => by
    simp only [List.foldlM_cons, eval_bind, hstep, List.foldl_cons, eval_foldlM oracle step g
      hstep l]

/-- The cost of a monadic left fold whose steps all cost `t`. -/
theorem cost_foldlM {β γ T : Type} [AddMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) (step : β → γ → FreeM Q β) (t : T)
    (hstep : ∀ b c, (step b c).cost oracle weight = t) :
    ∀ (l : List γ) (b : β), (l.foldlM step b).cost oracle weight = l.length • t
  | [], b => by simp
  | c :: l, b => by
    simp only [List.foldlM_cons, cost_bind, hstep, cost_foldlM oracle weight step t hstep l,
      List.length_cons, succ_nsmul']

end Cslib.FreeM
