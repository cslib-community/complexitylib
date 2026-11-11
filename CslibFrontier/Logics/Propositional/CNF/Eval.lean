/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF

/-!
# Evaluating a clause

Two basic facts about `Cslib.Logic.PL.Clause.eval`, complementing
`Cslib.Logic.PL.Clause.eval_eq_true_iff`: a clause is false exactly when every literal is read
against its polarity, and its value depends only on the values of its variables. They live in this
leaf module rather than in `CslibFrontier.Logics.Propositional.CNF`, which is widely imported.

## Main results

* `Cslib.Logic.PL.Clause.eval_eq_false_iff`: a clause is false iff each of its literals is false.
* `Cslib.Logic.PL.Clause.eval_congr`: a clause depends only on the values of its variables.
-/

public section

namespace Cslib.Logic.PL

/-- A clause is false exactly when each of its literals is read against its polarity. -/
theorem Clause.eval_eq_false_iff {V : Type*} (σ : V → Bool) (c : Clause V) :
    c.eval σ = false ↔ ∀ l ∈ c, σ l.1 = !l.2 := by
  rw [← Bool.not_eq_true, Clause.eval_eq_true_iff]
  simp only [not_exists, not_and]
  refine forall₂_congr fun l _ => ?_
  cases σ l.1 <;> cases l.2 <;> simp

/-- A clause only depends on the values of its variables. -/
theorem Clause.eval_congr {V : Type*} {σ τ : V → Bool} {c : Clause V}
    (h : ∀ l ∈ c, σ l.1 = τ l.1) : c.eval σ = c.eval τ := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  exact exists_congr fun l => and_congr_right fun hl => by rw [h l hl]

end Cslib.Logic.PL
