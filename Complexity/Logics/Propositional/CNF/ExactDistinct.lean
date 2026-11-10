/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactThree

/-!
# Clauses with exactly `k` distinct variables

`Clause.IsExactDistinct k` and `CNF.IsExactDistinct k` require exactly `k` literals per clause, on
pairwise distinct variables, with unrestricted polarities. This is the notion of a `k`-CNF formula
used by Moser's algorithmic Local Lemma, where a resampling of a clause assigns exactly `k` fresh
random bits. For `k = 3` it is `Clause.IsExactThreeDistinct`.

## Main definitions

* `Cslib.Logic.PL.Clause.IsExactDistinct`, `Cslib.Logic.PL.CNF.IsExactDistinct`.

## Main results

* `Cslib.Logic.PL.Clause.isExactDistinct_three_iff`: the case `k = 3`.
* `Cslib.Logic.PL.CNF.IsExactDistinct.ne_nil`: for `k > 0` every clause is nonempty.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- A clause has **exactly `k` distinct variables** when it has `k` literals and its variables have
no duplicates. -/
def Clause.IsExactDistinct (k : ℕ) (c : Clause V) : Prop :=
  c.length = k ∧ (c.map Prod.fst).Nodup

/-- A formula is an **exact `k`-CNF with distinct variables per clause** when every clause has
exactly `k` distinct variables. -/
def CNF.IsExactDistinct (k : ℕ) (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.IsExactDistinct k

/-- Whether a clause has exactly `k` distinct variables is decidable. -/
instance [DecidableEq V] {k : ℕ} {c : Clause V} : Decidable (c.IsExactDistinct k) :=
  inferInstanceAs (Decidable (c.length = k ∧ (c.map Prod.fst).Nodup))

/-- Whether every clause of a formula has exactly `k` distinct variables is decidable. -/
instance [DecidableEq V] {k : ℕ} {φ : CNF V} : Decidable (φ.IsExactDistinct k) :=
  inferInstanceAs (Decidable (∀ c ∈ φ, c.IsExactDistinct k))

/-- The case `k = 3` is `Clause.IsExactThreeDistinct`. -/
theorem Clause.isExactDistinct_three_iff {c : Clause V} :
    c.IsExactDistinct 3 ↔ c.IsExactThreeDistinct :=
  Iff.rfl

/-- For `k > 0`, the clauses of an exact `k`-CNF are nonempty. -/
theorem CNF.IsExactDistinct.ne_nil {k : ℕ} {φ : CNF V} (hφ : φ.IsExactDistinct k) (hk : 0 < k) :
    ∀ c ∈ φ, c ≠ [] := fun c hc h => by
  have := (hφ c hc).1
  rw [h, List.length_nil] at this
  omega

end Cslib.Logic.PL
