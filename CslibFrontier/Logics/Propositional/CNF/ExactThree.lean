/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF

/-!
# Exact three-literal clauses with distinct variables

`Clause.IsExactThreeDistinct` and `CNF.IsExactThreeDistinct` require exactly three
pairwise distinct variables per clause. Literal polarities are unrestricted.

## Main results

* `Clause.isExactThreeDistinct_iff`: the explicit three-literal characterization.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- A clause has **three distinct variables** when it has length `3` and its variables have no
duplicates. -/
def Clause.IsExactThreeDistinct (c : Clause V) : Prop :=
  c.length = 3 ∧ (c.map Prod.fst).Nodup

/-- A formula is an **exact 3-CNF with distinct variables per clause** when every clause has three
distinct variables. -/
def CNF.IsExactThreeDistinct (φ : CNF V) : Prop :=
  ∀ c ∈ φ, c.IsExactThreeDistinct

/-- Whether a clause has three distinct variables is decidable. -/
instance [DecidableEq V] {c : Clause V} : Decidable c.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (c.length = 3 ∧ (c.map Prod.fst).Nodup))

/-- Whether every clause of a CNF formula has three distinct variables is decidable. -/
instance [DecidableEq V] {φ : CNF V} : Decidable φ.IsExactThreeDistinct :=
  inferInstanceAs (Decidable (∀ c ∈ φ, c.IsExactThreeDistinct))

/-- An exact 3-clause with distinct variables has length `3`. -/
theorem Clause.IsExactThreeDistinct.length_eq {c : Clause V} (hc : c.IsExactThreeDistinct) :
    c.length = 3 :=
  hc.1

/-- The variables of an exact 3-clause with distinct variables have no duplicates. -/
theorem Clause.IsExactThreeDistinct.nodup_map_fst {c : Clause V} (hc : c.IsExactThreeDistinct) :
    (c.map Prod.fst).Nodup :=
  hc.2

/-- Every exact 3-clause with distinct variables is a list of three literals on pairwise distinct
variables. -/
theorem Clause.isExactThreeDistinct_iff {c : Clause V} :
    c.IsExactThreeDistinct ↔
      ∃ l₁ l₂ l₃ : Literal V,
        c = [l₁, l₂, l₃] ∧ l₁.1 ≠ l₂.1 ∧ l₁.1 ≠ l₃.1 ∧ l₂.1 ≠ l₃.1 := by
  constructor
  · rintro ⟨hlen, hnodup⟩
    match c, hlen with
    | [l₁, l₂, l₃], _ =>
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, and_true] at hnodup
      exact ⟨l₁, l₂, l₃, rfl, hnodup.1.1, hnodup.1.2, hnodup.2.1⟩
  · rintro ⟨l₁, l₂, l₃, rfl, h12, h13, h23⟩
    refine ⟨rfl, ?_⟩
    simp [h12, h13, h23]

end Cslib.Logic.PL
