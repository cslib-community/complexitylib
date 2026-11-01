/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the variable occurrences of a CSP instance

The variable occurrences `F.vars` of a CSP instance bound its other sizes. When every scope is
nonempty there are at least as many occurrences as constraints (`CSP.length_le_length_vars`), and
when every variable occurs at most `Δ` times there are at most `Δ` occurrences per variable
(`CSP.length_vars_le_mul_numVars`). The auxiliary formula `F.varCNF` has one clause per
constraint (`CSP.length_varCNF`).

## Main results

* `Cslib.Logic.PL.CSP.length_varCNF`: `F.varCNF` has as many clauses as `F` has constraints.
* `Cslib.Logic.PL.CSP.length_le_length_vars`: with nonempty scopes, at least as many occurrences
  as constraints.
* `Cslib.Logic.PL.CSP.length_vars_le_mul_numVars`: at most `Δ n` occurrences when every one of
  the `n` variables occurs at most `Δ` times.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*}

@[simp]
theorem length_varCNF (F : CSP Rel V) : F.varCNF.length = F.length := List.length_map _

/-- An instance whose scopes are nonempty has at least as many variable occurrences as
constraints. -/
theorem length_le_length_vars {F : CSP Rel V} (h : ∀ c ∈ F, 1 ≤ c.2.length) :
    F.length ≤ F.vars.length := by
  induction F with
  | nil => simp
  | cons c F ih =>
    have hc := h c List.mem_cons_self
    have hF := ih fun c' hc' => h c' (List.mem_cons_of_mem c hc')
    simp only [vars, List.flatMap_cons, List.length_append, List.length_cons] at hF ⊢
    omega

/-- An instance in which every variable occurs at most `Δ` times has at most `Δ n` variable
occurrences, for `n` variables. -/
theorem length_vars_le_mul_numVars [DecidableEq V] {F : CSP Rel V} {Δ : ℕ}
    (hΔ : ∀ v, F.vars.count v ≤ Δ) : F.vars.length ≤ Δ * F.numVars := by
  rw [← List.sum_toFinset_count_eq_length, numVars, mul_comm]
  exact Finset.sum_le_card_nsmul _ _ _ fun v _ => hΔ v

end Cslib.Logic.PL.CSP
