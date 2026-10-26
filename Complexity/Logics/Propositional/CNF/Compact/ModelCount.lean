/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.GetD

/-!
# Model counts under compact variable numbering

First-occurrence numbering preserves the number of satisfying assignments on the variables
occurring in a formula. The variable type may be infinite or empty.

## Main results

* `Cslib.Logic.PL.CNF.modelCount_compact`: compaction preserves the model count.

## References

This is an elementary counting property of the existing compaction construction.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

/-- First-occurrence numbering preserves the number of satisfying assignments, including for
empty formulas, empty clauses, and repeated literal occurrences. -/
theorem modelCount_compact (φ : CNF V) : φ.compact.modelCount = φ.modelCount := by
  refine modelCount_eq_card_filter (fun σ (v : φ.vars.toFinset) => σ (φ.vars.idxOf (v : V)))
    (fun τ => φ.eval (φ.extendAssignment τ) = true) (fun σ τ _ _ => ?_) fun τ => ?_
  · rw [compact, vars_relabel, List.forall_mem_map, funext_iff, Subtype.forall]
    simp only [List.mem_toFinset]
  · constructor
    · intro hτ
      let σ : ℕ → Bool := fun i => φ.vars[i]?.elim false (φ.extendAssignment τ)
      have he : ∀ v ∈ φ.vars, σ (φ.vars.idxOf v) = φ.extendAssignment τ v := by
        intro v hv
        simp [σ, List.getElem?_idxOf hv]
      refine ⟨σ, ?_, funext fun v => ?_⟩
      · rw [compact, eval_relabel]
        exact (eval_congr he).trans hτ
      · exact (he v (List.mem_toFinset.1 v.2)).trans
          (extendAssignment_of_mem _ (List.mem_toFinset.1 v.2))
    · rintro ⟨σ, hσ, rfl⟩
      rw [compact, eval_relabel] at hσ
      rw [← hσ]
      exact eval_extendAssignment_restrict φ (σ ∘ φ.vars.idxOf)

end Cslib.Logic.PL.CNF
