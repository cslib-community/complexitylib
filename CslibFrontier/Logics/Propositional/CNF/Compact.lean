/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
import Mathlib.Data.List.Basic

/-!
# Compact variable numbering for CNF formulas

Variables are renamed by their first positions in the list of literal occurrences. The resulting
indices are smaller than the number of occurrences, even when the original names have a succinct
encoding. Repeated variables retain the same name. This prepares reductions whose output indices
are unary without expanding binary input names into unary integers.

## Main definitions

* `Cslib.Logic.PL.CNF.compact`: rename variables by their first occurrences.

## Main results

* `Cslib.Logic.PL.CNF.satisfiable_compact`: compaction preserves satisfiability.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

/-- Rename each variable by its first position among all literal occurrences. -/
def compact (φ : CNF V) : CNF ℕ := φ.relabel φ.vars.idxOf

/-- Compaction keeps all clauses, their order, and their lengths. -/
@[simp]
theorem map_length_compact (φ : CNF V) :
    (φ.compact.map List.length) = φ.map List.length := by
  simp [compact, CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]

/-- Compaction preserves the number of clauses. -/
@[simp]
theorem length_compact (φ : CNF V) : φ.compact.length = φ.length := by
  simp [compact, CNF.relabel]

/-- Every renamed variable is below the number of literal occurrences. -/
theorem mem_vars_compact_lt (φ : CNF V) {v : ℕ} (hv : v ∈ φ.compact.vars) :
    v < φ.vars.length := by
  simp only [compact, CNF.vars, CNF.relabel] at hv
  obtain ⟨_, hmem, rfl⟩ := List.mem_map.1 hv
  obtain ⟨_, hc, hmem⟩ := List.mem_flatten.1 hmem
  obtain ⟨c, hclause, rfl⟩ := List.mem_map.1 hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hmem
  exact List.idxOf_lt_length_of_mem
    (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hclause, hl⟩, rfl⟩)

/-- Reading original names at the compact positions recovers the original evaluation. -/
theorem eval_compact (φ : CNF V) (σ : V → Bool) :
    φ.compact.eval (fun i => φ.vars[i]?.elim false σ) = φ.eval σ := by
  rw [compact, CNF.eval_relabel]
  apply CNF.eval_congr
  intro v hv
  simp [List.getElem?_idxOf hv]

/-- Compaction preserves satisfiability, without requiring a finite variable type. -/
theorem satisfiable_compact (φ : CNF V) : φ.compact.Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ φ.vars.idxOf, by simpa only [compact, CNF.eval_relabel] using hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun i => φ.vars[i]?.elim false σ, (eval_compact φ σ).trans hσ⟩

end Cslib.Logic.PL.CNF
