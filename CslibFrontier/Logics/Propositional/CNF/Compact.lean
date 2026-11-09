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

* `Cslib.Logic.PL.CNF.satisfiable_relabel_idxOf`: renaming variables by their positions in a list
  containing them preserves satisfiability.
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

/-- Renaming each variable by its position in a list `l` containing all variables of `φ` is undone
by reading the names back from `l`. -/
theorem eval_relabel_idxOf (φ : CNF V) {l : List V} (hl : ∀ v ∈ φ.vars, v ∈ l) (σ : V → Bool) :
    (φ.relabel l.idxOf).eval (fun i => l[i]?.elim false σ) = φ.eval σ := by
  rw [CNF.eval_relabel]
  apply CNF.eval_congr
  intro v hv
  simp [List.getElem?_idxOf (hl v hv)]

/-- Renaming by positions in a list containing all variables preserves satisfiability. -/
theorem satisfiable_relabel_idxOf (φ : CNF V) {l : List V} (hl : ∀ v ∈ φ.vars, v ∈ l) :
    (φ.relabel l.idxOf).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ l.idxOf, by simpa only [CNF.eval_relabel] using hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun i => l[i]?.elim false σ, (eval_relabel_idxOf φ hl σ).trans hσ⟩

/-- Reading original names at the compact positions recovers the original evaluation. -/
theorem eval_compact (φ : CNF V) (σ : V → Bool) :
    φ.compact.eval (fun i => φ.vars[i]?.elim false σ) = φ.eval σ :=
  eval_relabel_idxOf φ (fun _ h => h) σ

/-- Compaction preserves satisfiability, without requiring a finite variable type. -/
theorem satisfiable_compact (φ : CNF V) : φ.compact.Satisfiable ↔ φ.Satisfiable :=
  satisfiable_relabel_idxOf φ fun _ h => h

end Cslib.Logic.PL.CNF
