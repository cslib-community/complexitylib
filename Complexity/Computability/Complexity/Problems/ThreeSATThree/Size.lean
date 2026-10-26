/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSATThree
public import Complexity.Logics.Propositional.CNF.ModelCount

/-!
# Total size bounds for the finite occurrence splitter

The existing `toThreeSATThree` reduction accepts arbitrary binary-labelled CNF inputs. Its
width-valid branch has one implication per literal occurrence; its rejecting branch is `[[]]`.
Distinct variables are bounded by literal occurrences, independently of the original label sizes.

## Main definitions

The existing total splitter, ordinary CNF variable count, and literal occurrences are reused.

## Main results

* `Cslib.Complexity.width_toThreeSATThree`: every total output has width at most three.
* `Cslib.Complexity.count_vars_toThreeSATThree_le`: every output variable occurs at most thrice.
* `Cslib.Complexity.size_toThreeSATThree_le`: the total incidence size is at most seven times
  the original clause and literal-occurrence size, including the unit offset.

## References

These are quantitative consequences of the finite splitter adapted from `lean-trominoes`
revision `6d5b36c15cec6cb18d30137b7f1c7fb92ea24332`. The imported construction records
the source credit.
The linear bound using occurrence counts is original.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- Even rejected inputs produce width at most three; no width assumption is required. -/
theorem width_toThreeSATThree (φ : CNF ℕ) :
    ∀ c ∈ toThreeSATThree φ, c.length ≤ 3 := by
  unfold toThreeSATThree
  split_ifs with hw
  · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa using CNF.width_toThreeOccurrence (by decide : 2 ≤ 3) hw' d hd
  · simp

/-- Every total output has at most three literal occurrences per variable, including repeats. -/
theorem count_vars_toThreeSATThree_le (φ : CNF ℕ) (v : ℕ) :
    (toThreeSATThree φ).vars.count v ≤ 3 := by
  unfold toThreeSATThree
  split_ifs
  · rw [CNF.vars_relabel]
    by_cases hv : v ∈ φ.toThreeOccurrence.vars.map ThreeSATThree.numberCopy
    · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hv
      rw [List.count_map_of_injective _ _ ThreeSATThree.numberCopy_injective]
      exact CNF.count_vars_toThreeOccurrence_le φ x
    · simp [List.count_eq_zero.2 hv]
  · simp [CNF.vars]

/-- Exact clause/literal counts and the generic variable-count bound give this sharper bound
on the width-valid branch. Original labels may be arbitrarily large binary naturals. -/
theorem size_toThreeSATThree_le_of_width (φ : CNF ℕ) (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (toThreeSATThree φ).numVars + (toThreeSATThree φ).length +
      (toThreeSATThree φ).vars.length + 1 ≤ φ.length + 7 * φ.vars.length + 1 := by
  have hn := CNF.numVars_le_length_vars (toThreeSATThree φ)
  rw [length_vars_toThreeSATThree φ hw] at hn ⊢
  rw [length_toThreeSATThree φ hw]
  omega

/-- The total splitter's incidence size is linearly bounded on all binary-labelled CNF inputs.
The rejecting output `[[]]` has size two, so invalid-width inputs satisfy the same bound. -/
theorem size_toThreeSATThree_le (φ : CNF ℕ) :
    (toThreeSATThree φ).numVars + (toThreeSATThree φ).length +
      (toThreeSATThree φ).vars.length + 1 ≤ 7 * (φ.length + φ.vars.length + 1) := by
  by_cases hw : ∀ c ∈ φ, c.length ≤ 3
  · have h := size_toThreeSATThree_le_of_width φ hw
    omega
  · have hg : φ.all (fun c => decide (c.length ≤ 3)) = false := by simpa using hw
    simp only [toThreeSATThree, hg, Bool.false_eq_true, ite_false]
    change 2 ≤ 7 * (φ.length + φ.vars.length + 1)
    omega

end Cslib.Complexity
