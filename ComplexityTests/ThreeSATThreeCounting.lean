/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.ThreeSATThree.Counting
import Complexity.Logics.Propositional.CNF.Compact.ModelCount
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

/-! # Exact counts under occurrence splitting and numbering -/

open Cslib.Logic.PL Cslib.Complexity

/-- Model-count preservation under `toThreeSATThree` and `CNF.toThreeOccurrence`, and guarded
`SharpThreeSAT` / `SharpThreeSATThree` counts across width-three and width-four formulas. -/
example :
    (toThreeSATThree []).modelCount = 1 ∧
    (toThreeSATThree [[]]).modelCount = 0 ∧
    (toThreeSATThree [[(0, true), (0, true), (0, true)]]).modelCount = 1 ∧
    (toThreeSATThree [[(7, true)]]).modelCount = 1 ∧
    (toThreeSATThree
      [[(0, true), (1, true)], [(0, true), (1, true)]]).modelCount = 3 ∧
    (CNF.toThreeOccurrence
      [[(0, true), (0, false), (0, true), (0, false)]]).modelCount = 2 ∧
    (toThreeSATThree
      [[(0, true), (0, false), (0, true), (0, false)]]).modelCount = 0 ∧
    SharpThreeSAT [[(0, true), (0, false), (0, true), (0, false)]] = 0 ∧
    SharpThreeSAT [[(0, true), (0, true), (0, true)], [(0, true)]] = 1 ∧
    SharpThreeSATThree [[(0, true), (0, true), (0, true)], [(0, true)]] = 0 ∧
    SharpThreeSATThree
      (toThreeSATThree [[(0, true), (0, true), (0, true)], [(0, true)]]) = 1 :=
  ⟨by rw [modelCount_toThreeSATThree _ (by simp)]; decide,
    by rw [modelCount_toThreeSATThree _ (by simp)]; decide,
    by rw [modelCount_toThreeSATThree _ (by simp)]; decide,
    by rw [modelCount_toThreeSATThree _ (by simp)]; decide,
    by rw [modelCount_toThreeSATThree _ (by simp)]; decide,
    by rw [CNF.modelCount_toThreeOccurrence]; decide,
    by decide, by decide, by decide, by decide,
    by rw [sharpThreeSATThree_toThreeSATThree]; decide⟩

/-- Relabeling and compaction model-count invariance, colliding variable relabeling, and the
bridge from guarded counts to `ThreeSAT` / `ThreeSATThree`. -/
example :
    CNF.modelCount (CNF.relabel (fun v : ℕ => v % 2) [[(7, true), (42, true)]]) = 3 ∧
    CNF.modelCount ([[(0, true), (1, true)]] : CNF ℕ) = 3 ∧
    CNF.modelCount (CNF.relabel (fun _ => 0) ([[(0, true), (1, true)]] : CNF ℕ)) = 1 ∧
    CNF.modelCount (CNF.relabel (fun v => nomatch v : Empty → ℕ) []) = 1 ∧
    CNF.modelCount (CNF.relabel (fun _ => 0) ([] : CNF ℕ)) = 1 ∧
    CNF.compact ([[(1000000, true), (1000000, true), (7, true)]] : CNF ℕ) =
      [[(0, true), (0, true), (2, true)]] ∧
    CNF.modelCount (CNF.compact ([[(1000000, true), (1000000, true), (7, true)]] : CNF ℕ)) = 3 ∧
    [[(7, true)]] ∈ ThreeSAT ∧
    [[(7, true)]] ∈ ThreeSATThree ∧
    [[(0, true), (0, true), (0, true)], [(0, true)]] ∉ ThreeSATThree := by
  refine ⟨?_, by decide, by decide,
    by rw [CNF.modelCount_relabel_of_injOn _ (fun v => nomatch v)]; decide,
    by rw [CNF.modelCount_relabel_of_injOn _ (by simp [CNF.vars, Set.InjOn])]; decide,
    by decide,
    by rw [CNF.modelCount_compact]; decide,
    SharpThreeSAT.mem_ThreeSAT_iff.mpr (by decide),
    SharpThreeSATThree.mem_ThreeSATThree_iff.mpr (by decide),
    by rw [SharpThreeSATThree.mem_ThreeSATThree_iff]; decide⟩
  rw [CNF.modelCount_relabel_of_injOn _ (by
    intro a ha b hb h
    change a ∈ [7, 42] at ha
    change b ∈ [7, 42] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | norm_num at h)]
  decide
