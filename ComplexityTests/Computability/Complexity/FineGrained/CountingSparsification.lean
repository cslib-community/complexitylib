/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingSparsification
public import ComplexityTests.Computability.Complexity.FineGrained.CountingSparsifyPolyTime

/-!
# Tests for depth-first counting-sparsification search

Concrete execution trace and edge-case tests for `Cslib.Complexity.CountingSparsify` and
`Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule`:
* Step-by-step stack and accumulator trace of `CountingSparsify.step` on `flowerWithTautology`
  (showing the `2 ^ (n - ψ.numVars)` unused-variable weighting on the unit heart leaf
  `[[(0, true)]]` contributing `2 ^ (3 - 1) * 1 = 4` and the 3-unit petal/negated-heart leaf
  contributing `2 ^ (3 - 3) * 1 = 1` for a total of `5 = flowerWithTautology.modelCount`);
* Full `CountingSparsify.search` evaluation on `flowerWithTautology`, the empty formula `[]` (at
  `k = 0` and `k = 2`), the empty-clause formula `[[]]`, and formulas exceeding width `k`.
-/

@[expose] public section

namespace Cslib.Complexity.Tests

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification

/-! ### 1. Step-by-step trace of `CountingSparsify.step` on `flowerWithTautology` -/

/-- Step-by-step trace on `flowerWithTautology`: initial state (`n = 3` declared variables, stack
containing the nontautological normal form of the 2-clause flower, accumulator `0`), step 1
(popping the non-sparse flower into its `false` and `true` children), step 2 (popping the sparse
`false` child weighted by `2 ^ (3 - 1) * 1 = 4`), and step 3 (popping the sparse `true` child
weighted by `2 ^ (3 - 3) * 1 = 1` for a total of `5`). -/
example :
    CountingSparsify.init 2 flowerWithTautology =
      (3, ([[[(0, true), (1, true)], [(0, true), (2, false)]]], 0)) ∧
    CountingSparsify.step 2 2 CNF.modelCount (CountingSparsify.init 2 flowerWithTautology) =
      (3, ([[[(0, true)]], [[(1, true)], [(2, false)], [(0, false)]]], 0)) ∧
    (CountingSparsify.step 2 2 CNF.modelCount)^[2]
        (CountingSparsify.init 2 flowerWithTautology) =
      (3, ([[[(1, true)], [(2, false)], [(0, false)]]], 4)) ∧
    (CountingSparsify.step 2 2 CNF.modelCount)^[3]
        (CountingSparsify.init 2 flowerWithTautology) =
      (3, ([], 5)) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### 2. Full `CountingSparsify.search` evaluation and edge cases -/

/-- `CountingSparsify.search` recovers all `5` satisfying assignments of `flowerWithTautology` on
its `3` occurring variables, handles `[]` at `k = 0` and `k = 2` and `[[]]`, and rejects a 3-CNF
clause under the `k = 2` width guard. -/
example :
    CountingSparsify.search 2 2 2 2 CNF.modelCount flowerWithTautology = 5 ∧
    CountingSparsify.search 2 2 2 2 CNF.modelCount flowerWithTautology =
      flowerWithTautology.modelCount ∧
    CountingSparsify.search 2 2 0 1 CNF.modelCount ([] : CNF ℕ) = 1 ∧
    CountingSparsify.search 2 2 2 1 CNF.modelCount ([] : CNF ℕ) = 1 ∧
    CountingSparsify.search 2 2 2 1 CNF.modelCount ([[]] : CNF ℕ) = 0 ∧
    CountingSparsify.search 2 2 2 1 CNF.modelCount [[(0, true), (1, true), (2, true)]] = 0 := by
  decide

/-! ### 3. Non-vacuity witness for `CountingTreeBound` at width `K = 1` -/

/-- At width `K = 1`, every `CountingNormalized 1` formula is already sparse because no clause of
width `≤ 1` can strictly contain a nonempty heart (`1 ≤ H.card < c ≤ 1`). Consequently the only leaf
word is `[]`, witnessing `CountingTreeBound M 1 B L_coeff` unconditionally. -/
theorem countingTreeBound_one {M : ℕ} (hM : 1 ≤ M) (B L_coeff : ℕ) :
    CountingSparsify.CountingTreeBound M 1 B L_coeff hM le_rfl := by
  intro ψ declared _
  have hsparse : ClauseSet.Sparsification.Sparse (countingThreshold M) ψ.1.toClauseSet := by
    intro c H hH
    obtain ⟨D, hD⟩ := hH.flower_nonempty (one_le_countingThreshold hM)
    have hDcard : D.card ≤ 1 := ψ.2.card_le D (ClauseSet.Sparsification.flower_subset _ _ _ hD)
    have hDc : D.card = c := (ClauseSet.Sparsification.mem_flower.mp hD).2.1
    have := hH.1
    have := hH.2.1
    omega
  refine ⟨fun w hw => ?_, fun W hW => ?_⟩
  · cases w with
    | nil => simp
    | cons b u => exact absurd hsparse hw.1
  · have hsub : W ⊆ {[]} := fun w hw => by
      rw [Finset.mem_singleton]
      cases w with
      | nil => rfl
      | cons b u => exact absurd hsparse (hW _ hw).1
    calc W.card ≤ ({[]} : Finset (List Bool)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton []
      _ ≤ 2 ^ (declared.card / B + 1) := Nat.one_le_two_pow

example (φ : CNF ℕ) (hφ : ∀ c ∈ φ, c.length ≤ 1) :
    CountingSparsify.search 2 1 1 1 CNF.modelCount φ = φ.modelCount :=
  CountingSparsify.search_eq_modelCount (by omega) (by omega) (by omega) le_rfl
    (countingTreeBound_one (by omega) 1 1) (fun _ _ _ => rfl) hφ

end Cslib.Complexity.Tests
