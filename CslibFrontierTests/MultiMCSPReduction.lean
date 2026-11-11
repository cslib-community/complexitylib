/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.MultiNPHard.Reduction
import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Tests for the reduction from Set Cover to Multi-MCSP

Concrete instances of `CslibFrontier.Computability.MCSP.MultiNPHard.Reduction`:

1. Parameters: two ground elements and two sets give `N + t + 4 = 8` and arity `6 · size 8 = 24`.
2. Positions: with a repeated ground element, the positions of each set and the relabelling of a
   cover.
3. An empty ground list maps to the fixed instance `fallback`, which is positive.
4. Completeness: `({0, 1}; {0}, {1})` with `k = 2` is a yes-instance of `GapSetCover 3`, so every
   random string gives a yes-instance of Multi-MCSP, over the constant-free basis and cslib's basis.
5. Soundness: three singletons on three elements with `k = 1` are a no-instance, so at most a third
   of the tables give a yes-instance.
6. The randomized reduction, given the running-time hypothesis, for both bases.
-/

namespace CslibFrontierTests.MultiMCSPReduction

open Cslib Cslib.Circuits Cslib.Complexity Cslib.MultiMCSP Cslib.MultiMCSP.Reduction Finset

/-! ### Parameters -/

/-- The sets `{0}` and `{1}` on the ground list `[0, 1]`. -/
private def S₀ : SetSystem := ⟨[0, 1], [[0], [1]]⟩

example : bound S₀ = 8 := by decide

example : arity S₀ = 24 := by
  rw [arity, show bound S₀ = 2 ^ 3 by decide, Nat.size_pow]

example : 18 ≤ arity S₀ := eighteen_le_arity S₀

/-! ### Positions -/

/-- The ground list `[5, 5, 7]` repeats `5`; the sets are `{5}` and `{7, 9}`. -/
private def S₁ : SetSystem := ⟨[5, 5, 7], [[5], [7, 9]]⟩

/-- Set `0` holds the positions `0` and `1` of the repeated element `5`. -/
example : residues S₁ ⟨0, by decide⟩ = {0, 1} := by decide

/-- Set `1` holds the position of `7`; its element `9` is not in the ground list and is ignored. -/
example : residues S₁ ⟨1, by decide⟩ = {2} := by decide

/-- Both sets cover the positions, hence cover `S₁`. -/
example : S₁.IsCover univ :=
  (forall_residues_iff S₁ univ).mp (by decide)

/-- Set `1` alone misses position `0`, so it does not cover `S₁`. -/
example : ¬ S₁.IsCover {⟨1, by decide⟩} := by
  rw [← forall_residues_iff]
  decide

/-! ### The empty ground list -/

example (k : ℕ) (r : List Bool) : reduce ((⟨[], [[0]]⟩, k), r) = fallback :=
  reduce_of_ground_eq_nil rfl k r

example : fallback.Positive := reduce_positive ((⟨[], []⟩, 0), [])

/-! ### Completeness -/

private theorem S₀_yes : (S₀, 2) ∈ (GapSetCover 3).yes := by
  have hC : S₀.IsCover univ := (forall_residues_iff S₀ univ).mp (by decide)
  have hopt := SetSystem.optCoverSize_le hC
  simp only [card_univ, Fintype.card_fin] at hopt
  exact mem_yes_iff.mpr ⟨⟨univ, hC⟩, hopt⟩

example (r : List Bool) : reduce ((S₀, 2), r) ∈ MultiMCSP Boolean.DeMorgan.interpretation :=
  reduce_mem_of_yes S₀_yes r

example (r : List Bool) : reduce ((S₀, 2), r) ∈ MultiMCSP Boolean.interpretation :=
  reduce_mem_of_yes S₀_yes r

/-! ### Soundness -/

/-- The singletons `{0}, {1}, {2}` on the ground list `[0, 1, 2]`. -/
private def S₂ : SetSystem := ⟨[0, 1, 2], [[0], [1], [2]]⟩

private theorem S₂_no : (S₂, 1) ∈ (GapSetCover 3).no := by
  have hC : S₂.IsCover univ := (forall_residues_iff S₂ univ).mp (by decide)
  have hcov : S₂.Coverable := ⟨univ, hC⟩
  -- Every cover uses all three sets.
  have hopt : 3 ≤ S₂.optCoverSize := (SetSystem.le_optCoverSize_iff hcov).mpr fun C hC => by
    rw [← forall_residues_iff] at hC
    revert C
    decide
  exact mem_no_iff.mpr ⟨hcov, hopt, Nat.one_pos⟩

/-- A no-instance has a nonempty ground list. -/
example : S₂.ground ≠ [] := ground_ne_nil_of_mem_no S₂_no

open scoped Classical in
example : 3 * #{T : Fin (2 ^ arity S₂) → Bool |
    ofTable S₂ 1 T ∈ MultiMCSP Boolean.DeMorgan.interpretation} ≤ 2 ^ 2 ^ arity S₂ :=
  three_mul_card_ofTable_mem_le S₂_no

/-! ### The randomized reduction, given its running time -/

open Turing.MultiTapeTM in
example (h : ComputableInPolyTime reduce (encPair encSetCover encBits) encInstance) :
    PromiseProblem.RPReducible encSetCover encInstance (GapSetCover 3)
      ((PromiseProblem.ofSet (MultiMCSP Boolean.DeMorgan.interpretation)).restrict
        {x | x.Positive}) :=
  rpReducible_of_computableInPolyTime h

open Turing.MultiTapeTM in
example (h : ComputableInPolyTime reduce (encPair encSetCover encBits) encInstance) :
    PromiseProblem.RPReducible encSetCover encInstance (GapSetCover 3)
      ((PromiseProblem.ofSet (MultiMCSP Boolean.interpretation)).restrict {x | x.Positive}) :=
  rpReducible_of_computableInPolyTime h

end CslibFrontierTests.MultiMCSPReduction
