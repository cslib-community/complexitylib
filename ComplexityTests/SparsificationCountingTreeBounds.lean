/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTreeBounds

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingTreeBounds

/-! ### 1. Nontautological filtering and `reduce` normalization -/

private def tautClause : Finset (Literal (Fin 3)) :=
  {(0, true), (0, false), (1, true)}

private def properClause₀ : Finset (Literal (Fin 3)) :=
  {(0, true), (1, true)}

private def properClause₁ : Finset (Literal (Fin 3)) :=
  {(0, true), (2, true)}

private def mixedSet : ClauseSet (Fin 3) :=
  {tautClause, properClause₀, properClause₁}

-- `nontautological` drops the tautological clause while retaining both proper clauses.
example : nontautological mixedSet = {properClause₀, properClause₁} := by decide

-- `reduce (nontautological mixedSet)` is both `Reduced` and nontautological.
example :
    Reduced (reduce (nontautological mixedSet)) ∧
      ∀ C ∈ reduce (nontautological mixedSet), ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C :=
  ⟨reduced_reduce (nontautological mixedSet),
    fun _ hC => nontautological_of_mem_reduce_nontautological hC⟩

private def sampleCNF : CNF (Fin 3) :=
  [[(0, true), (0, false), (1, true)], [(0, true), (1, true)], [(0, true), (2, true)]]

-- Concrete satisfaction and model-count checks via `sat_reduce_nontautological_iff` and
-- `modelCountOn_toCNF_reduce_nontautological` (`mixedSet = sampleCNF.toClauseSet` has `5` models on
-- `Fin 3`).
example :
    (reduce (nontautological mixedSet)).Sat (fun _ => true) ∧
      ¬ (reduce (nontautological mixedSet)).Sat (fun _ => false) := by
  rw [sat_reduce_nontautological_iff, sat_reduce_nontautological_iff]
  decide

example :
    (reduce (nontautological mixedSet)).toCNF.modelCountOn (univ : Finset (Fin 3)) = 5 := by
  have hms : mixedSet = sampleCNF.toClauseSet := by decide
  rw [modelCountOn_toCNF_reduce_nontautological, hms, modelCountOn_toCNF_toClauseSet]
  decide

/-! ### 2. Branch-word representation bridge and `length_countingLeaves_pow_le` -/

private def flower2 : ClauseSet (Fin 3) :=
  {properClause₀, properClause₁}

-- At M = 2, the heart `{(0, true)}` is heavy in `flower2` (`2 ^ (2 - 1) = 2 ≤ 2`), so `flower2`
-- is not `(2 ^ ·)`-sparse.
example : Heavy (2 ^ ·) flower2 2 {(0, true)} ∧ ¬ Sparse (2 ^ ·) flower2 := by
  refine ⟨⟨by decide, by decide, by decide⟩, fun hs => ?_⟩
  exact hs 2 {(0, true)} ⟨by decide, by decide, by decide⟩

-- Concrete check of the representation bridge (`countingTreeRule`, `countingLeafWords`,
-- `countingLeaves_eq_map_walk_countingLeafWords`, `nodup_countingLeafWords`,
-- `mem_countingLeafWords_iff_isLeafWord`) on `flower2`.
example :
    countingLeaves (2 ^ ·) flower2 =
      (countingLeafWords (2 ^ ·) flower2).map ((countingTreeRule (2 ^ ·)).walk flower2) ∧
    (countingLeafWords (2 ^ ·) flower2).Nodup ∧
    (∀ w, w ∈ countingLeafWords (2 ^ ·) flower2 ↔
      (countingTreeRule (2 ^ ·)).IsLeafWord flower2 w) := by
  have hθ : ∀ j, 1 ≤ j → 2 ≤ 2 ^ j := fun j hj =>
    by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hj
  exact ⟨countingLeaves_eq_map_walk_countingLeafWords (2 ^ ·) flower2,
    nodup_countingLeafWords (2 ^ ·) flower2,
    mem_countingLeafWords_iff_isLeafWord hθ flower2⟩

-- Concrete upper bound from `length_countingLeaves_pow_le` on `flower2` (`n = 3, k = 2, M = 2`,
-- where `countingDepthCoeff 2 2 * 3 = 12` and `countingBChoiceCoeff 2 * 3 / 2 = 6`).
example :
    (countingLeaves (2 ^ ·) flower2).length ≤ ∑ j ∈ range 7, Nat.choose 12 j := by
  simpa [countingBChoiceCoeff, countingDepthCoeff] using
    length_countingLeaves_pow_le (k := 2) (M := 2) (by decide) (by unfold Reduced; decide)
      (by decide) (by decide) (univ : Finset (Fin 3))
      (fun _ _ _ _ => mem_univ _)

-- Check concrete numerical leaf bounds (`nontautological`, `occurrences ≤ 6`, `card ≤ 19`,
-- `toCNF.length ≤ 19`) on `flower2`.
example : ∀ L ∈ countingLeaves (2 ^ ·) flower2,
    (∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) ∧
      (∀ v : Fin 3, L.occurrences v ≤ 6) ∧
      L.card ≤ 19 ∧
      L.toCNF.length ≤ 19 := by
  have hθ : ∀ j, 1 ≤ j → 2 ≤ 2 ^ j := fun j hj =>
    by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have hθ1 : ∀ r, 1 ≤ 2 ^ r := fun r => Nat.one_le_pow r 2 (by decide)
  have hnt : ∀ C ∈ flower2, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by decide
  have hk : ∀ C ∈ flower2, C.card ≤ 2 := by decide
  have hsup : ∀ C ∈ flower2, ∀ l ∈ C, l.1 ∈ (univ : Finset (Fin 3)) :=
    fun _ _ _ _ => mem_univ _
  intro L hL
  refine ⟨nontautological_of_mem_countingLeaves hθ1 hnt hL,
    fun v => (occurrences_le_of_mem_countingLeaves hθ (hθ1 0) hk hL v).trans (by decide),
    (card_le_of_mem_countingLeaves_of_support hθ (hθ1 0) hk hsup hL).trans (by decide),
    (length_toCNF_le_of_mem_countingLeaves_of_support hθ (hθ1 0) hk hsup hL).trans (by decide)⟩

/-! ### 3. Parameter-budget and width-1 / width-0 boundary checks -/

-- Explicit budget witness for `length_countingLeaves_pow_le_two_pow_of_budget` at `k = 2, B = 1,
-- M = 512`: `countingBChoiceCoeff 2 = 4 ≤ 512` and `countingDepthCoeff 2 512 = 4`, so
-- `1 * 4 * Nat.clog 2 (4 * 4 * 512) = 4 * 13 = 52 ≤ 512`.
example :
    (countingLeaves (512 ^ ·) flower2).length ≤ 16 :=
  length_countingLeaves_pow_le_two_pow_of_budget (k := 2) (M := 512) (B := 1)
    (by decide) (by decide) (fun _ => ⟨by decide, by decide⟩)
    (by unfold Reduced; decide) (by decide) (by decide)
    (univ : Finset (Fin 3)) (fun _ _ _ _ => mem_univ _) (n := 3) (by decide)

-- At width `k = 1`, `length_countingLeaves_pow_le` forces length `≤ 1`,
-- which with `countingLeaves_ne_nil` proves `(countingLeaves (2 ^ ·) unitRoot).length = 1`.
def unitRoot : ClauseSet (Fin 2) :=
  {{(0, true)}, {(1, false)}}

theorem unitRoot_length_countingLeaves_eq_one : (countingLeaves (2 ^ ·) unitRoot).length = 1 := by
  have hle : (countingLeaves (2 ^ ·) unitRoot).length ≤ 1 := by
    simpa [countingBChoiceCoeff, countingDepthCoeff] using
      length_countingLeaves_pow_le (k := 1) (M := 2) (by decide) (by unfold Reduced; decide)
        (by decide) (by decide) (univ : Finset (Fin 2))
        (fun _ _ _ _ => mem_univ _)
  have hpos : 0 < (countingLeaves (2 ^ ·) unitRoot).length :=
    List.length_pos_iff.mpr (countingLeaves_ne_nil (2 ^ ·) unitRoot)
  omega

/-! ### 4. Unconditional CNF counting-sparsification corollaries -/

example :
    ((countingLeaves (2 ^ ·) (reduce (nontautological sampleCNF.toClauseSet))).map
        ClauseSet.toCNF).countP (fun F => F.eval (fun _ => true)) = 1 ∧
      ((countingLeaves (2 ^ ·) (reduce (nontautological sampleCNF.toClauseSet))).map
        ClauseSet.toCNF).countP (fun F => F.eval (fun _ => false)) = 0 := by
  rw [countP_eval_toCNF_countingLeaves_nontautological,
    countP_eval_toCNF_countingLeaves_nontautological]
  decide

example :
    ((countingLeaves (2 ^ ·) (reduce (nontautological sampleCNF.toClauseSet))).map
        fun L => L.toCNF.modelCountOn (univ : Finset (Fin 3))).sum = 5 := by
  rw [sum_modelCountOn_countingLeaves_nontautological (2 ^ ·) sampleCNF univ]
  decide

example :
    1 ≤ (countingLeaves (fun j => (countingThresholdBase 3 2) ^ j)
        (reduce (nontautological sampleCNF.toClauseSet))).length ∧
      (countingLeaves (fun j => (countingThresholdBase 3 2) ^ j)
        (reduce (nontautological sampleCNF.toClauseSet))).length ≤ 4 :=
  ⟨List.length_pos_iff.mpr (countingLeaves_ne_nil _ _),
    length_countingLeaves_nontautological_thresholdBase_le (k := 3) (B := 2) (by decide)
      sampleCNF (by decide) (univ : Finset (Fin 3)) (fun _ _ => mem_univ _) (n := 3) (by decide)⟩

example :
    let θ := fun j => (countingThresholdBase 3 2) ^ j
    let ψ₀ := reduce (nontautological sampleCNF.toClauseSet)
    ((countingLeaves θ ψ₀).map fun L => L.toCNF.modelCountOn (univ : Finset (Fin 3))).sum = 5 ∧
      (countingLeaves θ ψ₀).length ≤ 4 ∧
      ∀ L ∈ countingLeaves θ ψ₀,
        Sparse θ L ∧ Reduced L ∧
          (∀ C ∈ L, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C) ∧
          (∀ C ∈ L, C.card ≤ 3) := by
  intro θ ψ₀
  obtain ⟨hsum, -, hlen, hleaves⟩ :=
    countingLeaves_nontautological_thresholdBase_spec (k := 3) (B := 2) (by decide)
      sampleCNF (by decide) (univ : Finset (Fin 3)) (fun _ _ => mem_univ _) (n := 3) (by decide)
  have hmc : sampleCNF.modelCountOn (univ : Finset (Fin 3)) = 5 := by decide
  refine ⟨hsum.trans hmc, hlen, fun L hL => ?_⟩
  obtain ⟨hs, hr, hnt, hk, -⟩ := hleaves L hL
  exact ⟨hs, hr, hnt, hk⟩

end ComplexityTests.SparsificationCountingTreeBounds
