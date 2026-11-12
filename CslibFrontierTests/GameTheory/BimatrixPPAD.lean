/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Bimatrix.PPAD
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PPADS
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Bimatrix Nash equilibrium in `PPAD`

Kernel-checked tests for `CslibFrontier/GameTheory/Bimatrix/PPAD.lean`:

* Concrete well-formed `2 × 2` coordination, matching-pennies, `3 × 2` von Stengel (3.3), and
  degenerate zero-payoff games: valid rational Nash witnesses (`BimatrixCode.IsRationalNash` and
  `BimatrixCode.BimatrixNash`) as well as non-Nash strategy pairs and negative-probability vectors.
* Malformed, zero-dimension, and non-rectangular codes accept only `[]`.
* Direct kernel check of the `Turing.MultiTapeTM.encRat`, `StrategyPair`, and `encWitness`
  encodings and witness length bounds.
* `BimatrixNash.isNash`, `extractNash_sound`, `BimatrixNash_mem_PPAD`, `BimatrixNash_mem_TFNP`,
  `BimatrixNash_isTotalSearch`, `BimatrixNash_searchReducible_endOfLineRel`,
  `BimatrixNash_searchReducible_EndOfLine`, and strict `module` axiom checks.
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.BimatrixPPAD

open Cslib Cslib.Complexity Cslib.GameTheory Cslib.GameTheory.BimatrixCode Turing.MultiTapeTM

/-! ### Concrete games and malformed inputs -/

/-- `2 × 2` coordination game. -/
def coordCode : BimatrixCode := ⟨[[1, 0], [0, 1]], [[1, 0], [0, 1]]⟩

/-- `2 × 2` matching pennies (unique mixed equilibrium `(1/2, 1/2)`). -/
def penniesCode : BimatrixCode := ⟨[[1, -1], [-1, 1]], [[-1, 1], [1, -1]]⟩

/-- `3 × 2` game (3.3) of [vonStengel2007] with equilibrium `((4/5, 1/5, 0), (2/3, 1/3))`. -/
def stengelCode : BimatrixCode := ⟨[[3, 3], [2, 5], [0, 6]], [[3, 2], [2, 6], [3, 1]]⟩

/-- Degenerate `2 × 2` zero game where every pair of mixed strategies is a Nash equilibrium. -/
def zeroCode : BimatrixCode := ⟨[[0, 0], [0, 0]], [[0, 0], [0, 0]]⟩

/-- Empty `0 × 0` code (malformed). -/
def emptyCode : BimatrixCode := ⟨[], []⟩

/-- Non-rectangular code (malformed). -/
def nonRectCode : BimatrixCode := ⟨[[1, 0], [0]], [[1, 0], [0, 1]]⟩

/-- Mismatched row-count code (malformed). -/
def mismatchCode : BimatrixCode := ⟨[[1, 0]], [[1, 0], [0, 1]]⟩

example : coordCode.WellFormed ∧ coordCode.wellFormedB = true ∧ coordCode.vertexLen = 8 :=
  ⟨(wellFormed_iff_wellFormedB coordCode).2 (by decide), by decide, by decide⟩

example : stengelCode.rows = 3 ∧ stengelCode.cols = 2 ∧ stengelCode.vertexLen = 10 :=
  ⟨by decide, by decide, by decide⟩

example : emptyCode.wellFormedB = false ∧ ¬emptyCode.WellFormed ∧ emptyCode.vertexLen = 0 :=
  ⟨by decide, fun h => by have := (wellFormed_iff_wellFormedB emptyCode).1 h; contradiction,
    by decide⟩

example : nonRectCode.wellFormedB = false ∧ ¬nonRectCode.WellFormed ∧
    mismatchCode.wellFormedB = false ∧ ¬mismatchCode.WellFormed := by
  refine ⟨by decide, fun h => ?_, by decide, fun h => ?_⟩
  · have := (wellFormed_iff_wellFormedB nonRectCode).1 h; contradiction
  · have := (wellFormed_iff_wellFormedB mismatchCode).1 h; contradiction

/-! ### Encoding opacity and witness-length checks -/

example : (encRat (-1 : ℚ)).length = 6 := by
  rw [Turing.MultiTapeTM.length_encRat]
  have h1 : (-1 : ℚ).num = -1 ∧ (-1 : ℚ).den = 1 := by norm_num
  rw [h1.1, h1.2]
  decide

example : (encRat (4 / 5 : ℚ)).length = 12 := by
  rw [Turing.MultiTapeTM.length_encRat]
  have h45 : (4 / 5 : ℚ).num = 4 ∧ (4 / 5 : ℚ).den = 5 := by norm_num
  rw [h45.1, h45.2]
  decide

private lemma witness_len_le_of_entry_le {c : BimatrixCode} {x y : List ℚ} {K : ℕ}
    (hx_len : x.length ≤ 3) (hy_len : y.length ≤ 3)
    (hx : ∀ q ∈ x, (encRat q).length ≤ K) (hy : ∀ q ∈ y, (encRat q).length ≤ K)
    (hK : 2 * (3 * (2 * K + 1)) + 1 + 3 * (2 * K + 1) ≤ 500) :
    (encWitness ⟨x, y⟩).length ≤
      120 * (encBimatrix c).length ^ 3 + 400 * (encBimatrix c).length + 100 := by
  have hx' := length_encList_le encRat x hx
  have hy' := length_encList_le encRat y hy
  have hxm : (encList encRat x).length ≤ 3 * (2 * K + 1) :=
    hx'.trans (Nat.mul_le_mul_right _ hx_len)
  have hym : (encList encRat y).length ≤ 3 * (2 * K + 1) :=
    hy'.trans (Nat.mul_le_mul_right _ hy_len)
  have hL : 1 ≤ (encBimatrix c).length := by
    rw [encBimatrix_apply, length_encPair]
    omega
  rw [encWitness_apply, length_encPair]
  dsimp only
  omega

private lemma encRat_length_le_sixteen {q : ℚ} (hn : q.num.natAbs ≤ 10) (hd : q.den ≤ 10) :
    (encRat q).length ≤ 16 := by
  rw [Turing.MultiTapeTM.length_encRat]
  have h1 : q.num.natAbs.size ≤ 4 := Nat.size_le.2 (by omega)
  have h2 : q.den.size ≤ 4 := Nat.size_le.2 (by omega)
  omega

example : (encWitness ⟨[1 / 2, 1 / 2], [1 / 2, 1 / 2]⟩).length ≤
    120 * (encBimatrix coordCode).length ^ 3 + 400 * (encBimatrix coordCode).length + 100 := by
  refine witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide) <;>
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num

example : 4 ≤ (encRat (0 : ℚ)).length ∧ 18 ≤ (encList encRat [1 / 2, 1 / 2]).length := by
  refine ⟨Turing.MultiTapeTM.four_le_length_encRat 0, ?_⟩
  have h := length_encList_ge_mul encRat [1 / 2, 1 / 2] 4 fun q _ =>
    Turing.MultiTapeTM.four_le_length_encRat q
  exact Nat.le_trans (by decide) h

/-! ### Valid and invalid rational Nash witnesses -/

/-- Pure equilibrium `([1, 0], [1, 0])` of the `2 × 2` coordination game. -/
theorem coordCode_pure_isRationalNash : coordCode.IsRationalNash [1, 0] [1, 0] := by
  refine ⟨by decide, by decide, ?_, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro i
    change (∑ j : Fin 2, coordCode.toMatA i j * [1, 0].getD j.1 0) ≤
      ∑ a : Fin 2, ∑ j : Fin 2, [1, 0].getD a.1 0 * coordCode.toMatA a j * [1, 0].getD j.1 0
    fin_cases i <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatA, coordCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num
  · intro j
    change (∑ i : Fin 2, [1, 0].getD i.1 0 * coordCode.toMatB i j) ≤
      ∑ i : Fin 2, ∑ b : Fin 2, [1, 0].getD i.1 0 * coordCode.toMatB i b * [1, 0].getD b.1 0
    fin_cases j <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatB, coordCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num

example : coordCode.BimatrixNash (encWitness ⟨[1, 0], [1, 0]⟩) := by
  have hw : coordCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  refine ⟨witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide),
    ⟨[1, 0], [1, 0]⟩, rfl, coordCode_pure_isRationalNash⟩ <;>
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num

/-- `BimatrixNash.isNash` bridges concrete `BimatrixCode` witnesses to `BimatrixGame.IsNash`. -/
example : ∃ s : StrategyPair,
    encWitness ⟨[1, 0], [1, 0]⟩ = encWitness s ∧
    coordCode.toGame.IsNash (fun i : Fin coordCode.rows => (s.x.getD i.1 0 : ℝ))
      (fun j : Fin coordCode.cols => (s.y.getD j.1 0 : ℝ)) :=
  BimatrixNash.isNash ((wellFormed_iff_wellFormedB coordCode).2 (by decide)) <| by
    have hw : coordCode.wellFormedB = true := by decide
    simp only [BimatrixNash, hw, ite_true]
    refine ⟨witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide),
      ⟨[1, 0], [1, 0]⟩, rfl, coordCode_pure_isRationalNash⟩ <;>
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num

/-- Uniform mixed equilibrium `([1/2, 1/2], [1/2, 1/2])` of matching pennies. -/
theorem penniesCode_uniform_isRationalNash :
    penniesCode.IsRationalNash [1 / 2, 1 / 2] [1 / 2, 1 / 2] := by
  refine ⟨by decide, by decide, ?_, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro i
    change (∑ j : Fin 2, penniesCode.toMatA i j * [1 / 2, 1 / 2].getD j.1 0) ≤
      ∑ a : Fin 2, ∑ j : Fin 2,
        [1 / 2, 1 / 2].getD a.1 0 * penniesCode.toMatA a j * [1 / 2, 1 / 2].getD j.1 0
    fin_cases i <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatA, penniesCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num
  · intro j
    change (∑ i : Fin 2, [1 / 2, 1 / 2].getD i.1 0 * penniesCode.toMatB i j) ≤
      ∑ i : Fin 2, ∑ b : Fin 2,
        [1 / 2, 1 / 2].getD i.1 0 * penniesCode.toMatB i b * [1 / 2, 1 / 2].getD b.1 0
    fin_cases j <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatB, penniesCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num

example : penniesCode.BimatrixNash (encWitness ⟨[1 / 2, 1 / 2], [1 / 2, 1 / 2]⟩) := by
  have hw : penniesCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  refine ⟨witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide),
    ⟨[1 / 2, 1 / 2], [1 / 2, 1 / 2]⟩, rfl, penniesCode_uniform_isRationalNash⟩ <;>
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num

/-- Pure pair `([1, 0], [1, 0])` is NOT a Nash equilibrium of matching pennies. -/
example : ¬penniesCode.BimatrixNash (encWitness ⟨[1, 0], [1, 0]⟩) := by
  have hw : penniesCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  rintro ⟨_, ⟨x, y⟩, hxy, hrat⟩
  rcases StrategyPair.ext_iff.1 (encWitness.injective hxy) with ⟨hx, hy⟩
  dsimp only at hx hy
  subst hx hy
  have h2 := hrat.2.2.2.2.2.2.2 ⟨1, by decide⟩
  change (∑ i : Fin 2, [1, 0].getD i.1 0 * penniesCode.toMatB i ⟨1, by decide⟩) ≤
    ∑ i : Fin 2, ∑ b : Fin 2,
      [1, 0].getD i.1 0 * penniesCode.toMatB i b * [1, 0].getD b.1 0 at h2
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatB, penniesCode,
    List.getD_cons_zero, List.getD_cons_succ] at h2
  norm_num at h2

/-- Mixed equilibrium `([4/5, 1/5, 0], [2/3, 1/3])` of von Stengel's `3 × 2` game (3.3). -/
theorem stengelCode_mixed_isRationalNash :
    stengelCode.IsRationalNash [4 / 5, 1 / 5, 0] [2 / 3, 1 / 3] := by
  refine ⟨by decide, by decide, ?_, by norm_num, ?_, by norm_num, ?_, ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro i
    change (∑ j : Fin 2, stengelCode.toMatA i j * [2 / 3, 1 / 3].getD j.1 0) ≤
      ∑ a : Fin 3, ∑ j : Fin 2,
        [4 / 5, 1 / 5, 0].getD a.1 0 * stengelCode.toMatA a j * [2 / 3, 1 / 3].getD j.1 0
    fin_cases i <;>
      · simp only [Fin.sum_univ_two, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
          toMatA, stengelCode, List.getD_cons_zero, List.getD_cons_succ]
        norm_num
  · intro j
    change (∑ i : Fin 3, [4 / 5, 1 / 5, 0].getD i.1 0 * stengelCode.toMatB i j) ≤
      ∑ i : Fin 3, ∑ b : Fin 2,
        [4 / 5, 1 / 5, 0].getD i.1 0 * stengelCode.toMatB i b * [2 / 3, 1 / 3].getD b.1 0
    fin_cases j <;>
      · simp only [Fin.sum_univ_two, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
          toMatB, stengelCode, List.getD_cons_zero, List.getD_cons_succ]
        norm_num

example : stengelCode.BimatrixNash (encWitness ⟨[4 / 5, 1 / 5, 0], [2 / 3, 1 / 3]⟩) := by
  have hw : stengelCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  refine ⟨witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide),
    ⟨[4 / 5, 1 / 5, 0], [2 / 3, 1 / 3]⟩, rfl, stengelCode_mixed_isRationalNash⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num

/-- Degenerate `2 × 2` zero game admits mixed rational equilibria. -/
example : zeroCode.BimatrixNash (encWitness ⟨[1 / 3, 2 / 3], [1 / 4, 3 / 4]⟩) := by
  have hw : zeroCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  refine ⟨witness_len_le_of_entry_le (K := 16) (by decide) (by decide) ?_ ?_ (by decide),
    ⟨[1 / 3, 2 / 3], [1 / 4, 3 / 4]⟩, rfl,
    ⟨by decide, by decide, ?_, by norm_num, ?_, by norm_num, ?_, ?_⟩⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> apply encRat_length_le_sixteen <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro i
    change (∑ j : Fin 2, zeroCode.toMatA i j * [1 / 4, 3 / 4].getD j.1 0) ≤
      ∑ a : Fin 2, ∑ j : Fin 2,
        [1 / 3, 2 / 3].getD a.1 0 * zeroCode.toMatA a j * [1 / 4, 3 / 4].getD j.1 0
    fin_cases i <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatA, zeroCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num
  · intro j
    change (∑ i : Fin 2, [1 / 3, 2 / 3].getD i.1 0 * zeroCode.toMatB i j) ≤
      ∑ i : Fin 2, ∑ b : Fin 2,
        [1 / 3, 2 / 3].getD i.1 0 * zeroCode.toMatB i b * [1 / 4, 3 / 4].getD b.1 0
    fin_cases j <;>
      · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, toMatB, zeroCode,
          List.getD_cons_zero, List.getD_cons_succ]
        norm_num

/-- Negative entries summing to `1` are rejected by `IsRationalNash` / `BimatrixNash`. -/
example : ¬coordCode.BimatrixNash (encWitness ⟨[2, -1], [1, 0]⟩) := by
  have hw : coordCode.wellFormedB = true := by decide
  simp only [BimatrixNash, hw, ite_true]
  rintro ⟨_, ⟨x, y⟩, hxy, hrat⟩
  obtain ⟨rfl, rfl⟩ := StrategyPair.ext_iff.1 (encWitness.injective hxy)
  have hneg := hrat.2.2.1 (-1) (by decide)
  norm_num at hneg

/-- Empty witness `[]` is rejected on well-formed games and uniquely accepted on malformed ones. -/
example : ¬coordCode.BimatrixNash [] ∧ emptyCode.BimatrixNash [] ∧ ¬emptyCode.BimatrixNash [false] ∧
    nonRectCode.BimatrixNash [] ∧ mismatchCode.BimatrixNash [] := by
  have hcw : coordCode.wellFormedB = true := by decide
  have hew : emptyCode.wellFormedB = false := by decide
  have hnw : nonRectCode.wellFormedB = false := by decide
  have hmw : mismatchCode.wellFormedB = false := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [BimatrixNash, hcw, ite_true]
    rintro ⟨_, s, hxy, _⟩
    have hnil : (encPair (encList encRat) (encList encRat) (s.x, s.y)).length =
        ([] : List Bool).length := by
      rw [← encWitness_apply]
      exact congrArg List.length hxy.symm
    have hpos := length_encPair (s.x, s.y) (enc₁ := encList encRat) (enc₂ := encList encRat)
    simp only [List.length_nil] at hnil
    omega
  · simp only [BimatrixNash, hew, Bool.false_eq_true, ite_false]
  · simp only [BimatrixNash, hew, Bool.false_eq_true, ite_false]
    decide
  · simp only [BimatrixNash, hnw, Bool.false_eq_true, ite_false]
  · simp only [BimatrixNash, hmw, Bool.false_eq_true, ite_false]

/-! ### `PPAD`, `TFNP`, totality, and `EndOfLine` reductions -/

example : BimatrixNash ∈ PPAD encBimatrix := BimatrixNash_mem_PPAD

example : BimatrixNash ∈ TFNP encBimatrix := BimatrixNash_mem_TFNP

example : searchDomain BimatrixNash = Set.univ :=
  isTotalSearch_iff_searchDomain_eq_univ.1 BimatrixNash_isTotalSearch

example : BimatrixNash ∈ PPP encBimatrix := PPAD_subset_PPP BimatrixNash_mem_PPAD

example : BimatrixNash ∈ PPA encBimatrix := PPAD_subset_PPA BimatrixNash_mem_PPAD

example : SearchReducible encBimatrix encBimatrix BimatrixNash
    (endOfLineRel vertexLen pred succ) :=
  BimatrixNash_searchReducible_endOfLineRel

example : SearchReducible encBimatrix encEndOfLine BimatrixNash EndOfLine :=
  BimatrixNash_searchReducible_EndOfLine

/-- Every end-of-line witness of `coordCode` extracts via `extractNash` to a genuine Nash
equilibrium of `coordCode.toGame`. -/
example (u : List Bool) (hu : endOfLineRel vertexLen pred succ coordCode u) :
    ∃ s : StrategyPair, extractNash (coordCode, u) = encWitness s ∧
      coordCode.toGame.IsNash (fun i : Fin coordCode.rows => (s.x.getD i.1 0 : ℝ))
        (fun j : Fin coordCode.cols => (s.y.getD j.1 0 : ℝ)) :=
  BimatrixNash.isNash ((wellFormed_iff_wellFormedB coordCode).2 (by decide))
    (extractNash_sound hu)

/-! ### Strict `module` axiom checks -/

/--
info: 'Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_PPAD' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BimatrixNash_mem_PPAD

/--
info: 'Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_TFNP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BimatrixNash_mem_TFNP

/--
info: 'Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_EndOfLine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BimatrixNash_searchReducible_EndOfLine

/--
info: 'Cslib.GameTheory.BimatrixCode.extractNash_sound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms extractNash_sound

end CslibFrontierTests.GameTheory.BimatrixPPAD

end
