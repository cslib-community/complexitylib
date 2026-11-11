/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss
import Mathlib.Tactic

/-!
# Tests for Bareiss–Jordan rational elimination and polynomial-time certificates

Kernel-checked examples (using `rfl` and `decide`, without `native_decide`) exercising:
1. Full-rank fractional systems (`clearDenoms`, `ratRref`, `ratRank`, `ratSolve`).
2. Rank-deficient `2 × 3` and overdetermined `3 × 2` rational matrices, verifying row bases,
   kernel bases, `IsReducedRowEchelon`, `rationalElim_spec`, `rationalElim_entry_bounds`.
3. Inconsistent linear systems (`ratSolve_spec`), zero matrices, `0`-row/`0`-column edge cases,
   and ragged/malformed tables (`rationalElim_wellFormed`).
4. Direct strict-`module` instantiation of `ComputableInPolyTime` certificates from
   `RationalElimination.lean` and `PolyTime/Rat.lean`.
-/

namespace CslibFrontierTests.BareissElimination

open Cslib.LinearAlgebra Turing.MultiTapeTM

/-! ### 1. Fractional full-rank 2 × 2 showcase -/

private def matFrac2x2 : RatTable :=
  ⟨2, 2, [[mkRat 1 2, mkRat 1 3], [mkRat 1 5, mkRat 1 7]]⟩

example :
    matFrac2x2.entry 0 0 = (1 : ℚ) / 2 ∧
      matFrac2x2.entry 0 1 = (1 : ℚ) / 3 ∧
      matFrac2x2.entry 1 0 = (1 : ℚ) / 5 ∧
      matFrac2x2.entry 1 1 = (1 : ℚ) / 7 := by
  simp only [matFrac2x2, RatTable.entry, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  norm_num

example :
    ratRank matFrac2x2 = 2 ∧
      (ratRref matFrac2x2).rows = [[(1 : ℚ), 0], [0, (1 : ℚ)]] ∧
      ratKernelBasis matFrac2x2 = [] := by
  decide

private def sysFrac2x2 : LinearSystemInput :=
  ⟨matFrac2x2, [mkRat 5 6, mkRat 12 35]⟩

example :
    (ratSolve sysFrac2x2).solution = some [(1 : ℚ), (1 : ℚ)] ∧
      (∀ x : Fin 2 → ℚ,
        matFrac2x2.toMatrix.mulVec x = (fun i => sysFrac2x2.rhs.getD i.val 0) ↔
          x = fun j => ([(1 : ℚ), (1 : ℚ)]).getD j.val 0) := by
  refine ⟨by decide, fun x => ?_⟩
  constructor
  · intro hx
    have h0 : ∑ j : Fin 2, matFrac2x2.toMatrix ⟨0, by decide⟩ j * x j =
        sysFrac2x2.rhs.getD 0 0 := congrFun hx ⟨0, by decide⟩
    have h1 : ∑ j : Fin 2, matFrac2x2.toMatrix ⟨1, by decide⟩ j * x j =
        sysFrac2x2.rhs.getD 1 0 := congrFun hx ⟨1, by decide⟩
    rw [Fin.sum_univ_two] at h0 h1
    simp only [matFrac2x2, sysFrac2x2, RatTable.toMatrix_apply, RatTable.entry,
      Fin.val_zero, Fin.val_one, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at h0 h1
    norm_num at h0 h1
    have hx0 : x 0 = 1 := by linarith
    have hx1 : x 1 = 1 := by linarith
    ext j
    fin_cases j
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
      exact hx0
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      exact hx1
  · rintro rfl
    have hspec := ratSolve_spec sysFrac2x2
    exact (hspec.1 [(1 : ℚ), (1 : ℚ)] (by decide)).2

/-! ### 2. Rank-deficient 2 × 3 rational matrix: RREF, row basis, kernel basis -/

private def matRank1_2x3 : RatTable :=
  ⟨2, 3, [[mkRat 1 2, (1 : ℚ), mkRat 3 2], [mkRat 1 3, mkRat 2 3, (1 : ℚ)]]⟩

example :
    ratRank matRank1_2x3 = 1 ∧
      (ratRref matRank1_2x3).rows = [[(1 : ℚ), (2 : ℚ), (3 : ℚ)], [0, 0, 0]] ∧
      (rationalElim matRank1_2x3).pivotRows = [0] ∧
      (rationalElim matRank1_2x3).pivotCols = [0] ∧
      (rationalElim matRank1_2x3).nonPivotCols = [1, 2] ∧
      ratRowBasis matRank1_2x3 = [[mkRat 1 2, (1 : ℚ), mkRat 3 2]] ∧
      ratKernelBasis matRank1_2x3 = [[(-2 : ℚ), (1 : ℚ), 0], [(-3 : ℚ), 0, (1 : ℚ)]] := by
  decide

example :
    (rationalElim matRank1_2x3).rref.WellFormed ∧
      Matrix.IsReducedRowEchelon (ratRref matRank1_2x3).toMatrix ∧
      (ratRank matRank1_2x3 : ℕ) = matRank1_2x3.toMatrix.rank :=
  ⟨rationalElim_wellFormed matRank1_2x3, ratRref_isReducedRowEchelon matRank1_2x3,
    ratRank_eq matRank1_2x3⟩

example :
    let res := rationalElim matRank1_2x3
    Submodule.span ℚ (Set.range fun idx : Fin res.kernelBasis.length =>
      (fun j : Fin matRank1_2x3.numCols => res.kernelBasis[idx.val].getD j.val 0)) =
      LinearMap.ker matRank1_2x3.toMatrix.mulVecLin := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hker⟩ := rationalElim_spec matRank1_2x3
  exact hker

/-! ### 3. Overdetermined 3 × 2 matrix: skipping dependent middle row -/

private def matOver3x2 : RatTable :=
  ⟨3, 2, [[(1 : ℚ), mkRat 1 2], [(2 : ℚ), (1 : ℚ)], [mkRat 1 3, mkRat 1 2]]⟩

example :
    ratRank matOver3x2 = 2 ∧
      (rationalElim matOver3x2).pivotRows = [0, 2] ∧
      (rationalElim matOver3x2).pivotCols = [0, 1] ∧
      (ratRref matOver3x2).rows = [[(1 : ℚ), 0], [0, (1 : ℚ)], [0, 0]] ∧
      ratRowBasis matOver3x2 = [[(1 : ℚ), mkRat 1 2], [mkRat 1 3, mkRat 1 2]] ∧
      ratKernelBasis matOver3x2 = [] := by
  decide

/-! ### 4. Consistent underdetermined & inconsistent linear systems -/

private def sysUnder2x3 : LinearSystemInput :=
  ⟨matRank1_2x3, [mkRat 5 2, mkRat 5 3]⟩

example :
    (ratSolve sysUnder2x3).solution = some [(5 : ℚ), 0, 0] ∧
      matRank1_2x3.toMatrix.mulVec
          (fun j => ((ratSolve sysUnder2x3).solution.getD []).getD j.val 0) =
        fun i => sysUnder2x3.rhs.getD i.val 0 := by
  refine ⟨by decide, ?_⟩
  have hspec := (ratSolve_spec sysUnder2x3).1 [(5 : ℚ), 0, 0] (by decide)
  have hsol : (ratSolve sysUnder2x3).solution.getD [] = [(5 : ℚ), 0, 0] := by decide
  rw [hsol]
  exact hspec.2

private def sysInconsistent : LinearSystemInput :=
  ⟨⟨2, 2, [[(1 : ℚ), (2 : ℚ)], [(2 : ℚ), (4 : ℚ)]]⟩, [(1 : ℚ), (3 : ℚ)]⟩

example :
    (ratSolve sysInconsistent).solution = none ∧
      ¬ ∃ x : Fin 2 → ℚ,
        sysInconsistent.matrix.toMatrix.mulVec x = fun i => sysInconsistent.rhs.getD i.val 0 :=
  ⟨by decide, (ratSolve_spec sysInconsistent).2.mp (by decide)⟩

/-! ### 5. Edge cases: zero matrices, 0 rows/cols, ragged/malformed tables, entry bounds -/

private def matZero2x3 : RatTable :=
  ⟨2, 3, [[0, 0, 0], [0, 0, 0]]⟩

private def matEmptyRows : RatTable := ⟨0, 3, []⟩
private def matEmptyCols : RatTable := ⟨3, 0, [[], [], []]⟩
private def matRagged : RatTable := ⟨2, 2, [[mkRat 1 2]]⟩

example :
    ratRank matZero2x3 = 0 ∧
      ratRowBasis matZero2x3 = [] ∧
      ratKernelBasis matZero2x3 = [[(1 : ℚ), 0, 0], [0, (1 : ℚ), 0], [0, 0, (1 : ℚ)]] ∧
      ratRank matEmptyRows = 0 ∧
      ratKernelBasis matEmptyRows = [[(1 : ℚ), 0, 0], [0, (1 : ℚ), 0], [0, 0, (1 : ℚ)]] ∧
      ratRank matEmptyCols = 0 ∧
      ratKernelBasis matEmptyCols = [] ∧
      ratRank matRagged = 1 ∧
      (ratRref matRagged).rows = [[(1 : ℚ), 0], [0, 0]] := by
  decide

example :
    (rationalElim matRagged).rref.WellFormed ∧
      (∀ q ∈ (ratRref matFrac2x2).rows.flatten,
        q.num.natAbs ≤ stageEntryBound 2 2 (2 ^ ((2 + 1) * 4)) ∧
        q.den ≤ stageEntryBound 2 2 (2 ^ ((2 + 1) * 4))) := by
  refine ⟨rationalElim_wellFormed matRagged, ?_⟩
  have hbd : ∀ i : Fin matFrac2x2.numRows, ∀ j : Fin matFrac2x2.numCols,
      (matFrac2x2.toMatrix i j).num.natAbs ≤ 2 ^ 4 ∧
      (matFrac2x2.toMatrix i j).den ≤ 2 ^ 4 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  intro q hq
  rw [List.mem_flatten] at hq
  obtain ⟨row, hrow, hq_row⟩ := hq
  exact (rationalElim_entry_bounds matFrac2x2 hbd).1 row hrow q hq_row

/-! ### 6. Strict `module` polynomial-time certificate instantiation -/

example :
    ComputableInPolyTime rationalElim RatTable.enc RationalElimResult.enc ∧
      ComputableInPolyTime ratRref RatTable.enc RatTable.enc ∧
      ComputableInPolyTime ratRank RatTable.enc encUnary ∧
      ComputableInPolyTime ratRowBasis RatTable.enc (encList (encList encRat)) ∧
      ComputableInPolyTime ratKernelBasis RatTable.enc (encList (encList encRat)) ∧
      ComputableInPolyTime ratSolve LinearSystemInput.enc LinearSolveResult.enc :=
  ⟨rationalElim_computableInPolyTime, ratRref_computableInPolyTime, ratRank_computableInPolyTime,
    ratRowBasis_computableInPolyTime, ratKernelBasis_computableInPolyTime,
    ratSolve_computableInPolyTime⟩

example :
    ComputableInPolyTime (fun p : ℚ × ℚ => p.1 + p.2) (encPair encRat encRat) encRat ∧
      ComputableInPolyTime (fun p : ℚ × ℚ => p.1 * p.2) (encPair encRat encRat) encRat ∧
      ComputableInPolyTime (fun p : ℚ × ℚ => p.1 / p.2) (encPair encRat encRat) encRat :=
  ⟨ComputableInPolyTime.rat_add, ComputableInPolyTime.rat_mul, ComputableInPolyTime.rat_div⟩

public section

/-- Exported kernel-checked witness that fractional `ratRank` and `ratSolve` compute cleanly. -/
theorem smoke_fractional_bareiss :
    ratRank ⟨2, 2, [[mkRat 1 2, mkRat 1 3], [mkRat 1 5, mkRat 1 7]]⟩ = 2 ∧
      (ratSolve ⟨⟨2, 2, [[mkRat 1 2, mkRat 1 3], [mkRat 1 5, mkRat 1 7]]⟩,
        [mkRat 5 6, mkRat 12 35]⟩).solution = some [(1 : ℚ), (1 : ℚ)] := by
  decide

end

end CslibFrontierTests.BareissElimination
