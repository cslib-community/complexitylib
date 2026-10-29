/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceExactness

/-! Regression tests for `BoundedIncidenceExactness`. -/

namespace ComplexityTests.BoundedIncidenceExactness

open Cslib Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

/-- Concrete unguarded stage-by-stage Proposition 5.3 branch pipeline at compact parameters
(`Q = 1`, `r = 1`, `A₀ = 0`, `R = 1`) for fast kernel-checked agreement checks against
`HeavyBranchFold.rootCount`. -/
private def tinyExactPipeline (n' : ℕ) (eqs : List (List (List ℕ))) : ℕ :=
  let k' := 1; let Q := 1; let r := 1; let A₀ := 0; let R := 1
  let ℓ := n' + 1; let q := n'; let J := q + 1
  let aug := withNeutralScopesList (eqs.map equationVars) n'
  let sc := BalancedSchedules.constructBalancedSchedules n' aug.length Q r 3
    (scopeIncidencesList n' aug)
  let d := buildReplacementDesignData n' 1 Q r A₀ R aug sc.1 sc.2
  let tbls := buildEqRowTables n' eqs d; let m := d.measurementMatrix.length
  let nodeJets := (List.range Q).map fun (t : ℕ) =>
    let grpEqs := (List.range r).map fun g => groupEquationsAt eqs d.factorGroups tbls t g
    let subCtx : SubsetStepCtx := ((n', r, m), (r * m, 1), (J, ℓ, k'), ((t : ℤ) + 1, d.denom),
      (d.varGroups.getD t [], d.groupMeasurementMatrices.getD t []), grpEqs)
    (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2
  (CommonCountingAccum.recoverOuterJetSumModPowTwo [1] J ℓ
    (((d.denom ^ k') ^ (2 * ℓ - 1)) ^ eqs.length) nodeJets).toNat

/-- Concrete kernel-checked exactness of the stage-by-stage pipeline across empty, contradictory,
linear, parity, and uniquely satisfiable systems, plus negative verification on an infeasible raw
input (`n' = 2 < 16`). -/
example : tinyExactPipeline 1 [] = HeavyBranchFold.rootCount 1 [] ∧
    tinyExactPipeline 1 [[[]]] = HeavyBranchFold.rootCount 1 [[[]]] ∧
    tinyExactPipeline 1 [[[0]]] = HeavyBranchFold.rootCount 1 [[[0]]] := by
  simp only [← countSystemExhaustive_eq_rootCount]
  decide +kernel

example : tinyExactPipeline 2 [[[0], [1]]] = HeavyBranchFold.rootCount 2 [[[0], [1]]] := by
  rw [← countSystemExhaustive_eq_rootCount]
  decide +kernel

example : tinyExactPipeline 2 [[[0], [1]], [[0], []]] =
      HeavyBranchFold.rootCount 2 [[[0], [1]], [[0], []]] ∧
    checkBranchFeasible 0 (2, []) = false ∧
    evalBoundedIncidenceBranch (((2, 0), (1, 1, 2, 1), (2, 2, 1, 1), [])) = 0 ∧
    HeavyBranchFold.rootCount 2 [] = 4 := by
  simp only [← countSystemExhaustive_eq_rootCount]
  decide +kernel

/-- Concrete end-to-end exactness of `guardedBranchSolver` and `countSparsePolySystem`
instantiated with `evalBoundedIncidenceBranch` via `evalBoundedIncidenceBranch_eq_rootCount` on
empty, contradictory, linear, quadratic, and cubic systems. -/
example :
    guardedBranchSolver 0 evalBoundedIncidenceBranch 3 [[[0, 1], []], [[1, 2], []]] = 1 ∧
    countSparsePolySystem 0 0 evalBoundedIncidenceBranch
      (mkPaperSparseInput 3 2 [[[0, 1], []], [[1, 2], []]]) = 1 ∧
    countSparsePolySystem 0 0 evalBoundedIncidenceBranch
      (mkPaperSparseInput 3 3 [[[0, 1, 2], []]]) = 1 ∧
    countSparsePolySystem 0 0 evalBoundedIncidenceBranch (mkPaperSparseInput 3 1 [[[]]]) = 0 ∧
    countSparsePolySystem 0 0 evalBoundedIncidenceBranch (mkPaperSparseInput 3 1 [[[0]]]) = 4 ∧
    countSparsePolySystem 0 0 evalBoundedIncidenceBranch (mkPaperSparseInput 3 0 []) = 8 := by
  have hbr : ∀ n' eqs', checkBranchFeasible 0 (n', eqs') = true →
      evalBoundedIncidenceBranch (prepareBranchEvalInput (n', eqs')) =
        HeavyBranchFold.rootCount n' eqs' :=
    fun _ _ h => evalBoundedIncidenceBranch_eq_rootCount h
  rw [guardedBranchSolver_eq_rootCount hbr, countSparsePolySystem_eq_rootCount hbr,
    countSparsePolySystem_eq_rootCount hbr, countSparsePolySystem_eq_rootCount hbr,
    countSparsePolySystem_eq_rootCount hbr, countSparsePolySystem_eq_rootCount hbr]
  simp only [← countSystemExhaustive_eq_rootCount]
  decide +kernel

/-- Nonvacuous feasible witnesses for `evalBoundedIncidenceBranch_eq_rootCount`: there exists a
concrete dimension `n' ≥ 20` on which both `(n', [])` and the nonlinear quadratic system
`(n', [[[0, 1], []]])` pass `checkBranchFeasible 0` and execute the non-fallback branch evaluator
path with exact root counts matching `HeavyBranchFold.rootCount`. -/
example : ∃ n' : ℕ, 20 ≤ n' ∧
    checkBranchFeasible 0 (n', []) = true ∧
    evalBoundedIncidenceBranch (prepareBranchEvalInput (n', [])) =
      HeavyBranchFold.rootCount n' [] ∧
    checkBranchFeasible 0 (n', [[[0, 1], []]]) = true ∧
    evalBoundedIncidenceBranch (prepareBranchEvalInput (n', [[[0, 1], []]])) =
      HeavyBranchFold.rootCount n' [[[0, 1], []]] := by
  obtain ⟨N₁, hN₁, hth⟩ := exists_threshold_checkBranchFeasible_eq_true 0 (β₀ := 1) le_rfl
  have h20 : 20 ≤ N₁ := (le_max_right 0 20).trans hN₁
  have hlam : 2 ≤ Nat.clog 2 N₁ :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  have hb0 : branchMaxFactorIncidence N₁ [] ≤ 2 := by
    apply Nat.succ_le_succ
    refine (List.max_le_iff (l := _ :: _) (by simp)).mpr ?_
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨Nat.zero_le 1, fun x hx => ?_⟩
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.zero_le 1
  have hfeas0 : checkBranchFeasible 0 (N₁, []) = true :=
    (hth le_rfl (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])
      (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])
      (by rw [pow_one]; omega) (by change 1 ≤ _; rw [pow_one]; omega)).2.2
  have hvars2 : ∀ eq ∈ ([[[0, 1], []]] : List (List (List ℕ))), ∀ m ∈ eq, ∀ v ∈ m, v < 2 :=
    checkVarsLt_eq_true_iff.mp (by decide +kernel)
  have hvars1 : ∀ eq ∈ ([[[0, 1], []]] : List (List (List ℕ))), ∀ m ∈ eq, ∀ v ∈ m, v < N₁ :=
    fun eq heq m hm v hv => (hvars2 eq heq m hm v hv).trans_le (by omega)
  have hb1 : branchMaxFactorIncidence N₁ [[[0, 1], []]] ≤ 2 := by
    apply Nat.succ_le_succ
    refine (List.max_le_iff (l := _ :: _) (by simp)).mpr ?_
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨Nat.zero_le 1, fun x hx => ?_⟩
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    unfold varDegree
    exact List.countP_le_length
  have hw1 : branchMaxFactorWidth N₁ [[[0, 1], []]] = 2 := by
    unfold branchMaxFactorWidth
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [scopeWidthOn_eq_length_equationVars (hvars1 [[0, 1], []] (List.mem_singleton_self _))]
    decide +kernel
  have hfeas1 : checkBranchFeasible 0 (N₁, [[[0, 1], []]]) = true :=
    (hth le_rfl (checkCanonicalSystem_eq_true_iff.mp (by decide +kernel)) hvars1
      (by rw [pow_one]; omega) (by rw [hw1, pow_one]; omega)).2.2
  exact ⟨N₁, h20, hfeas0, evalBoundedIncidenceBranch_eq_rootCount hfeas0,
    hfeas1, evalBoundedIncidenceBranch_eq_rootCount hfeas1⟩

end ComplexityTests.BoundedIncidenceExactness
