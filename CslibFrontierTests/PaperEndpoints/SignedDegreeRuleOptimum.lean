/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.SignedDegreePartitionOptimum
public import CslibFrontier.Computability.Complexity.FineGrained.SignedSigmaRho
public import CslibFrontierTests.PaperEndpoints.DegreeRuleOptimum
meta import CslibFrontier.Computability.Complexity.FineGrained.SignedDegreePartition
meta import CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval
meta import CslibFrontierTests.PaperEndpoints.DegreeRuleOptimum

/-! # Signed extrema: actual normalization, distribution, scans and scalar reconstruction -/

public section
open Cslib.Logic.PL
set_option linter.hashCommand false

/-- info: ((some ([0, 2], 1), some ([2, 0], 1)),
 (some ([1, 1], 2), some ([1, 1], 2)), (none, none),
 some ([0, 0], 1), some ([0, 0], 1)) -/
#guard_msgs (whitespace := lax) in
#eval (DegreeRuleOptimumTests.run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (DegreePartition.Signed.normalize (boundedPartitionEdge, [(-2, 2 ^ 512), (-1, 2)])),
  DegreeRuleOptimumTests.run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (DegreePartition.Signed.normalize (boundedPartitionEdge, [(1, 1), (-1, 2)])),
  DegreeRuleOptimumTests.run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (DegreePartition.Signed.normalize (boundedPartitionEdge, [(-3, -1), (0, 2)])),
  DegreeRuleOptimumTests.run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (DegreePartition.Signed.normalize ((0, []), [(-2, 0), (-1, 2 ^ 512)])))

/-- info: ((some 1, some 2), (some 2, some 2), (none, none), some 0, some 0) -/
#guard_msgs (whitespace := lax) in
#eval (DegreeRuleOptimumTests.sets (fun k => k.val == 0) (fun k => k.val == 1)
    (IndependentDominationInterval.Signed.normalize (degreeRulePath, -3, 2 ^ 512)),
  DegreeRuleOptimumTests.sets (fun k => k.val == 0) (fun k => k.val == 1)
    (IndependentDominationInterval.Signed.normalize (degreeRulePath, 2, 2 ^ 512)),
  DegreeRuleOptimumTests.sets (fun _ => true) (fun _ => true)
    (IndependentDominationInterval.Signed.normalize (boundedPartitionEdge, -3, -1)),
  DegreeRuleOptimumTests.sets (fun _ => false) (fun _ => false)
    (IndependentDominationInterval.Signed.normalize ((0, []), -(2 ^ 512), 0)))

/- Formal transport preserves the impossibility of a negative upper bound. -/
example {n q : ℕ} (G : SimpleGraph (Fin n)) (M : Fin q → Fin q → Set ℕ)
    (lo hi : Fin q → ℤ) (j : Fin q) (hj : hi j < 0) (S : Fin q → Set (Fin n)) :
    ¬ DegreePartition.Signed.Optimum.Feasible G M lo hi S := by
  intro h
  have hh := (h.2 j).2
  have hn : (0 : ℤ) ≤ Nat.card (S j) := Int.natCast_nonneg _
  omega

open Classical in
example : ∃ opt : DegreePartition.Signed.Input → DegreePartition.Optimum.Result,
    ∃ cs : Cslib.GenericRAM.NativeCertificate opt DegreePartition.Signed.encInput
      DegreePartition.Optimum.encResult, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((DegreePartition.Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin 3 → ℤ),
        DegreePartition.Signed.Optimum.Optimal G (fun _ _ => Set.univ) lo hi 1
          (opt (DegreePartition.Signed.ofGraph G lo hi)) ∧
        (16 ≤ n → (cs.time (DegreePartition.Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((DegreePartition.Signed.encInput (DegreePartition.Signed.ofGraph G lo hi)).length + 1 :
            ℕ) ^ e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DegreePartition.Signed.Optimum.exists_optimal_finiteCofinite_certificate
    (fun _ _ => Set.univ) (by intro _ _; simp) 1
