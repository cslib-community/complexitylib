/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.SigmaRhoOptimum
public import CslibFrontierTests.PaperEndpoints.BoundedDegreePartition
meta import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionDistribution
meta import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionOptimum
meta import CslibFrontier.Computability.Complexity.FineGrained.SigmaRhoOptimum
meta import CslibFrontierTests.PaperEndpoints.BoundedDegreePartition

/-!
# Computed attained degree-rule and labeled-partition extrema

The production traversal/selection is tested with the tiny original-label oracle from the
bounded-partition clients. No auxiliary cube is enumerated. Native interfaces below instantiate
the actual sharp counter and do not take this test oracle as a premise.
-/

public section

namespace DegreeRuleOptimumTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM DegreePartition

set_option linter.hashCommand false

/-- Tiny pipeline: real grid, binary equality requests, original-label oracle and scans. -/
@[expose] def run {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (i : ℕ)
    (x : Bounded.BinaryFrontend.Input) : Optimum.Result :=
  Optimum.select q i (x, Distribution.run q (boundedPartitionTestCount M)
    (Bounded.BinaryFrontend.original x))

/- Independent labels are retained; both interval filtering and the chosen objective matter. -/
/-- info: ((some ([0, 0, 2], 1), some ([2, 0, 0], 1)),
 (some ([0, 0, 2], 1), some ([0, 2, 0], 1)),
 (some ([0, 1, 1], 2), some ([1, 1, 0], 2)), none, none) -/
#guard_msgs (whitespace := lax) in
#eval (run (q := 3) (D := 1) (fun _ _ _ => true) 0
    (boundedPartitionEdge, [(0, 2), (0, 2), (0, 2)]),
  run (q := 3) (D := 1) (fun _ _ _ => true) 1
    (boundedPartitionEdge, [(0, 2), (0, 2), (0, 2)]),
  run (q := 3) (D := 1) (fun _ _ _ => true) 0
    (boundedPartitionEdge, [(0, 2), (1, 2), (0, 2)]),
  run (q := 3) (D := 1) (fun _ _ _ => true) 0
    (boundedPartitionEdge, [(1, 2), (1, 2), (1, 2)]))

/- Original multiplicities are retained, not quotiented by permutations or replaced by booleans. -/
/-- info: ((some ([1, 1], 2), some ([1, 1], 2)),
 (some ([1, 1], 2), some ([1, 1], 2)), none, none) -/
#guard_msgs (whitespace := lax) in
#eval (run (q := 2) (D := 2) (fun i j s => i == j || s.val == 1) 0
    (boundedPartitionEdge, [(0, 2), (0, 2)]),
  run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (boundedPartitionEdge, [(1, 1), (0, 2 ^ 512)]),
  run (q := 2) (D := 1) (fun _ _ _ => true) 0
    (boundedPartitionEdge, [(2, 1), (0, 2)]))

/- Empty feasible classes/graphs return zero values; missing feasibility returns absence. -/
/-- info: ((some ([0, 0, 0], 1), some ([0, 0, 0], 1)), (none, none), none, none) -/
#guard_msgs (whitespace := lax) in
#eval (run (q := 3) (D := 1) (fun _ _ _ => false) 0
    ((0, []), [(0, 0), (0, 0), (0, 0)]),
  run (q := 3) (D := 1) (fun _ _ _ => true) 0
    ((0, []), [(0, 0), (1, 1), (0, 0)]),
  run (q := 2) (D := 1) (fun _ _ _ => false) 0
    ((1, [[false]]), [(0, 1), (0, 1)]))

/-- Test-only sigma-rho specialization of the real preparation and scalar reconstruction. -/
@[expose] def sets (σ ρ : SimpleGraph.DegreeRule 1)
    (x : SigmaRho.BinaryFrontend.Input) : SigmaRho.Optimum.Result :=
  SigmaRho.Optimum.values (run (q := 2) (D := 1)
    (fun i j k => if j == 0 then if i == 0 then σ k else ρ k else true) 0
      (SigmaRho.Optimum.prepare x))

/- A path has minimum independent-domination size one and maximum size two. -/
/-- info: ((some 1, some 2), (some 2, some 2), (none, none),
 (some 0, some 2), (some 0, some 0), none, none) -/
#guard_msgs (whitespace := lax) in
#eval (sets (fun k => k.val == 0) (fun k => k.val == 1) (degreeRulePath, 0, 3),
  sets (fun k => k.val == 0) (fun k => k.val == 1) (degreeRulePath, 2, 2 ^ 512),
  sets (fun k => k.val == 0) (fun k => k.val == 1) (degreeRulePath, 0, 0),
  sets (fun _ => true) (fun _ => true) (boundedPartitionEdge, 0, 2 ^ 512),
  sets (fun _ => false) (fun _ => false) ((0, []), 0, 0),
  sets (fun _ => false) (fun _ => false) ((1, [[false]]), 0, 1))

/- A formal semantic test derives actual zero optima, rather than restating the exported API. -/
open Classical in
example (G : SimpleGraph (Fin 0)) : SigmaRho.Optimum.Optimal G ∅ ∅ 0 0 (some 0, some 0) := by
  have h : SigmaRho.Optimum.Feasible G ∅ ∅ 0 0 ∅ := by
    refine ⟨fun u => Fin.elim0 u, ?_, ?_⟩ <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact iff_of_false (by decide) (fun hn => hn ⟨∅, h⟩)
  · exact iff_of_false (by decide) (fun hn => hn ⟨∅, h⟩)
  · intro k hk
    have hk0 : k = 0 := Option.some.inj hk.symm
    subst k
    exact ⟨∅, h, by simp, fun _ _ => Nat.zero_le _⟩
  · intro k hk
    have hk0 : k = 0 := Option.some.inj hk.symm
    subst k
    refine ⟨∅, h, by simp, ?_⟩
    intro S _
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin 0)

open Classical in
example : ∃ opt : Bounded.BinaryFrontend.Input → Optimum.Result,
    ∃ cs : NativeCertificate opt Bounded.BinaryFrontend.encInput Optimum.encResult,
      ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((Bounded.BinaryFrontend.encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin 3 → ℕ),
          Optimum.Optimal G (fun _ _ => Set.univ) lo hi 1
            (opt (Bounded.BinaryFrontend.ofGraph G lo hi)) ∧
          (16 ≤ n → (cs.time (Bounded.BinaryFrontend.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
            ((Bounded.BinaryFrontend.encInput (Bounded.BinaryFrontend.ofGraph G lo hi)).length + 1 :
              ℕ) ^ e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  Optimum.exists_optimal_finiteCofinite_certificate (fun _ _ => Set.univ)
    (by intro _ _; simp) 1

end DegreeRuleOptimumTests
