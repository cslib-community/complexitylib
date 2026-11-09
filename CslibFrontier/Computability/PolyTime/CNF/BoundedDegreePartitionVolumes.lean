/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.BoundedDegreePartition
public import CslibFrontier.Logics.Propositional.CNF.DegreePartitionVolumes

/-!
# Actual vertex-polynomial bounded-partition query volume

The bound includes all allocated functional padding clauses and all old threshold/matrix clauses.
It is independent of binary bound magnitudes and separate from actual binary runtime certification.
Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
-/

public section

namespace Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend

/-- Every emitted source query has explicit vertex-polynomial clause volume for fixed q,D. -/
theorem query_volume {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ)
    (N : ℕ) (Q : CNF ℕ) (hQ : (N, Q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build M (ofGraph G lo hi)))) :
    Q.length ≤ n * (1 + q ^ 2) + q * D * n * (n + 1) ^ D + q ^ 2 * n * (D + 1) +
      q * (2 + 3808 * (n + 1)) + 2 * (q * D * n * ((n + 1) ^ D + 1)) := by
  classical
  have old := DegreePartition.BinaryFrontend.build_ofGraph G hD M
  have hside := congrArg (fun z => (TwoBoundary.BinaryFrontend.side z).length) old
  simp only [DegreePartition.BinaryFrontend.build, TwoBoundary.BinaryFrontend.side,
    TwoBoundary.BinaryFrontend.ofFinite, CNF.relabel, List.length_map] at hside
  have hconds := congrArg
    (fun z => ((TwoBoundary.BinaryFrontend.conditions z).map List.length).sum) old
  simp only [DegreePartition.BinaryFrontend.build, TwoBoundary.BinaryFrontend.conditions,
    TwoBoundary.BinaryFrontend.ofFinite, List.map_map, CNF.relabel, List.length_map,
    Function.comp_def] at hconds
  have htest (i : Fin q) : (sizeTest D i.val (ofGraph G lo hi)).length ≤
      2 + 3808 * (n + 1) := by
    simp only [sizeTest, CNF.relabel, List.length_map, interval_ofGraph]
    calc
      _ ≤ 2 + 2856 * (n + 1) + PaddedCardinality.capacity n :=
        (PaddedCardinality.bounds n (lo i) (hi i)).1
      _ = _ := by unfold PaddedCardinality.capacity; ring
  have htests : ((List.finRange q).flatMap fun i => sizeTest D i.val (ofGraph G lo hi)).length ≤
      q * (2 + 3808 * (n + 1)) := by
    simp only [List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _i : Fin q, (2 + 3808 * (n + 1)) := Finset.sum_le_sum fun i _ => htest i
      _ = _ := by simp
  have hv := DegreePartition.volumes G hD M
  obtain ⟨B, P, he, hb, hp, _, _⟩ := representation G hD M lo hi
  have hB := congrArg (fun z => (TwoBoundary.BinaryFrontend.side z).length) he
  have hP := congrArg (fun z =>
    ((TwoBoundary.BinaryFrontend.conditions z).map List.length).sum) he
  simp only [build, TwoBoundary.BinaryFrontend.side, TwoBoundary.BinaryFrontend.ofFinite,
    List.length_append, CNF.relabel, List.length_map] at hB
  simp only [build, TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.map_map, CNF.relabel, List.length_map, Function.comp_def] at hP
  have hg : original (ofGraph G lo hi) = IndependentDomination.ofGraph G := rfl
  rw [hg, hside] at hB
  rw [hg, hconds] at hP
  rw [he] at hQ
  have hquery := (TwoBoundary.BinaryFrontend.compile_budget B P hb hp N Q hQ).2.1
  nlinarith

end Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend
