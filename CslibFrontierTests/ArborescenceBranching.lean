/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Arborescence.PolyTime
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for branchings, materialized `O(n³)` solvers, and `P` certificates

Exercises the full `#3526` arborescence and branching stack:

* `Digraph.Branching`: `IsBranching`, `superRootExtend`, `restrictOption`, undirected acyclicity,
  and non-branching counterexamples (in-degree `2` and directed cycles);
* `Arborescence.Table`: `edmondsTableM` and `edmondsOutTableM` exact values, `O(n³)` tick bounds,
  optimality, and infeasibility (`none`);
* `Arborescence.Branching`: `optimumBranching`, `optimumBranchingM`, `minBranching` on mixed
  positive/negative cyclic digraphs, and Edmonds (1967, Section 2) weight-shift reductions
  (`edmonds_shift_weight_branching`, `edmonds_rooted_outArborescence_of_shift`);
* `Arborescence.PolyTime`: list-table solvers (`edmondsList`, `edmondsOutList`,
  `optimumBranchingList`), positive/negative/out-of-bounds threshold deciders, and `P` membership
  (`minArborescenceDec_mem_P`, `minOutArborescenceDec_mem_P`, `maxBranchingDec_mem_P`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ArborescenceBranching

open Cslib.Algorithms.Lean.Arborescence

/-! ### 1. `Digraph.Branching` and super-root bijection -/

private def branchingArcs : List (Fin 4 × Fin 4) := [(0, 1), (0, 2)]

private def B4 : Digraph (Fin 4) where
  Adj u v := (u, v) ∈ branchingArcs

private instance : DecidableRel B4.Adj :=
  fun u v => inferInstanceAs (Decidable ((u, v) ∈ branchingArcs))

private theorem B4_eq_branchingDigraph : B4 = Digraph.branchingDigraph ![0, 0, 0, 3] := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

private theorem B4_isBranching : B4.IsBranching := by
  rw [B4_eq_branchingDigraph, Digraph.isBranching_branchingDigraph_iff]
  intro v
  fin_cases v
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

example : (Finset.univ.filter fun e : Fin 4 × Fin 4 => B4.Adj e.1 e.2).card = 2 := by decide

example : B4.superRootExtend.IsInArborescence none :=
  Digraph.isBranching_iff_isInArborescence_superRootExtend.mp B4_isBranching

example : Digraph.restrictOption B4.superRootExtend = B4 :=
  Digraph.restrictOption_superRootExtend B4

example : (SimpleGraph.fromRel B4.Adj).IsAcyclic := B4_isBranching.toSimpleGraph_isAcyclic

private def inDegTwoDigraph : Digraph (Fin 3) where
  Adj u v := (u, v) ∈ ([(0, 2), (1, 2)] : List (Fin 3 × Fin 3))

example : ¬ inDegTwoDigraph.IsBranching := by
  intro hB
  have h01 : (0 : Fin 3) = 1 :=
    hB.in_unique (show inDegTwoDigraph.Adj 0 2 by simp [inDegTwoDigraph])
      (show inDegTwoDigraph.Adj 1 2 by simp [inDegTwoDigraph])
  exact absurd h01 (by decide)

private def twoCycleDigraph : Digraph (Fin 3) where
  Adj u v := (u, v) ∈ ([(0, 1), (1, 0)] : List (Fin 3 × Fin 3))

example : ¬ twoCycleDigraph.IsBranching := by
  intro hB
  have hwalk : Relation.TransGen twoCycleDigraph.Adj 0 0 :=
    Relation.TransGen.head (show twoCycleDigraph.Adj 0 1 by simp [twoCycleDigraph])
      (Relation.TransGen.single (show twoCycleDigraph.Adj 1 0 by simp [twoCycleDigraph]))
  exact hB.acyclic hwalk

/-! ### 2. `Arborescence.Table`: `edmondsTableM` and `edmondsOutTableM` -/

private def arbArcs : List (Fin 4 × Fin 4) :=
  [(1, 0), (2, 0), (1, 2), (2, 1), (3, 1), (2, 3), (3, 2)]

private def arbAdj : List (List Bool) :=
  [ [false, false, false, false],
    [true,  false, true,  false],
    [true,  true,  false, true ],
    [false, true,  true,  false] ]

private def arbCostTable : List (List ℤ) :=
  [ [100, 100, 100, 100],
    [ 10, 100,   1, 100],
    [  5,   1, 100,   0],
    [100,   2,   4, 100] ]

private def G_cyc : Digraph (Fin 4) where
  Adj u w := (u, w) ∈ arbArcs

private instance : DecidableRel G_cyc.Adj :=
  fun u w => inferInstanceAs (Decidable ((u, w) ∈ arbArcs))

private def c_int (u w : Fin 4) : ℤ :=
  match u.val, w.val with
  | 1, 0 => 10 | 2, 0 => 5 | 1, 2 => 1 | 2, 1 => 1 | 3, 1 => 2 | 2, 3 => 0 | 3, 2 => 4
  | _, _ => 100

private def arbOpt : Fin 4 → Fin 4 := ![0, 2, 0, 1]

example : (edmondsTableM G_cyc c_int 0).ret = some arbOpt := by
  rw [edmondsTableM_ret_eq_edmonds]
  decide

example : (edmondsTableM G_cyc c_int 0).time ≤ 15 * (FinEnum.card (Fin 4)) ^ 3 :=
  time_edmondsTableM_le G_cyc c_int 0

example : (Digraph.parentDigraph 0 arbOpt).IsInArborescence 0 ∧
    Digraph.parentDigraph 0 arbOpt ≤ G_cyc ∧
    arcCost (Digraph.parentDigraph 0 arbOpt) c_int = 8 ∧
    ∀ (T : Digraph (Fin 4)) [DecidableRel T.Adj],
      T.IsInArborescence 0 → T ≤ G_cyc → 8 ≤ arcCost T c_int := by
  obtain ⟨hT, hTG, hopt⟩ :=
    edmondsTable_optimal (G := G_cyc) (c := c_int) (r := 0) (p := arbOpt) (by
      rw [edmondsTableM_ret_eq_edmonds]; decide)
  have hcost : arcCost (Digraph.parentDigraph (0 : Fin 4) arbOpt) c_int = 8 := by
    rw [arcCost_parentDigraph]; decide
  refine ⟨hT, hTG, hcost, fun T _ hT' hTG' => ?_⟩
  exact hcost ▸ hopt T hT' hTG'

private def G_rev : Digraph (Fin 4) where
  Adj u w := G_cyc.Adj w u

private instance : DecidableRel G_rev.Adj :=
  fun u w => inferInstanceAs (Decidable (G_cyc.Adj w u))

example : (edmondsOutTableM G_rev (fun u w => c_int w u) 0).ret = some arbOpt := by
  rw [edmondsOutTableM_ret_eq_edmondsOut]
  decide

example : (edmondsOutTableM G_rev (fun u w => c_int w u) 0).time ≤
    15 * (FinEnum.card (Fin 4)) ^ 3 :=
  time_edmondsOutTableM_le G_rev (fun u w => c_int w u) 0

private def H_infeas : Digraph (Fin 3) where
  Adj u w := (u, w) ∈ ([(1, 2), (2, 1)] : List (Fin 3 × Fin 3))

private instance : DecidableRel H_infeas.Adj :=
  fun u w => inferInstanceAs (Decidable ((u, w) ∈ ([(1, 2), (2, 1)] : List (Fin 3 × Fin 3))))

example : (edmondsOutTableM H_infeas (fun _ _ => (1 : ℤ)) 0).ret = none := by
  rw [edmondsOutTableM_ret_eq_edmondsOut]
  decide

example : ∀ t, ¬ IsInArborescenceParent (fun u w => H_infeas.Adj w u) 0 t :=
  (edmondsOutTable_spec (G := H_infeas) (c := fun _ _ => (1 : ℤ)) (r := 0)).2
    (by rw [edmondsOutTableM_ret_eq_edmondsOut]; decide)

/-! ### 3. `Arborescence.Branching` and Edmonds Section 2 reductions -/

private def brArcs : List (Fin 4 × Fin 4) := [(0, 1), (1, 2), (2, 0), (1, 0), (0, 3)]

private def brAdj : List (List Bool) :=
  [ [false, true,  false, true ],
    [true,  false, true,  false],
    [true,  false, false, false],
    [false, false, false, false] ]

private def brWtTable : List (List ℤ) :=
  [ [0,   5, 0, -3],
    [-4,  0, 6,  0],
    [1,   0, 0,  0],
    [0,   0, 0,  0] ]

private def G_br : Digraph (Fin 4) where
  Adj u v := (u, v) ∈ brArcs

private instance : DecidableRel G_br.Adj :=
  fun u v => inferInstanceAs (Decidable ((u, v) ∈ brArcs))

private def w_br (u v : Fin 4) : ℤ :=
  match u.val, v.val with
  | 0, 1 => 5 | 1, 2 => 6 | 2, 0 => 1 | 1, 0 => -4 | 0, 3 => -3
  | _, _ => 0

example : optimumBranchingParent G_br w_br = ![0, 0, 1, 3] := by decide

example : arcCost (optimumBranching G_br w_br) w_br = 11 := by decide

private def B_sub : Digraph (Fin 4) where
  Adj u v := (u, v) ∈ ([(0, 1), (1, 2)] : List (Fin 4 × Fin 4))

private instance : DecidableRel B_sub.Adj :=
  fun u v => inferInstanceAs (Decidable ((u, v) ∈ ([(0, 1), (1, 2)] : List (Fin 4 × Fin 4))))

private theorem B_sub_isBranching : B_sub.IsBranching := by
  have hEq : B_sub = Digraph.branchingDigraph ![0, 0, 1, 3] := by
    ext u v; fin_cases u <;> fin_cases v <;> decide
  rw [hEq, Digraph.isBranching_branchingDigraph_iff]
  intro v
  fin_cases v
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

example : (optimumBranching G_br w_br).IsBranching ∧ optimumBranching G_br w_br ≤ G_br ∧
    arcCost B_sub w_br ≤ arcCost (optimumBranching G_br w_br) w_br :=
  ⟨optimumBranching_isBranching G_br w_br, optimumBranching_le G_br w_br,
    optimumBranching_optimal G_br w_br B_sub B_sub_isBranching (fun u v huv => by
      fin_cases u <;> fin_cases v <;> simp_all [B_sub, G_br, brArcs])⟩

example : (optimumBranchingM G_br w_br).ret = ![0, 0, 1, 3] := by
  rw [optimumBranchingM_ret_eq]
  decide

example : (optimumBranchingM G_br w_br).time ≤ 15 * (FinEnum.card (Fin 4) + 1) ^ 3 :=
  time_optimumBranchingM_le G_br w_br

example : (minBranching G_br w_br).IsBranching ∧ minBranching G_br w_br ≤ G_br ∧
    arcCost (minBranching G_br w_br) w_br = -7 := by
  refine ⟨minBranching_isBranching G_br w_br, minBranching_le G_br w_br, ?_⟩
  decide

private theorem br_shift_lt :
    ∑ e ∈ Finset.univ.filter (fun e : Fin 4 × Fin 4 => G_br.Adj e.1 e.2),
      max (w_br e.1 e.2) (-w_br e.1 e.2) < (25 : ℤ) := by
  decide

private def spanOut0 : Digraph (Fin 4) := Digraph.branchingDigraph ![0, 0, 1, 0]

private instance : DecidableRel spanOut0.Adj :=
  fun u v => inferInstanceAs (Decidable ((Digraph.branchingDigraph ![0, 0, 1, 0]).Adj u v))

private theorem spanOut0_isOut : spanOut0.IsOutArborescence 0 := by
  have hB : spanOut0.IsBranching := by
    rw [spanOut0, Digraph.isBranching_branchingDigraph_iff]
    intro v
    fin_cases v
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
  have hcard : (Finset.univ.filter fun e : Fin 4 × Fin 4 => spanOut0.Adj e.1 e.2).card =
      Fintype.card (Fin 4) - 1 := by
    decide
  obtain ⟨r, hr⟩ := hB.isOutArborescence_iff_card_arcs.mpr hcard
  have hr0 : r = 0 := by
    by_contra hne
    obtain ⟨u, hu, -⟩ := (Digraph.isOutArborescence_iff.mp hr).2.1 0 (Ne.symm hne)
    fin_cases u <;> simp [spanOut0, Digraph.branchingDigraph] at hu
  exact hr0 ▸ hr

private theorem spanOut0_le : spanOut0 ≤ G_br := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp_all [spanOut0, Digraph.branchingDigraph, G_br, brArcs]

example :
    let Bstar := optimumBranching G_br (fun u v => w_br u v + (25 : ℤ))
    (∃ r, Bstar.IsOutArborescence r) ∧
      (∀ (T : Digraph (Fin 4)) [DecidableRel T.Adj],
        T.IsOutArborescence 0 → T ≤ G_br → arcCost T w_br ≤ arcCost Bstar w_br) ∧
      arcCost Bstar w_br = 8 := by
  dsimp only
  have hshift := edmonds_shift_weight_branching G_br w_br 25 br_shift_lt
  obtain ⟨hex_out, hopt⟩ := hshift.2.2.2 ⟨0⟩ ⟨0, spanOut0, spanOut0_isOut, spanOut0_le⟩
  exact ⟨hex_out, fun T _ hT hTG => hopt 0 T hT hTG, by decide⟩

private def spanOut1 : Digraph (Fin 4) := Digraph.branchingDigraph ![2, 1, 1, 0]

private instance : DecidableRel spanOut1.Adj :=
  fun u v => inferInstanceAs (Decidable ((Digraph.branchingDigraph ![2, 1, 1, 0]).Adj u v))

private theorem spanOut1_isOut : spanOut1.IsOutArborescence 1 := by
  have hB : spanOut1.IsBranching := by
    rw [spanOut1, Digraph.isBranching_branchingDigraph_iff]
    intro v
    fin_cases v
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  have hcard : (Finset.univ.filter fun e : Fin 4 × Fin 4 => spanOut1.Adj e.1 e.2).card =
      Fintype.card (Fin 4) - 1 := by
    decide
  obtain ⟨r, hr⟩ := hB.isOutArborescence_iff_card_arcs.mpr hcard
  have hr1 : r = 1 := by
    by_contra hne
    obtain ⟨u, hu, -⟩ := (Digraph.isOutArborescence_iff.mp hr).2.1 1 (Ne.symm hne)
    fin_cases u <;> simp [spanOut1, Digraph.branchingDigraph] at hu
  exact hr1 ▸ hr

private theorem spanOut1_le : spanOut1 ≤ G_br := by
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp_all [spanOut1, Digraph.branchingDigraph, G_br, brArcs]

private theorem br_rooted_shift_lt :
    ∑ e ∈ Finset.univ.filter (fun e : Fin 4 × Fin 4 => (rootedDigraph G_br 1).Adj e.1 e.2),
      max (w_br e.1 e.2) (-w_br e.1 e.2) < (25 : ℤ) := by
  decide

example :
    let Bstar := optimumBranching (rootedDigraph G_br 1) (fun u v => w_br u v + (25 : ℤ))
    Bstar.IsOutArborescence 1 ∧ Bstar ≤ G_br ∧ arcCost Bstar w_br = 4 := by
  dsimp only
  have hroot := edmonds_rooted_outArborescence_of_shift G_br 1 w_br 25 br_rooted_shift_lt
    ⟨spanOut1, spanOut1_isOut, spanOut1_le⟩
  exact ⟨hroot.1, hroot.2.1, by decide⟩

/-! ### 4. `Arborescence.PolyTime`: list solvers and `P` certificates -/

private def arbInst : ArborescenceInstance := ⟨arbAdj, arbCostTable, 0⟩

private def arbInstNeg : ArborescenceInstance :=
  ⟨arbAdj, arbCostTable.map (List.map fun c => c - 20), 0⟩

private def arbInstOob : ArborescenceInstance := ⟨arbAdj, arbCostTable, 4⟩

private def arbInstRev : ArborescenceInstance :=
  ⟨transposeBoolTable arbAdj, transposeIntTable 4 arbCostTable, 0⟩

private def H_adj : List (List Bool) :=
  [[false, false, false], [false, false, true], [false, true, false]]

private def H_cost : List (List ℤ) := [[0, 0, 0], [0, 0, 1], [0, 1, 0]]

private def brInst : BranchingInstance := ⟨brAdj, brWtTable⟩

example : edmondsList arbInst = some [0, 2, 0, 1] := by decide

example : edmondsList arbInstNeg = some [0, 2, 0, 1] := by decide

example : edmondsList arbInstOob = none := by decide

example : edmondsOutList arbInstRev = some [0, 2, 0, 1] := by decide

example : edmondsOutList ⟨H_adj, H_cost, 0⟩ = none := by decide

example : optimumBranchingList brInst = [0, 0, 1, 3] := by decide

example : minArborescenceDecide ⟨arbInst, 8⟩ = true ∧
    (⟨arbInst, 8⟩ : ArborescenceDecInstance) ∈ minArborescenceDec :=
  ⟨by decide, (minArborescenceDecide_eq_true_iff _).mp (by decide)⟩

example : minArborescenceDecide ⟨arbInst, 7⟩ = false ∧
    (⟨arbInst, 7⟩ : ArborescenceDecInstance) ∉ minArborescenceDec := by
  have hf : minArborescenceDecide ⟨arbInst, 7⟩ = false := by decide
  refine ⟨hf, fun h => ?_⟩
  have ht : minArborescenceDecide ⟨arbInst, 7⟩ = true :=
    (minArborescenceDecide_eq_true_iff _).mpr h
  rw [hf] at ht
  exact absurd ht (by decide)

example : minArborescenceDecide ⟨arbInstNeg, -52⟩ = true ∧
    minArborescenceDecide ⟨arbInstNeg, -53⟩ = false := ⟨by decide, by decide⟩

example : minOutArborescenceDecide ⟨arbInstRev, 8⟩ = true ∧
    (⟨arbInstRev, 8⟩ : ArborescenceDecInstance) ∈ minOutArborescenceDec :=
  ⟨by decide, (minOutArborescenceDecide_eq_true_iff _).mp (by decide)⟩

example : minOutArborescenceDecide ⟨arbInstRev, 7⟩ = false ∧
    (⟨arbInstRev, 7⟩ : ArborescenceDecInstance) ∉ minOutArborescenceDec := by
  have hf : minOutArborescenceDecide ⟨arbInstRev, 7⟩ = false := by decide
  refine ⟨hf, fun h => ?_⟩
  have ht : minOutArborescenceDecide ⟨arbInstRev, 7⟩ = true :=
    (minOutArborescenceDecide_eq_true_iff _).mpr h
  rw [hf] at ht
  exact absurd ht (by decide)

example : maxBranchingDecide ⟨brInst, 11⟩ = true ∧
    (⟨brInst, 11⟩ : BranchingDecInstance) ∈ maxBranchingDec :=
  ⟨by decide, (maxBranchingDecide_eq_true_iff _).mp (by decide)⟩

example : maxBranchingDecide ⟨brInst, 12⟩ = false ∧
    (⟨brInst, 12⟩ : BranchingDecInstance) ∉ maxBranchingDec := by
  have hf : maxBranchingDecide ⟨brInst, 12⟩ = false := by decide
  refine ⟨hf, fun h => ?_⟩
  have ht : maxBranchingDecide ⟨brInst, 12⟩ = true :=
    (maxBranchingDecide_eq_true_iff _).mpr h
  rw [hf] at ht
  exact absurd ht (by decide)

example : minArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  minArborescenceDec_mem_P

example : minOutArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  minOutArborescenceDec_mem_P

example : maxBranchingDec ∈ Cslib.Complexity.P encBranchingDecInstance :=
  maxBranchingDec_mem_P

end CslibFrontierTests.ArborescenceBranching
