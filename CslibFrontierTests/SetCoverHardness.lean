/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.PCP.Approximation.SetCover.LundYannakakis
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

/-!
# Set Cover approximation hardness tests

Nonvacuous kernel-checked examples (using no `native_decide`) exercising:

1. Concrete unweighted and weighted `SetSystem` instances (`SetCover`, `WeightedSetCover`,
   `Coverable`, `coverableBool`, `isCoverList`, and the `Greedy` and `toWeighted` bridges).
2. Explicit Boolean-cube separation on `boolCubeGadget Bool` and `exists_small_partitionGadget`.
3. Concrete `toWeightedSetCoverOf` and `toSetCoverOf` reductions on satisfiable and unsatisfiable
   two-edge `LabelCover` graphs, including non-uniform vertex degrees.
4. Instantiations of `GapSetCover_npHard`, `GapWeightedSetCover_npHard`,
   `P_eq_NP_of_setCover_approx_const`, `exists_weightedSetCover_log_gap`, and
   `exists_setCover_log_gap`.
-/

public section

namespace CslibFrontierTests.SetCoverHardness

open Cslib.Complexity Cslib.PCP Cslib.PCP.Encoded
open Cslib.Complexity.SetCoverReduction
open Turing.MultiTapeTM

/-! ### 1. Concrete unweighted and weighted set systems -/

/-- Coverable 3-element system whose minimum cover uses sets `1` and `2`. -/
def sysSample : SetSystem :=
  ⟨[1, 2, 3], [[1], [1, 2], [2, 3]]⟩

/-- Uncoverable system: ground element `4` appears in no candidate set. -/
def sysUncoverable : SetSystem :=
  ⟨[1, 4], [[1, 2], [2, 3]]⟩

example : sysSample.isCoverList [1, 2] = true := by decide

example : sysSample.isCoverList [0, 1] = false := by decide

example : sysSample.Coverable :=
  (SetSystem.coverableBool_eq_true_iff _).1 (by decide)

example : ¬ sysUncoverable.Coverable := by
  intro h
  have hb := (SetSystem.coverableBool_eq_true_iff _).2 h
  revert hb
  decide

example : (sysSample, 2) ∈ SetCover := by
  rw [mem_SetCover_iff_optCoverSize]
  refine ⟨(SetSystem.coverableBool_eq_true_iff _).1 (by decide), ?_⟩
  let i₁ : Fin sysSample.sets.length := ⟨1, by simp [sysSample]⟩
  let i₂ : Fin sysSample.sets.length := ⟨2, by simp [sysSample]⟩
  refine SetSystem.optCoverSize_le (C := {i₁, i₂}) ?_
  intro u hu
  simp only [sysSample, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨i₁, Finset.mem_insert_self _ _,
      by simp only [i₁, sysSample, Fin.getElem_fin, List.getElem_cons_succ,
        List.getElem_cons_zero, List.mem_cons, true_or]⟩
  · exact ⟨i₁, Finset.mem_insert_self _ _,
      by simp only [i₁, sysSample, Fin.getElem_fin, List.getElem_cons_succ,
        List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false, or_true]⟩
  · exact ⟨i₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      by simp only [i₂, sysSample, Fin.getElem_fin, List.getElem_cons_succ,
        List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false, or_true]⟩

example : (sysSample, 1) ∉ SetCover := by
  intro ⟨C, hC, hk⟩
  have hmem1 : ∃ i ∈ C, 1 ∈ sysSample.sets[i] := hC 1 (by decide)
  have hmem3 : ∃ i ∈ C, 3 ∈ sysSample.sets[i] := hC 3 (by decide)
  obtain ⟨i₁, hi₁, h1⟩ := hmem1
  obtain ⟨i₃, hi₃, h3⟩ := hmem3
  have hne : i₁ ≠ i₃ := by
    rintro rfl
    fin_cases i₁ <;> simp_all [sysSample]
  have hcard : 2 ≤ C.card := by
    have hsub : {i₁, i₃} ⊆ C := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · exact hi₁
      · rw [Finset.mem_singleton.1 hx']
        exact hi₃
    calc 2 = ({i₁, i₃} : Finset (Fin sysSample.sets.length)).card := by
            rw [Finset.card_pair hne]
      _ ≤ C.card := Finset.card_le_card hsub
  omega

/-- Empty-ground boundary systems (`ground = []` has optimal cost `0`). -/
def sysEmptyGround : SetSystem :=
  ⟨[], [[1]]⟩

def wSysEmptyGround : WeightedSetSystem :=
  ⟨[], [⟨[1], 5⟩]⟩

example : sysEmptyGround.Coverable ∧ sysEmptyGround.optCoverSize = 0 ∧
    sysEmptyGround.IsCover sysEmptyGround.greedyIndices.toFinset := by
  have hcov : sysEmptyGround.Coverable := (SetSystem.coverableBool_eq_true_iff _).1 (by decide)
  have hopt : sysEmptyGround.optCoverSize = 0 :=
    Nat.le_zero.1 (SetSystem.optCoverSize_le (C := ∅) (fun _ h => by simp [sysEmptyGround] at h))
  exact ⟨hcov, hopt, sysEmptyGround.greedyIndices_isCover hcov⟩

example : wSysEmptyGround.Coverable ∧ wSysEmptyGround.optCoverWeight = 0 ∧
    wSysEmptyGround.IsCover wSysEmptyGround.greedyIndices.toFinset := by
  have hcov : wSysEmptyGround.Coverable :=
    (WeightedSetSystem.coverableBool_eq_true_iff _).1 (by decide)
  have hopt : wSysEmptyGround.optCoverWeight = 0 :=
    Nat.le_zero.1 ((WeightedSetSystem.optCoverWeight_le (C := ∅)
      (fun _ h => by simp [wSysEmptyGround] at h)).trans_eq
      (by simp [WeightedSetSystem.coverWeight]))
  exact ⟨hcov, hopt, wSysEmptyGround.greedyIndices_isCover hcov⟩

/-- Weighted system where the singleton union `{1, 2}` has weight `3` vs `[1, 2, 3]` of
weight `5`. -/
def wSysSample : WeightedSetSystem :=
  ⟨[1, 2, 3], [⟨[1, 2], 2⟩, ⟨[2, 3], 1⟩, ⟨[1, 2, 3], 5⟩]⟩

/-- Uncoverable weighted system: ground element `4` appears in no candidate set. -/
def wSysUncoverable : WeightedSetSystem :=
  ⟨[1, 4], [⟨[1, 2], 2⟩, ⟨[2, 3], 1⟩]⟩

example : ¬ wSysUncoverable.Coverable := by
  intro h
  have hb := (WeightedSetSystem.coverableBool_eq_true_iff _).2 h
  revert hb
  decide

example : (wSysSample, 3) ∈ WeightedSetCover := by
  let i₀ : Fin wSysSample.sets.length := ⟨0, by simp [wSysSample]⟩
  let i₁ : Fin wSysSample.sets.length := ⟨1, by simp [wSysSample]⟩
  let C : Finset (Fin wSysSample.sets.length) := {i₀, i₁}
  refine ⟨C, fun u hu => ?_, ?_⟩
  · simp only [wSysSample, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨i₀, Finset.mem_insert_self _ _,
        by simp only [i₀, wSysSample, Fin.getElem_fin, List.getElem_cons_zero,
          List.mem_cons, true_or]⟩
    · exact ⟨i₀, Finset.mem_insert_self _ _,
        by simp only [i₀, wSysSample, Fin.getElem_fin, List.getElem_cons_zero,
          List.mem_cons, List.not_mem_nil, or_false, or_true]⟩
    · exact ⟨i₁, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        by simp only [i₁, wSysSample, Fin.getElem_fin, List.getElem_cons_succ,
          List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false, or_true]⟩
  · have hne : i₀ ≠ i₁ := by simp [i₀, i₁]
    have hsum : C.sum (fun i => wSysSample.sets[i].weight) = 3 := by
      simp only [C]
      rw [Finset.sum_pair hne]
      rfl
    rw [WeightedSetSystem.coverWeight]
    exact hsum.le

example : (wSysSample, 2) ∉ WeightedSetCover := by
  intro ⟨C, hC, hwt⟩
  have hmem1 : ∃ i ∈ C, 1 ∈ wSysSample.sets[i].elements := hC 1 (by decide)
  have hmem3 : ∃ i ∈ C, 3 ∈ wSysSample.sets[i].elements := hC 3 (by decide)
  obtain ⟨i₁, hi₁, h1⟩ := hmem1
  obtain ⟨i₃, hi₃, h3⟩ := hmem3
  let i₀ : Fin wSysSample.sets.length := ⟨0, by simp [wSysSample]⟩
  let i₁' : Fin wSysSample.sets.length := ⟨1, by simp [wSysSample]⟩
  let i₂ : Fin wSysSample.sets.length := ⟨2, by simp [wSysSample]⟩
  have hsum_le : C.sum (fun i => wSysSample.sets[i].weight) ≤ 2 := hwt
  fin_cases i₁ <;> simp [wSysSample] at h1
  · fin_cases i₃ <;> simp [wSysSample] at h3
    · have hsub : {i₀, i₁'} ⊆ C := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact hi₁
        · rw [Finset.mem_singleton.1 hx']
          exact hi₃
      have hne : i₀ ≠ i₁' := by simp [i₀, i₁']
      have h3le : 3 ≤ C.sum (fun i => wSysSample.sets[i].weight) := by
        calc 3 = ({i₀, i₁'} : Finset (Fin wSysSample.sets.length)).sum
                (fun i => wSysSample.sets[i].weight) := by
              rw [Finset.sum_pair hne]; rfl
          _ ≤ C.sum (fun i => wSysSample.sets[i].weight) :=
              Finset.sum_le_sum_of_subset hsub
      omega
    · have h5le : 5 ≤ C.sum (fun i => wSysSample.sets[i].weight) := by
        calc 5 = ({i₂} : Finset (Fin wSysSample.sets.length)).sum
                (fun i => wSysSample.sets[i].weight) := rfl
          _ ≤ C.sum (fun i => wSysSample.sets[i].weight) :=
              Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.2 hi₃)
      omega
  · have h5le : 5 ≤ C.sum (fun i => wSysSample.sets[i].weight) := by
      calc 5 = ({i₂} : Finset (Fin wSysSample.sets.length)).sum
              (fun i => wSysSample.sets[i].weight) := rfl
        _ ≤ C.sum (fun i => wSysSample.sets[i].weight) :=
            Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.2 hi₁)
    omega

example : wSysSample.Coverable :=
  (WeightedSetSystem.coverable_iff_toSetSystem _).2
    ((SetSystem.coverableBool_eq_true_iff _).1 (by decide))

example : sysSample.toWeighted.optCoverWeight = sysSample.optCoverSize :=
  optCoverWeight_toWeighted sysSample

example : ApproxPreservingReducible minSetCover minWeightedSetCover
    encSetSystem encWeightedSetSystem (encList encNat) (encList encNat) (fun _ ρ => ρ) :=
  (ApproxPreservingReducible.refl minSetCover encSetSystem (encList encNat)).trans
    approxPreservingReducible_setCover_weightedSetCover

example {A : WeightedSetSystem → List ℕ}
    (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => 2) A) :
    ∃ A₁ : SetSystem → List ℕ,
      ComputableInPolyTime A₁ encSetSystem (encList encNat) ∧
        minSetCover.IsApprox (fun _ => 2) A₁ :=
  approxPreservingReducible_setCover_weightedSetCover.comp_isApprox hA happrox

example : PromiseProblem.PolyTimeReducible encSetCover encWeightedSetCover
    (GapSetCover 3) (GapWeightedSetCover 3) ∧
    (sysSample.toWeighted, 2) ∈ (GapWeightedSetCover 2).yes := by
  refine ⟨polyTimeReducible_GapSetCover_GapWeightedSetCover 3, ?_⟩
  rw [GapWeightedSetCover, mem_yes_GapWeightedSetCoverFn]
  refine ⟨(coverable_toWeighted_iff _).2
    ((SetSystem.coverableBool_eq_true_iff _).1 (by decide)), ?_⟩
  rw [optCoverWeight_toWeighted]
  let i₁ : Fin sysSample.sets.length := ⟨1, by simp [sysSample]⟩
  let i₂ : Fin sysSample.sets.length := ⟨2, by simp [sysSample]⟩
  have hle : sysSample.optCoverSize ≤ 2 := by
    refine SetSystem.optCoverSize_le (C := {i₁, i₂}) ?_ |>.trans ?_
    · intro u hu
      simp only [sysSample, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl
      · exact ⟨i₁, Finset.mem_insert_self _ _,
          by simp [i₁, sysSample]⟩
      · exact ⟨i₁, Finset.mem_insert_self _ _,
          by simp [i₁, sysSample]⟩
      · exact ⟨i₂, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          by simp [i₂, sysSample]⟩
    · exact (Finset.card_insert_le _ _).trans (by decide)
  exact_mod_cast hle

example : sysSample.IsCover sysSample.greedyIndices.toFinset ∧
    (sysSample.greedyIndices.length : ℝ) ≤
      (1 + Real.log sysSample.ground.toFinset.card) * sysSample.optCoverSize :=
  let hcov := (SetSystem.coverableBool_eq_true_iff sysSample).1 (by decide)
  ⟨sysSample.greedyIndices_isCover hcov, sysSample.greedyIndices_length_le_one_add_log hcov⟩

example : wSysSample.IsCover wSysSample.greedyIndices.toFinset ∧
    (wSysSample.coverWeight wSysSample.greedyIndices.toFinset : ℝ) ≤
      (1 + Real.log wSysSample.ground.toFinset.card) * wSysSample.optCoverWeight :=
  let hcov := (WeightedSetSystem.coverableBool_eq_true_iff wSysSample).1 (by decide)
  ⟨wSysSample.greedyIndices_isCover hcov, wSysSample.greedyWeight_le_one_add_log hcov⟩

/-! ### 2. Partition gadgets -/

example : (boolCubeGadget Bool).size = 4 := by decide

example : ∃ x < (boolCubeGadget Bool).size,
    (boolCubeGadget Bool).mem x true = true ∧ (boolCubeGadget Bool).mem x false = false :=
  (boolCubeGadget_separates Bool 2 {true} {false} (by decide) (by decide)).imp fun _ hx =>
    ⟨hx.1, hx.2.1 true (by simp), hx.2.2 false (by simp)⟩

example : ∀ (A' B' : Finset Bool), A'.card + B'.card ≤ 2 →
    (∀ x < (boolCubeGadget Bool).size,
      (∃ a ∈ A', (boolCubeGadget Bool).mem x a = false) ∨
        (∃ b ∈ B', (boolCubeGadget Bool).mem x b = true)) →
    ∃ a ∈ A', ∃ b ∈ B', a = b :=
  fun A' B' hcard hcov =>
    PartitionGadget.exists_eq_of_covers (boolCubeGadget_separates Bool 2) id A' B' hcard hcov

example : ∃ G : PartitionGadget Bool, G.Separates 2 ∧ G.size = 28 := by
  obtain ⟨G, hsep, hsz⟩ := exists_small_partitionGadget Bool 2
  refine ⟨G, hsep, ?_⟩
  have hcard : Fintype.card Bool = 2 := by simp
  have hclog : Nat.clog 2 (2 * 2 + 1) = 3 := by decide
  rw [hcard, hclog] at hsz
  exact hsz

/-! ### 3. Concrete Label Cover to Set Cover reductions -/

/-- Satisfiable two-edge Label Cover graph over `Bool → Bool` with non-uniform right degree
(`degR 0 = 2`). -/
def satGraph : Graph (Bool → Bool) :=
  ⟨2, [⟨0, 0, id⟩, ⟨1, 0, fun _ => true⟩]⟩

/-- Contradictory two-edge Label Cover graph forcing `false = b` and `true = b` at vertex `0`. -/
def unsatGraph : Graph (Bool → Bool) :=
  ⟨1, [⟨0, 0, fun _ => false⟩, ⟨0, 0, fun _ => true⟩]⟩

example : satGraph.edges.length = 2 := rfl

example : (weightedSetSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph).ground.length = 8 := by
  rw [weightedSetSystemOf_ground_length]
  have hlen : satGraph.edges.length = 2 := rfl
  have hsz : (boolCubeGadget Bool).size = 4 := by decide
  rw [hlen, hsz]

example : (setSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph).ground.length ≤ 32 := by
  refine setSystemOf_ground_length_le.trans_eq ?_
  have hlen : satGraph.edges.length = 2 := rfl
  have hsz : (boolCubeGadget Bool).size = 4 := by decide
  rw [hlen, hsz]
  norm_num

example : (setSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph).Coverable :=
  setSystemOf_coverable (by decide) (by decide) (boolCubeGadget Bool) satGraph

example : (weightedSetSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph).Coverable :=
  weightedSetSystemOf_coverable (by decide) (by decide) (boolCubeGadget Bool) satGraph

example : (toSetCoverOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph) ∈ (GapSetCover 2).yes := by
  rw [GapSetCover, mem_yes_GapSetCoverFn]
  refine ⟨setSystemOf_coverable (by decide) (by decide) _ _,
    setSystemOf_complete (by decide) (by decide) _ _ ?_⟩
  have hsat : (satGraph.toGraph projectionEval).Satisfiable := by
    rw [satisfiable_toGraph_projectionEval_iff]
    refine ⟨fun _ => true, fun _ => true, fun d hd => ?_⟩
    simp only [satGraph, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  rw [(ConstraintGraph.unsatVal_eq_zero_iff _).2 hsat]
  norm_num

example : (toWeightedSetCoverOf [false, true] [false, true] false
    (boolCubeGadget Bool) satGraph) ∈ (GapWeightedSetCover 2).yes := by
  rw [GapWeightedSetCover, mem_yes_GapWeightedSetCoverFn]
  refine ⟨weightedSetSystemOf_coverable (by decide) (by decide) _ _,
    weightedSetSystemOf_complete (by decide) (by decide) _ _ ?_⟩
  have hsat : (satGraph.toGraph projectionEval).Satisfiable := by
    rw [satisfiable_toGraph_projectionEval_iff]
    refine ⟨fun _ => true, fun _ => true, fun d hd => ?_⟩
    simp only [satGraph, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> rfl
  rw [(ConstraintGraph.unsatVal_eq_zero_iff _).2 hsat]
  norm_num

example : ¬ (unsatGraph.toGraph projectionEval).Satisfiable := by
  rw [satisfiable_toGraph_projectionEval_iff]
  rintro ⟨ℓ, r, h⟩
  have h0 : false = r 0 := h ⟨0, 0, fun _ => false⟩ (by simp [unsatGraph])
  have h1 : true = r 0 := h ⟨0, 0, fun _ => true⟩ (by simp [unsatGraph])
  exact Bool.false_ne_true (h0.trans h1.symm)

example : (setSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) unsatGraph).optCoverSize ≤ 4 →
    (1 - 2 * (1 : ℝ) / 4) * (4 / (4 : ℝ) ^ 2) ≤
      1 - ConstraintGraph.unsatVal (unsatGraph.toGraph projectionEval) := by
  intro hopt
  exact setSystemOf_sound (by decide : ∀ a : Bool, a ∈ [false, true])
    (by decide : ∀ b : Bool, b ∈ [false, true]) (by decide : 0 < 4)
    (boolCubeGadget_separates Bool 4) (by simp [unsatGraph]) (by exact_mod_cast hopt)

example : (weightedSetSystemOf [false, true] [false, true] false
    (boolCubeGadget Bool) unsatGraph).optCoverWeight ≤ 4 →
    (1 - 2 * (1 : ℝ) / 4) * (4 / (4 : ℝ) ^ 2) ≤
      1 - ConstraintGraph.unsatVal (unsatGraph.toGraph projectionEval) := by
  intro hopt
  exact weightedSetSystemOf_sound (by decide : ∀ a : Bool, a ∈ [false, true])
    (by decide : ∀ b : Bool, b ∈ [false, true]) (by decide : 0 < 4)
    (boolCubeGadget_separates Bool 4) (by simp [unsatGraph]) (by exact_mod_cast hopt)

/-! ### 4. Complexity-theoretic endpoints -/

example (hpne : P encCNF ≠ NP encCNF) :
    GapSetCover 3 ∉ PromiseP encSetCover ∧ GapWeightedSetCover 3 ∉ PromiseP encWeightedSetCover :=
  ⟨GapSetCover_notMem_PromiseP (by norm_num) hpne,
    GapWeightedSetCover_notMem_PromiseP (by norm_num) hpne⟩

example {A : SetSystem → List ℕ}
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minSetCover.IsApprox (fun _ => 2) A) :
    P encCNF = NP encCNF :=
  P_eq_NP_of_setCover_approx_const (by norm_num) hA happrox encCNF

example {A : WeightedSetSystem → List ℕ}
    (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => 2) A) :
    P encCNF = NP encCNF :=
  P_eq_NP_of_weightedSetCover_approx_const (by norm_num) hA happrox encCNF

private theorem quarter_lt_inv_four_log_two : (1 / 4 : ℝ) < 1 / (4 * Real.log 2) := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 :=
    (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans_eq (by norm_num)
  exact div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)

example : ∃ t : ℕ, 4 ≤ t ∧ ∃ G : PartitionGadget Bool, G.Separates t ∧
    G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card Bool + 1) + 1) ∧
    let bs : List Bool := Finset.univ.toList
    let gs : List Bool := Finset.univ.toList
    let S := setSystemOf bs gs (Classical.arbitrary Bool) G satGraph
    let k := 2 * List.length satGraph.edges
    S.Coverable ∧
    (1 ≤ 1 - ConstraintGraph.unsatVal (satGraph.toGraph projectionEval) →
      (S, k) ∈ (GapSetCoverFn fun X => (1 / 4 : ℝ) * Real.log (List.length X.ground)).yes) ∧
    (1 - ConstraintGraph.unsatVal (satGraph.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
      (S, k) ∈ (GapSetCoverFn fun X => (1 / 4 : ℝ) * Real.log (List.length X.ground)).no) :=
  exists_setCover_log_gap (c := (1 / 4 : ℝ)) (by norm_num) quarter_lt_inv_four_log_two
    satGraph (by simp [satGraph])

example : ∃ t : ℕ, 4 ≤ t ∧ ∃ G : PartitionGadget Bool, G.Separates t ∧
    G.size = 2 ^ t * (t * Nat.clog 2 (2 * Fintype.card Bool + 1) + 1) ∧
    let bs : List Bool := Finset.univ.toList
    let gs : List Bool := Finset.univ.toList
    let W := weightedSetSystemOf bs gs (Classical.arbitrary Bool) G satGraph
    let k := 2 * List.length satGraph.edges
    W.Coverable ∧
    (1 ≤ 1 - ConstraintGraph.unsatVal (satGraph.toGraph projectionEval) →
      (W, k) ∈ (GapWeightedSetCoverFn fun X =>
        (1 / 4 : ℝ) * Real.log (List.length X.ground)).yes) ∧
    (1 - ConstraintGraph.unsatVal (satGraph.toGraph projectionEval) ≤ 1 / (t : ℝ) ^ 2 →
      (W, k) ∈ (GapWeightedSetCoverFn fun X =>
        (1 / 4 : ℝ) * Real.log (List.length X.ground)).no) :=
  exists_weightedSetCover_log_gap (c := (1 / 4 : ℝ)) (by norm_num) quarter_lt_inv_four_log_two
    satGraph (by simp [satGraph])

end CslibFrontierTests.SetCoverHardness
