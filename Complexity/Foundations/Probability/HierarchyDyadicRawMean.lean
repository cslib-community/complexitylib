/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawExecution
public import Complexity.Foundations.Probability.RootMetric.Stationarity

/-!
# Conditional means of the literal dyadic RAW execution

The common walk preserves each assembled group's conditional mean on its actual
source/usage grid. Its signed means telescope before absolute values or clipping.
Every ray keeps its own scale and last budget. Equal-budget groups and budget zero
need no recursive availability. Availability below is conditional, not a recursive
execution theorem. These are original execution identities; no noise estimate is claimed.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- A group's actual paired samples, with zero used only as an option decoder.
`pairedSample_decoded` justifies this decoder from executed endpoint availability. -/
@[expose] def decodedGroupInput
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ((B.rays t).map fun bin =>
    ((B.sample history (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))
      t r bin).getD 0 σ x y -
    (B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin))
      t r bin).getD 0 σ x y)).sum

private theorem sample_exists_of_positive
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ)
    (h : 0 < m → ∃ A, B.sample history m t r bin = some A) :
    ∃ A, B.sample history m t r bin = some A := by
  by_cases hm : m = 0
  · subst m
    exact ⟨0, B.sample_zero history t r bin⟩
  · exact h (Nat.pos_of_ne_zero hm)

/-- Equal-budget groups execute zero without asking whether either sample exists. -/
theorem pairedSample_decoded
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ)
    (hcalls : let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f t r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c t r bin = some C)) :
    B.pairedSample history M d t r bin = some
      ((B.sample history (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))
        t r bin).getD 0 -
      (B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin))
        t r bin).getD 0) := by
  dsimp only at hcalls
  by_cases he : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  · simp only [pairedSample, he, ↓reduceIte, sub_self]
  · obtain ⟨hf, hc⟩ := hcalls he
    obtain ⟨A, hA⟩ := B.sample_exists_of_positive history _ t r bin hf
    obtain ⟨C, hC⟩ := B.sample_exists_of_positive history _ t r bin hc
    simp only [pairedSample, he, ↓reduceIte, hA, hC, Option.getD_some]
    rfl

/-- The actual common completion preserves the signed group mean. This uses the
original source and usage suffixes, and includes empty ray lists and empty slices. -/
theorem completedGroup_mean
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hcalls : ∀ bin ∈ B.rays t,
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f t r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c t r bin = some C)) :
    ∃ F, B.completedGroup history M d t r = some F ∧ ∀ x y,
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su)) F x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (B.decodedGroupInput history M d t r) x y := by
  by_cases he : (B.rays t).isEmpty = true
  · have hz : B.rays t = [] := List.isEmpty_iff.mp he
    refine ⟨0, ?_, ?_⟩
    · simp only [completedGroup, he, ↓reduceIte]
    · intro x y
      unfold decodedGroupInput
      rw [hz]
      rfl
  let inputs := (B.rays t).map fun bin =>
    (B.sample history (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))
      t r bin).getD 0 -
    (B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin))
      t r bin).getD 0
  have hinputs : (B.rays t).mapM (B.pairedSample history M d t r) = some inputs := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun bin hb => B.pairedSample_decoded history M d t r bin (hcalls bin hb)
  have hin : (fun σ x y => (inputs.map (fun A => A σ x y)).sum) =
      B.decodedGroupInput history M d t r := by
    funext σ x y
    simp only [inputs, List.map_map, Function.comp_def,
      Pi.sub_apply, Matrix.sub_apply, decodedGroupInput]
  refine ⟨conditionalWalk
    (X s (side P ks) (CopyPadding.identifier B.padding ss))
    (Y u (side P ku) (CopyPadding.identifier B.padding su))
    (graph s u hsu (side P ks) (side P ku) (side_le P ks) (side_le P ku)
      (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
    (fun _ _ => B.steps M r d) (B.decodedGroupInput history M d t r),
    ?_, fun x y => rowSliceMean_conditionalWalk _ _ _ _ _ x y⟩
  rw [completedGroup, ite_eq_right he, hinputs]
  simp only [bind, Option.bind_some, hin]
  exact B.complete_grid M r s u hsu ks ku ss su hs hu _ d

/-- The actual decoded group inputs telescope ray by ray. Both signed endpoint
values are retained, so this identity also applies when scales are wholly omitted. -/
theorem decodedGroupInput_sum
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M m j : ℕ) (hj : j < m) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (σ : Environment P 3) (x y : ZMod P) :
    ∑ i ∈ range (j + 1), B.decodedGroupInput history M (dyadicSlack m i) t r σ x y =
      ((B.rays t).map fun bin =>
        ((B.sample history (LogSpaceEstimation.lastBudget M (dyadicSlack m j) B.slack
          (B.sampleScale r bin)) t r bin).getD 0 σ x y -
        (B.sample history (LogSpaceEstimation.lastBudget M (2 * dyadicSlack m 0) B.slack
          (B.sampleScale r bin)) t r bin).getD 0 σ x y)).sum := by
  induction j with
  | zero => simp only [Nat.zero_add, sum_range_one, decodedGroupInput]
  | succ j ih =>
    rw [sum_range_succ, ih (by omega)]
    unfold decodedGroupInput
    rw [dyadicSlack_succ (by omega : j + 1 < m)]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro bin _
    ring

omit [Fact P.Prime] in
/-- At the actual horizon the initial coarse budget is zero for every scale. -/
theorem raw_coarse_budget_zero (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) :
    LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0)
      B.slack (B.sampleScale r bin) = 0 := by
  have hp : M < 2 ^ (Nat.log2 M + 1) := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) M
  simp only [dyadicSlack, Nat.add_sub_cancel, Nat.pow_succ] at hp ⊢
  unfold LogSpaceEstimation.lastBudget
  omega

/-- Conditional mean of a literal executed RAW prefix, after stationarity and signed
cancellation. Only positive unequal endpoint calls need be supplied. The coarse
boundary is proved zero, not assumed to match a canonical sample. -/
theorem raw_prefix_mean
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays t,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f t r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c t r bin = some C))
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r = some (F i)) ∧
      B.raw history M t r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), F i σ x y) ∧
      ∀ x y, rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => ((B.rays t).map fun bin =>
          (B.sample history (LogSpaceEstimation.lastBudget M
            (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
              t r bin).getD 0 σ x y).sum) x y := by
  let F := fun i => (B.completedGroup history M
    (dyadicSlack (Nat.log2 M + 1) i) t r).getD 0
  have hF (i : ℕ) (hi : i < Nat.log2 M + 1) :=
    B.completedGroup_mean history M (dyadicSlack (Nat.log2 M + 1) i) t r
      s u hsu ks ku ss su hs hu (hcalls i hi)
  have he (i : ℕ) (hi : i < Nat.log2 M + 1) :
      B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r = some (F i) := by
    obtain ⟨A, hA, _⟩ := hF i hi
    simp only [F, hA, Option.getD_some]
  refine ⟨F, he, ?_, ?_⟩
  · have hm : (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r) =
        some ((List.range (Nat.log2 M + 1)).map F) := by
      apply List.mapM_eq_some_iff_forall₂.mpr
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact fun i hi => he i (List.mem_range.mp hi)
    rw [raw, hm]
    simp only [bind, Option.bind_some]
    congr 1
    funext σ x y
    simp only [List.map_map, Function.comp_def]
    rfl
  · intro x y
    change (𝔼 σ ∈ _, ∑ i ∈ range (j + 1), F i σ x y) = _
    rw [expect_sum_comm]
    have hm (i : ℕ) (hi : i ∈ range (j + 1)) : rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su)) (F i) x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) i) t r) x y := by
      have hi' : i < Nat.log2 M + 1 := (mem_range.mp hi).trans_le (by omega)
      obtain ⟨A, hA, hmean⟩ := hF i hi'
      simpa only [F, hA, Option.getD_some] using hmean x y
    change (∑ i ∈ range (j + 1), rowSliceMean _ _ (F i) x y) = _
    rw [sum_congr rfl hm]
    simp only [rowSliceMean, ← expect_sum_comm]
    simp_rw [B.decodedGroupInput_sum history M (Nat.log2 M + 1) j hj,
      B.raw_coarse_budget_zero M r, B.sample_zero history t r, Option.getD_some,
      Pi.zero_apply, Matrix.zero_apply, sub_zero]

/-- Exact signed deficit of an executed prefix against any reference rays and target.
At omitted or exhausted scales the deficit is minus the whole canonical ray, not an
accuracy claim for a fictitious zero-budget child. The last term is the remaining
canonical coverage/target gap; no such deficit is discarded or paid here. -/
theorem raw_prefix_signed_deficit
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays t,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f t r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c t r bin = some C))
    (j : ℕ) (hj : j < Nat.log2 M + 1)
    (canonical : Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) :
    ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r = some (F i)) ∧
      B.raw history M t r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), F i σ x y) ∧
      ∀ x y, rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y - G x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => ((B.rays t).map fun bin =>
          if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
              B.slack (B.sampleScale r bin) = 0 then -canonical bin σ x y else
            (B.sample history (LogSpaceEstimation.lastBudget M
              (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
              t r bin).getD 0 σ x y - canonical bin σ x y).sum) x y +
        (rowSliceMean
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y u (side P ku) (CopyPadding.identifier B.padding su))
          (fun σ x y => ((B.rays t).map fun bin => canonical bin σ x y).sum) x y - G x y) := by
  obtain ⟨F, hF, hraw, hm⟩ := B.raw_prefix_mean history M t r
    s u hsu ks ku ss su hs hu hcalls j hj
  refine ⟨F, hF, hraw, ?_⟩
  intro x y
  rw [hm]
  have he (σ : Environment P 3) :
      ((B.rays t).map fun bin =>
        (B.sample history (LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
          t r bin).getD 0 σ x y).sum =
      ((B.rays t).map fun bin =>
        if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r bin) = 0 then -canonical bin σ x y else
          (B.sample history (LogSpaceEstimation.lastBudget M
            (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
            t r bin).getD 0 σ x y - canonical bin σ x y).sum +
      ((B.rays t).map fun bin => canonical bin σ x y).sum := by
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro bin _
    split_ifs with hz
    · simp only [hz, B.sample_zero history t r bin, Option.getD_some,
        Pi.zero_apply, Matrix.zero_apply, neg_add_cancel]
    · ring
  unfold rowSliceMean
  simp_rw [he]
  rw [expect_add_distrib]
  ring

omit [Fact P.Prime] in
/-- The final positive-ray budget is literally the finite-input bin budget. -/
theorem raw_positive_budget (M i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    LogSpaceEstimation.lastBudget M 1 B.slack (B.sampleScale r (some i)) =
      B.binBudget M i r := rfl

omit [Fact P.Prime] in
/-- The single negative ray has zero scale, because the midpoint rate is the
terminal rate. No equality of positive and negative budgets is asserted. -/
theorem raw_negative_budget (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    LogSpaceEstimation.lastBudget M 1 B.slack (B.sampleScale r none) =
      B.childBudget M := by
  by_cases ht : r.terminal.rate = 0
  · simp [sampleScale, midpoint, ht, childBudget]
  · simp only [sampleScale, Option.map_none, Option.getD_none, midpoint, div_self ht,
      Real.logb_one, Int.floor_zero, childBudget]

/-- Surviving RAW endpoints assemble exactly the finite-input program when every
retained budget is positive. Exhausted endpoints require a separate deficit estimate;
this theorem does not turn calls at budget zero into zero-valued children. -/
theorem finiteInput_residual_decoded
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hlive : ∀ i ∈ B.bins, 0 < B.binBudget M i r) (hnlive : 0 < B.childBudget M)
    (hp : ∀ i ∈ B.bins, ∃ A, B.positiveSample history (B.binBudget M i r) i .residual r =
      some A)
    (hn : ∃ A, row history (B.childBudget M)
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ = some A) :
    B.finiteInput history M .residual r = some (fun σ x y =>
      ((B.rays .residual).map fun bin =>
        (B.sample history (LogSpaceEstimation.lastBudget M 1 B.slack
          (B.sampleScale r bin)) .residual r bin).getD 0 σ x y).sum) := by
  let positives := B.bins.toList.map fun i =>
    (B.positiveSample history (B.binBudget M i r) i .residual r).getD 0
  have hpos : B.bins.toList.mapM (fun i =>
      B.positiveSample history (B.binBudget M i r) i .residual r) = some positives := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro i hi
    obtain ⟨A, hA⟩ := hp i (mem_toList.mp hi)
    simp only [hA, Option.getD_some]
  obtain ⟨N, hN⟩ := hn
  rw [finiteInput, hpos]
  simp only [bind, Option.bind_some, hN, pure]
  congr 1
  funext σ x y
  simp only [rays, List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  rw [B.raw_negative_budget M r]
  simp only [sample, Nat.ne_of_gt hnlive, ↓reduceIte, hN, pure]
  change (positives.map (fun A => A σ x y)).sum - _ = _ + -_ * _ * _
  rw [sub_eq_add_neg]
  congr 1
  · simp only [positives, List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    rw [B.raw_positive_budget M i r]
    simp only [Nat.ne_of_gt (hlive i (mem_toList.mp hi)), ↓reduceIte]
  · ring

/-- The conditional mean of executed RAW equals the finite-input mean at its literal
surviving budgets. Common group walks are removed by stationarity before cancellation.
The final-budget positivity guard is explicit and stronger than parent activity. -/
theorem raw_residual_mean_finiteInput
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (hlive : ∀ i ∈ B.bins, 0 < B.binBudget M i r) (hnlive : 0 < B.childBudget M)
    (hp : ∀ i ∈ B.bins, ∃ A, B.positiveSample history (B.binBudget M i r) i .residual r =
      some A)
    (hn : ∃ A, row history (B.childBudget M)
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ = some A)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.finiteInput history M .residual r = some A) :
    ∃ R, B.raw history M .residual r = some R ∧ ∀ x y,
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su)) R x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su)) A x y := by
  obtain ⟨F, _, hraw, hmean⟩ := B.raw_prefix_mean history M .residual r
    s u hsu ks ku ss su hs hu hcalls (Nat.log2 M) (by omega)
  refine ⟨_, hraw, ?_⟩
  have he := Option.some.inj (hA.symm.trans
    (B.finiteInput_residual_decoded history M r hlive hnlive hp hn))
  intro x y
  rw [hmean, dyadicSlack_last, ← he]

omit [Fact P.Prime] in
/-- For any finite retained horizon, all final endpoint budgets are positive at
sufficiently large parent budgets. This does not assert activity of any child request. -/
theorem raw_endpoint_budgets_eventually_pos
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (∀ i ∈ B.bins, 0 < B.binBudget M i r) ∧ 0 < B.childBudget M := by
  let C := ∑ i ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
    (B.sampleScale r (some i))
  refine ⟨max 1 (max B.slack C) + 1, ?_⟩
  intro M hM
  have h1 : 1 < M := lt_of_lt_of_le (by omega) hM
  have hs : B.slack < M := lt_of_lt_of_le (by omega) hM
  constructor
  · intro i hi
    have hiC : LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale r (some i)) ≤ C := by
      dsimp only [C]
      exact single_le_sum (f := fun i => LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale r (some i))) (fun _ _ => Nat.zero_le _) hi
    rw [← B.raw_positive_budget M i r]
    unfold LogSpaceEstimation.lastBudget
    omega
  · unfold childBudget LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff
    norm_num only [Int.natAbs_zero, zero_add, mul_one]
    omega

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
