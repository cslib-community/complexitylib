/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyApproximateHistory

/-!
# Executed finite residual product transport

Connect the literal `BudgetData.finiteInput` program, with distinct per-bin and negative
budgets, to `HierarchyTask.conditionalChildCost_le_of_root_budgets`. That existing theorem
already performs the coupled product split, joint-mask integration and reset-source root
payment; no second finite product inequality is needed. The negative request is subtracted
once, outside the bin sum. The canonical family may be the genuine `canonicalRequestChild`.

These original execution bridges retain the conservative explicit width, bin and density
costs of that API. They do not allocate those costs from `requestPrecision`, construct
successful later correction calls, or modify production leaves.
-/

public section
noncomputable section
open Finset Cslib
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Literal compressed direct and reset-right calls, together with the evaluated nonzero
correction constructor, feed the existing product error theorem. The left range follows
from successful normalization; the right canonical range follows from the genuine dense
recipe. Its source remains the midpoint, including the original suffix. No accuracy is
inferred from any of these three execution premises. -/
theorem positiveSample_residual_compressed
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (D L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 bin .residual r.source (midpoint r)
        r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hl :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 bin .residual r.source (midpoint r)
        r.terminal (B.binRate bin)
      B.evaluate m Q.left = some (.row L))
    (hr :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 bin .residual r.source (midpoint r)
        r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 bin .residual r.source (midpoint r)
      r.terminal (B.binRate bin)
    let child := fun q => if q = Q.direct then D else if q = Q.left then L else R
    let canonical := canonicalRequestChild HP B.padding id B.base (B.cutoff bin)
      (B.auxiliary bin) HP.ρ HP.K
    ∃ A, B.positiveSample
      (fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none)
      m bin .residual r = some A ∧ ∀ σ x y,
      |A σ x y - HierarchyTask.rawPositiveSample (channels B.padding) 0 bin .residual
        r.source (midpoint r) r.terminal (B.binRate bin) (fun q => canonical q σ) x y| ≤
      HierarchyTask.positiveChildError (channels B.padding) 0 bin .residual
        r.source (midpoint r) r.terminal (B.binRate bin)
        (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * B.binCap)
        (fun q => child q σ) (fun q => canonical q σ) x y := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 bin .residual r.source (midpoint r)
    r.terminal (B.binRate bin)
  let child := fun q => if q = Q.direct then D else if q = Q.left then L else R
  let history := fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none
  have hdl : Q.direct ≠ Q.left := by
    intro h
    have ht := congrArg HierarchyTask.Request.task h
    simp only [Q, HierarchyTask.rawRequests, HierarchyTask.correctionAtomTask_last HP.k_pos]
      at ht
    contradiction
  have hrl : Q.right ≠ Q.left := by
    intro h
    have ht := congrArg HierarchyTask.Request.task h
    simp only [Q, HierarchyTask.rawRequests, HierarchyTask.correctionAtomTask_last HP.k_pos]
      at ht
    contradiction
  have hdr : Q.right ≠ Q.direct := by
    intro h
    have ht := congrArg (fun q => q.source.role) h
    exact (midpointRole_distinct r.source.role r.terminal.role).1 ht.symm
  have hrows : ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
      row history m q = some (child q) := by
    intro q hq
    have hh : row history m q = row (B.compressedHistory exponent ζ floor) m q := by
      simp only [row, history, hm, ↓reduceIte]
    rw [hh]
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · change row (B.compressedHistory exponent ζ floor) m Q.direct = some (child Q.direct)
      simp only [child, ↓reduceIte]
      rw [B.compressedHistory_dense exponent ζ floor m bin Q.direct rfl, hd]
    · have ht : Q.left.task = .row 0 (.normalized ⟨HP.k - 1,
          Nat.sub_lt HP.k_pos (by decide)⟩) := by
        simp only [Q, HierarchyTask.rawRequests,
          HierarchyTask.correctionAtomTask_last HP.k_pos]
      have he : child Q.left = L := by simp only [child, Ne.symm hdl, ↓reduceIte]
      change row (B.compressedHistory exponent ζ floor) m Q.left = some (child Q.left)
      rw [he]
      have hh : B.compressedHistory exponent ζ floor m Q.left = some (.row L) := by
        simpa only [compressedHistory, ht] using hl
      simp only [row, hh, Option.bind_some, BudgetValue.row?]
    · change row (B.compressedHistory exponent ζ floor) m Q.right = some (child Q.right)
      simp only [child, hdr, hrl, ↓reduceIte]
      rw [B.compressedHistory_dense exponent ζ floor m bin Q.right rfl, hr]
  have hleft := B.evaluate_normalized_bounds m false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hl
  refine ⟨_, B.positiveSample_of_rows history m bin .residual r child hrows, ?_⟩
  intro σ x y
  apply HierarchyTask.rawPositiveSample_sub_le
  · intro z
    have hb := hleft.1 σ x z
    change |child Q.left σ x z| ≤ _
    simpa only [child, Ne.symm hdl, ↓reduceIte, abs_of_nonneg hb.1] using hb.2
  · intro z
    have hb := normalizedRequest_mem_Icc HP B.padding Q.right (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) (fun _ => B.base)
      (densePreparation B.padding id Q.right (B.auxiliary bin) HP.ρ HP.K B.base) σ z y
    change |normalizedRequest B.padding id Q.right (B.cutoff bin) HP.ρ HP.K
      (fun _ => B.base)
      (densePreparation B.padding id Q.right (B.auxiliary bin) HP.ρ HP.K B.base) σ z y| ≤ _
    exact (abs_of_nonneg hb.1).trans_le hb.2

/-- The literal finite residual executes its three requests at each actual bin budget,
and its single negative at `childBudget M`. The supplied table at bin zero must agree
with that negative call, independently of the positive bin-zero budget. -/
theorem finiteInput_residual_of_rows
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ i ∈ B.bins, ∀ q ∈
      ({(HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).direct,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).left,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).right} : Finset _),
      row history (B.binBudget M i r) q = some (child i q))
    (hn : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row history (B.childBudget M) q = some (child 0 q)) :
    B.finiteInput history M .residual r = some (fun σ x y =>
      (∑ i ∈ B.bins, HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i) (fun q => child i q σ) x y) -
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y) := by
  let A := fun i σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i) (fun q => child i q σ) x y
  have hp : B.bins.toList.mapM
      (fun i => B.positiveSample history (B.binBudget M i r) i .residual r) =
      some (B.bins.toList.map A) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro i hi
    exact B.positiveSample_of_rows history _ i .residual r (child i)
      (hc i (Finset.mem_toList.mp hi))
  unfold finiteInput
  rw [hp]
  simp only [bind]
  rw [hn]
  simp only [Option.bind_some, pure]
  congr 1
  funext σ x y
  simp only [List.map_map, Function.comp_def, A, Finset.sum_map_toList,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests]

/-- Actual successful finite residual means consume the existing own-request scalar
root allocation, including both product errors and the direct error. No independence,
approximate canonical support, or parent accuracy is assumed. This is a conditional
execution/payment theorem; the explicit allocation is not a proved precision schedule. -/
theorem finiteInput_residual_root_payment
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child canonical : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ i ∈ B.bins, ∀ q ∈
      ({(HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).direct,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).left,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).right} : Finset _),
      row history (B.binBudget M i r) q = some (child i q))
    (hn : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row history (B.childBudget M) q = some (child 0 q))
    {CA CB cap δ : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hs : 0 < r.source.rate) (hδ : 0 ≤ δ)
    (hsource : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → 0 < q.source.rate)
    (hrange : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → ∀ σ x y,
      child i q σ x y ∈ Set.Icc 0 cap ∧ canonical i q σ x y ∈ Set.Icc 0 cap)
    (hoff : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → ∀ σ x y,
      ¬ q.usage.retains (channels B.padding) σ y →
      child i q σ x y = 0 ∧ canonical i q σ x y = 0)
    (hl : ∀ i ∈ B.bins, ∀ σ x z,
      |child i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).left σ x z| ≤ CA)
    (hr : ∀ i ∈ B.bins, ∀ σ z y,
      |canonical i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).right σ z y| ≤ CB) :
    let scale := (P : ℝ) ^ 2 / (P * r.source.rate) *
      HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P) (channels B.padding)
        B.bins 0 r.source (midpoint r) r.terminal B.binRate CA CB
    (∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate →
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y) (child i q) (canonical i q) ≤
      (δ / (1 + scale)) /
        (1 + (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 * (P * q.source.rate)) /
        (1 + #(HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
          r.source (midpoint r) r.terminal B.binRate))) →
    ∃ executed, B.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => executed σ x y -
            ((∑ i ∈ B.bins, HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
              r.source (midpoint r) r.terminal (B.binRate i) (fun q => canonical i q σ) x y) -
            HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
              r.source (midpoint r) r.terminal (B.binRate 0)
                (fun q => canonical 0 q σ) x y)) x y) ≤ δ := by
  intro scale hroot
  let E := fun i σ q => child i q σ
  let C := fun i σ q => canonical i q σ
  have hp := HierarchyTask.conditionalChildCost_le_of_root_budgets (channels B.padding)
    B.bins 0 r.source (midpoint r) r.terminal B.binRate (N := (P : ℝ)) hCA hCB
    (by exact_mod_cast (Fact.out : P.Prime).pos) hs hδ E C hsource hrange hoff
  simp only [ZMod.card] at hp
  specialize hp hroot
  refine ⟨_, B.finiteInput_residual_of_rows history M r child hc hn, ?_⟩
  apply le_trans ?_ hp
  apply (rowNormPow_le_mul (mul_nonneg (Nat.cast_nonneg P) hs.le) (c := 1) ?_).trans_eq
    (one_mul _)
  intro σ x y _ _
  have hc := HierarchyTask.residual_bins_sub_le (channels B.padding)
    ({τ | r.source.retains (channels B.padding) τ x ∧
      r.terminal.retains (channels B.padding) τ y} : Finset _) B.bins 0
    r.source (midpoint r) r.terminal B.binRate (fun _ => CB) CA E C x y
    (fun i hi τ _ z => hl i hi τ x z) (fun i hi τ _ z => hr i hi τ z y)
  simp only [rowSliceMean, expect_sub_distrib,
    HierarchyTask.conditionalChildCost, E, C] at hc ⊢
  rw [one_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) (hc.trans (le_abs_self _)) 4

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
