/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawMeanSchedule
public import Complexity.Foundations.Probability.RootMetric.WeightedError

/-!
# Conditional noise of literal residual RAW groups

The input to each production walk is the sum of its actual paired rays, including
one negative correction ray. No canonical-support or independence assumption is made.
The source and usage graph, last budgets and `BudgetData.steps` are unchanged.
The resulting prefix estimate retains the fixed-pair denominator and the centered
conditional input moment. In particular it does not replace the group mean by a
canonical mean or apply deterministic heavy-event rarity to noise.

This original finite consumer leaves a precise analytic obligation: pay the sum of
centered input moments in `rawRelativeNoiseBudget` uniformly from positive-endpoint
own-request child IH. Successful paired calls are separate explicit premises; this
module does not construct joint availability, derive that IH payment, choose a uniform
charge, or pay the full `initialSeparatedReserve`. Initial semantic endpoint
cancellation cannot be assumed for budget-dependent residual children. List execution
and correlated-prefix proof patterns adapt Samuel Schlesinger’s compression APIs.

## Main results

* `completedGroup_residual_of_paired`: production execution from literal paired rays.
* `rawFirstPrefixes_relative_noise`: correlated conditional prefix noise.
* `rawFirstPrefixes_actualNoiseEntry`: the actual first-channel decoder statistic.
* `rawFirstPrefixes_decoded_noise`: literal positive-only endpoint availability.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (B : BudgetData HP P)

/-- Residual rays always include the once-negative correction, even with no positive
bins. Success is required only of the actual paired calls, which already handle equal
and zero endpoints without child calls. General-product children remain inside them. -/
theorem completedGroup_residual_of_paired
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : ∀ bin ∈ B.rays .residual,
      B.pairedSample history M d .residual r bin = some (A bin)) :
    B.completedGroup history M d .residual r = some (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r d)
      (fun σ x y => ((B.rays .residual).map (fun bin => A bin σ x y)).sum)) := by
  have hm : (B.rays .residual).mapM (B.pairedSample history M d .residual r) =
      some ((B.rays .residual).map A) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact hA
  have he : (B.rays .residual).isEmpty = false := by simp [rays]
  unfold completedGroup
  rw [he]
  simp only [Bool.false_eq_true, ↓reduceIte, hm, bind, Option.bind_some,
    List.map_map, Function.comp_def]
  exact B.complete_grid M r s t hst ks ku ss su hs hu _ d

/-- The exact conditional input-moment obligation for a prefix of actual residual
walks. All paired amplitudes, product correlations and the negative sign stay in `A`.
The prefix cube pays arbitrary correlation; no rarity or rate relaxation is used. -/
@[expose] def rawRelativeNoiseBudget (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (A : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) : ℝ :=
  let Xs := retainedMask s (side P ks) B.padding ss
  let Yu := retainedMask t (side P ku) B.padding su
  let graphs := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  (j : ℝ) ^ 3 * ∑ i ∈ range j,
    ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y,
      (({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)).dens : ℝ) *
        (2 * (graphs x y).spectralExpansion ^ (2 * B.steps M r
          (dyadicSlack (Nat.log2 M + 1) i)) *
          𝔼 σ ∈ ({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)),
            |(A i σ x y - rowSliceMean Xs Yu (A i) x y) / (rate ku + G x y)| ^ 4)

/-- Actual residual prefix noise from successful literal paired samples. The input
family is constrained by execution, rather than by an assumed output/noise bound.
The empty prefix is included. The retained obligation is an input moment, not an IH
or a claim of fixed-constant allocation over unbounded rate/bin families. -/
theorem rawFirstPrefixes_relative_noise
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : ℕ → Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (j : ℕ) (hj : j ≤ Nat.log2 M + 1)
    (hA : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) i) .residual r bin =
        some (A i bin))
    (G : Matrix (ZMod P) (ZMod P) ℝ) :
    let Xs := retainedMask s (side P ks) B.padding ss
    let Yu := retainedMask t (side P ku) B.padding su
    let F := B.rawFirstPrefixes history M .residual r
    rowNormPow 4 P r.source.rate Xs Yu
      (fun σ x y => (F j σ x y - rowSliceMean Xs Yu (F j) x y) / (rate ku + G x y)) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i σ x y => ((B.rays .residual).map (fun bin => A i bin σ x y)).sum) G j := by
  dsimp only
  let input := fun i σ x y => ((B.rays .residual).map (fun bin => A i bin σ x y)).sum
  let Xs := retainedMask s (side P ks) B.padding ss
  let Yu := retainedMask t (side P ku) B.padding su
  let graphs := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  let W := fun i => conditionalWalk Xs Yu graphs
    (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) i)) (input i)
  have hF : B.rawFirstPrefixes history M .residual r j =
      fun σ x y => ∑ i ∈ range j, W i σ x y := by
    funext σ x y
    apply sum_congr rfl
    intro i hi
    rw [B.completedGroup_residual_of_paired history M _ r s t hst ks ku ss su hs hu
      (A i) (hA i ((mem_range.mp hi).trans_le hj)), Option.getD_some]
    rfl
  have hmean (x y : ZMod P) : rowSliceMean Xs Yu
      (B.rawFirstPrefixes history M .residual r j) x y =
      ∑ i ∈ range j, rowSliceMean Xs Yu (input i) x y := by
    rw [hF]
    unfold rowSliceMean
    rw [expect_sum_comm]
    apply sum_congr rfl
    intro i _
    exact rowSliceMean_conditionalWalk _ _ _ _ _ x y
  change rowNormPow 4 P r.source.rate Xs Yu (fun σ x y =>
    (B.rawFirstPrefixes history M .residual r j σ x y -
      rowSliceMean Xs Yu (B.rawFirstPrefixes history M .residual r j) x y) /
        (rate ku + G x y)) ≤ _
  simp_rw [hmean]
  rw [hF]
  simp_rw [← sum_sub_distrib, sum_div]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  apply (rowNormPow_sum_fourth_le _ hNu _ _ _).trans
  simp only [card_range, rawRelativeNoiseBudget]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i _
  exact rowNormPow_conditionalWalk_div_le_sum _ _ hNu _ _ _ _

/-- Full-terminal first-channel decoder noise, with arbitrary second increments.
Its denominator-retaining payment is the actual paired-input conditional budget.
Completion availability and payment of that budget from child IH remain separate. -/
theorem rawFirstPrefixes_actualNoiseEntry
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal)
    (A : ℕ → Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1)
    (hA : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) j) .residual r bin =
        some (A j bin))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    rowNormPow 4 P r.source.rate
      (retainedMask s (side P ks) B.padding ss) (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 i) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ka ss st
        (fun j σ x y => ((B.rays .residual).map (fun bin => A j bin σ x y)).sum) G (i + 1) := by
  rw [actualNoiseEntry_first_prefix_row_eq s t (side P ks) (side P ka) (side P ka)
    B.padding ss st _ ka G hG second 0 (by intros; rfl)]
  simp only [rowSliceMean, ← expect_div, ← sub_div]
  exact B.rawFirstPrefixes_relative_noise history M r s t hst ks ka ss st hs
    (husage.trans ht) A (i + 1) (by omega) hA G

/-- The same decoder payment expressed only with literal endpoint availability.
Equal endpoints make no calls; zero endpoints need no positive-budget success.
`decodedGroupInput` retains the once-negative ray and both real last budgets.
Own-request accuracy is deliberately not inferred from this availability premise. -/
theorem rawFirstPrefixes_decoded_noise
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal)
    (hcalls : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) j
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate
      (retainedMask s (side P ks) B.padding ss) (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 i) ≤
      B.rawRelativeNoiseBudget M r s t hst ks ka ss st
        (fun j => B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) j)
          .residual r) G (i + 1) := by
  let A := fun j bin =>
    (B.sample history (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r bin)) .residual r bin).getD 0 -
    (B.sample history (LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r bin)) .residual r bin).getD 0
  have hA (j : ℕ) (hj : j < Nat.log2 M + 1) (bin : Option ℕ)
      (hb : bin ∈ B.rays .residual) :
      B.pairedSample history M (dyadicSlack (Nat.log2 M + 1) j) .residual r bin =
        some (A j bin) :=
    B.pairedSample_decoded history M _ .residual r bin (hcalls j hj bin hb)
  exact B.rawFirstPrefixes_actualNoiseEntry history M r s t hst ks ka ss st hs ht
    husage A i hi hA G hG second

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
