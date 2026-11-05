/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyNoiseAllocation
public import Complexity.Foundations.Probability.RootMetric.RelativeError

/-!
# Relative endpoint moments before summing RAW rays

Keep the decoder's fixed pair denominator inside each literal endpoint moment,
then apply Minkowski and conditional centering. This avoids separating the
reciprocal denominator from the errors. The resulting sufficient payment still
requires an own-request precision allocation; it is not a recursive IH theorem.

## Main results

* `residualEndpointRootSum`: both literal positive endpoint allowances.
* `negativeSample_residual_relative_fourth_le`: pairwise once-negative conversion.
* `rawRelativeNoiseBudget_transported_le_of_relative_endpoints`: production budget consumer.
* `residualTransportedGroupInput_centered_relative_minkowski_le`: both relative
  endpoint root costs, without a reciprocal-denominator sup norm or bin count.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Both positive literal endpoint root allowances, with exhausted endpoints zero. -/
@[expose] def residualEndpointRootSum (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (e : ℕ → Option ℕ → ℝ) : ℝ :=
  ∑ bin ∈ insert none (B.bins.image some),
    ((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 then 0
      else e (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin) +
    (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 then 0
      else e (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin))

omit [Fact P.Prime] in
/-- Full exhaustion removes all endpoint costs without any IH, even if the
allowances are nonzero. This holds for every listed bin and every denominator. -/
theorem residualEndpointRootSum_eq_zero_of_le (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (e : ℕ → Option ℕ → ℝ)
    (hd : M ≤ d) : B.residualEndpointRootSum M d r e = 0 := by
  have hf (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp [residualEndpointRootSum, hf, hc]

/-- Relative endpoint errors are summed before centering. Both actual positive
budgets are paid; zero endpoints need no accuracy. The denominator is fixed by
the pair, so division commutes with its conditional mean even at a zero divisor. -/
theorem residualTransportedGroupInput_centered_relative_minkowski_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (X Y : Environment P 3 → ZMod P → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] (hNu : 0 ≤ (P : ℝ) * r.source.rate)
    (den : Matrix (ZMod P) (ZMod P) ℝ) (e : ℕ → Option ℕ → ℝ)
    (he0 : ∀ m bin, 0 ≤ e m bin)
    (he : ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) →
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => ((B.sample history m .residual r bin).getD 0 σ x y -
          B.residualCanonicalRay r bin σ x y) / den x y) ≤ e m bin ^ 4) :
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      (B.residualTransportedGroupInput history M d r σ x y -
        rowSliceMean X Y (B.residualTransportedGroupInput history M d r) x y) / den x y) ≤
      16 * B.residualEndpointRootSum M d r e ^ 4 := by
  unfold residualEndpointRootSum
  let S := insert none (B.bins.image some)
  let E := fun m bin σ x y => ((B.sample history m .residual r bin).getD 0 σ x y -
    (if m = 0 then 0 else B.residualCanonicalRay r bin σ x y)) / den x y
  let a := fun m bin => if m = 0 then 0 else e m bin
  let f := fun bin => LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
  let c := fun bin => LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  have hS (bin : Option ℕ) : bin ∈ S ↔ bin ∈ B.rays .residual := by
    simp only [S, rays, mem_insert, mem_image, List.mem_append, List.mem_map,
      mem_toList, List.mem_singleton]
    exact or_comm
  have ha (m : ℕ) (bin : Option ℕ) : 0 ≤ a m bin := by
    dsimp only [a]; split_ifs <;> first | positivity | exact he0 _ _
  have hE (m : ℕ) (bin : Option ℕ) (hb : bin ∈ S)
      (hmc : m = f bin ∨ m = c bin) :
      rowNormPow 4 P r.source.rate X Y (E m bin) ≤ a m bin ^ 4 := by
    by_cases hm : m = 0
    · subst m; simp [E, a, B.sample_zero, rowNormPow]
    · simpa only [E, a, hm, ↓reduceIte] using he bin ((hS bin).mp hb) m (by omega) hmc
  have hpair (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y) ≤
          (a (f bin) bin + a (c bin) bin) ^ 4 := by
    have h := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y
      (univ : Finset Bool)
      (fun b => if b then E (f bin) bin else -E (c bin) bin)
      (fun _ => 1) (fun b => if b then a (f bin) bin else a (c bin) bin)
      (by intros; norm_num) (by intro b _; cases b <;> exact ha _ _)
      (by
        intro b _; cases b
        · simpa only [Bool.false_eq_true, ↓reduceIte, rowNormPow, Pi.neg_apply, abs_neg]
            using hE (c bin) bin hb (Or.inr rfl)
        · exact hE (f bin) bin hb (Or.inl rfl))
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, Pi.neg_apply,
      sub_eq_add_neg, add_comm] using h
  have hsum (v : Option ℕ → ℝ) :
      ((B.rays .residual).map v).sum = ∑ bin ∈ S, v bin := by
    rw [show S = _ from rfl, sum_insert (by simp),
      sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_map_toList]; ring
  have hin : (fun σ x y => B.residualTransportedGroupInput history M d r σ x y /
      den x y) =
      fun σ x y => ∑ bin ∈ S, (E (f bin) bin σ x y - E (c bin) bin σ x y) := by
    funext σ x y
    change (((B.rays .residual).map _).sum / den x y) = _
    rw [hsum, Finset.sum_div]
    apply sum_congr rfl
    intro bin _
    dsimp only [E, f, c]
    ring
  have hi := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y S
    (fun bin σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y)
    (fun _ => 1) (fun bin => a (f bin) bin + a (c bin) bin)
    (by intros; norm_num) (by intro bin _; exact add_nonneg (ha _ _) (ha _ _)) hpair
  simp only [one_mul] at hi
  rw [← hin] at hi
  have hc := rowNormPow_centered_sub_fourth_le hNu X Y
    (fun σ x y => B.residualTransportedGroupInput history M d r σ x y / den x y) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero,
    ← expect_div, ← sub_div] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

/-- Executed once-negative error with the range and decoder denominator compared
at the same endpoint pair. The reference is the genuine canonical correction,
and the rooted error is on that correction's own usage. The coefficient is an
explicit unpaid premise, rather than a uniform recursive allocation claim. -/
theorem negativeSample_residual_relative_fourth_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (hm : 0 < m) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (Y : Environment P 3 → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (den cap : Matrix (ZMod P) (ZMod P) ℝ) (K : ℝ) (hs : 0 ≤ (P : ℝ) * r.source.rate)
    (hrow : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row history m q = some A)
    (hbound : ∀ σ x y, A σ x y ∈ Set.Icc 0 (cap x y) ∧
      B.residualCanonicalChild 0
        ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
          {r.terminal with rate := (midpoint r).rate},
          {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩ σ x y ∈
            Set.Icc 0 (cap x y))
    (hoff : ∀ σ x y,
      ¬ ({r.terminal with rate := min r.terminal.rate (midpoint r).rate}).retains
        (channels B.padding) σ y → A σ x y = B.residualCanonicalChild 0
          ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
            {r.terminal with rate := (midpoint r).rate},
            {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩ σ x y)
    (hcoef : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      ∀ x y, |(-(midpoint r).rate *
        HierarchyTask.usageRatio (channels B.padding) r.terminal q y) / den x y| *
          (4 * (cap x y) ^ ((3 : ℝ) / 4)) ≤ K) :
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x) Y
      (fun σ x y => ((B.sample history m .residual r none).getD 0 σ x y -
        B.residualCanonicalRay r none σ x y) / den x y) ≤
      K ^ 4 * rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        A (B.residualCanonicalChild 0 q) := by
  dsimp only
  rw [sample, ite_eq_right (by omega)]
  dsimp only
  rw [hrow]
  simp only [bind, pure, Option.bind_some, Option.getD_some, residualCanonicalRay,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests, Pi.neg_apply]
  convert rowNormPow_relative_sub_le_rootDistPow hs
    (fun σ x => r.source.retains (channels B.padding) σ x) Y
    (fun σ y => ({r.terminal with rate := min r.terminal.rate (midpoint r).rate}).retains
      (channels B.padding) σ y) A _ _ den cap
    (fun σ x y => (hbound σ x y).1) (fun σ x y => (hbound σ x y).2) hoff hcoef using 1
  congr 1
  funext σ x y
  ring

/-- Feed relative endpoint allowances to the actual transported-noise budget.
The original `steps`, pair densities, source normalization and prefix cube are
unchanged. Endpoint moment and root-sum allocation remain separate obligations. -/
theorem rawRelativeNoiseBudget_transported_le_of_relative_endpoints
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ)
    (e : ℕ → ℕ → Option ℕ → ℝ) (he0 : ∀ i m bin, 0 ≤ e i m bin)
    (he : ∀ i ∈ range j, ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
        B.slack (B.sampleScale r bin) ∨
      m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) i)
        B.slack (B.sampleScale r bin)) →
      rowNormPow 4 P r.source.rate
        (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
        (NormalizedMoments.retainedMask t (side P ku) B.padding su)
        (fun σ x y => ((B.sample history m .residual r bin).getD 0 σ x y -
          B.residualCanonicalRay r bin σ x y) / (rate ku + G x y)) ≤ e i m bin ^ 4) :
    B.rawRelativeNoiseBudget M r s t hst ks ku ss su
      (fun i => B.residualTransportedGroupInput history M
        (dyadicSlack (Nat.log2 M + 1) i) r) G j ≤
      (j : ℝ) ^ 3 * ∑ i ∈ range j,
        ‖fun xy : ZMod P × ZMod P => 2 *
          (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
            (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
            xy.1 xy.2).spectralExpansion ^
              (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))‖ *
          (16 * B.residualEndpointRootSum M (dyadicSlack (Nat.log2 M + 1) i) r (e i) ^ 4) := by
  apply B.rawRelativeNoiseBudget_le_of_centered_fourth
    M r s t hst ks ku ss su hs _ G j
  intro i hi
  apply B.residualTransportedGroupInput_centered_relative_minkowski_le history M _ r
    _ _ (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le)
    (fun x y => rate ku + G x y) (e i) (he0 i)
  exact he i hi

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
