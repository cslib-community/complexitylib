/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawNoiseSplit
public import Complexity.Foundations.Probability.HierarchyApproximateHistory
public import Complexity.Foundations.Probability.RootMetric.ProductError

/-!
# Unaveraged fourth moments of executed residual endpoints

Rooted own-request errors are converted before taking a conditional mean. The
coupled product theorem retains the midpoint source and its normalization, and
importance weights remain attached to the actual endpoint. These original bounds
are conservative finite transport bounds, not a uniform precision allocation.
The range and support premises must be justified by the actual child gates.
The finite sup norms, product cap and bin-count cube are displayed costs: this
module does not show that one primitive charge pays them before fields and horizons.
No insufficiency of the scalar own-request IH or estimator counterexample follows.

## Main results

* `positiveSample_residual_fourth_le`: executed direct/product unaveraged transport.
* `negativeSample_residual_fourth_le`: once-negative own-usage transport.
* `residualTransportedGroupInput_centered_fourth_le`: both literal endpoint errors.
* `rawRelativeNoiseBudget_le_of_centered_fourth`: production spectral-budget consumer.
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

/-- Executed direct/product endpoint error, before any averaging. The three own
rooted moments remain on their actual request masks; the right one uses midpoint
source normalization. Range/support gates are explicit, and execution is separate.
The reference table can in particular be `residualCanonicalChild`. -/
theorem positiveSample_residual_fourth_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m i : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child canonical : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (Y : Environment P 3 → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (CD CL CR : ℝ) (hCL : 0 ≤ CL) (hCR : 0 ≤ CR)
    (KL KR Kc : ℕ) (hs : 0 < r.source.rate) (hm : 0 < (midpoint r).rate)
    (hrows :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _), row history m q = some (child q))
    (hD :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x y, child Q.direct σ x y ∈ Set.Icc 0 CD ∧
        canonical Q.direct σ x y ∈ Set.Icc 0 CD)
    (hL :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x z, child Q.left σ x z ∈ Set.Icc 0 CL ∧
        canonical Q.left σ x z ∈ Set.Icc 0 CL)
    (hR :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z y, child Q.right σ z y ∈ Set.Icc 0 CR ∧
        canonical Q.right σ z y ∈ Set.Icc 0 CR)
    (hDo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x y, ¬ Q.direct.usage.retains (channels B.padding) σ y →
        child Q.direct σ x y = canonical Q.direct σ x y)
    (hRo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z y, ¬ Q.right.usage.retains (channels B.padding) σ y →
        child Q.right σ z y = 0 ∧ canonical Q.right σ z y = 0)
    (hLo :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x z, ¬ (midpoint r).retains (channels B.padding) σ z →
        child Q.left σ x z = 0 ∧ canonical Q.left σ x z = 0)
    (hK :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x, #{z ∈ ({z | (midpoint r).retains (channels B.padding) σ z} : Finset _) |
        child Q.left σ x z ≠ 0} ≤ KL ∧
        #{z ∈ ({z | (midpoint r).retains (channels B.padding) σ z} : Finset _) |
          canonical Q.left σ x z ≠ 0} ≤ KL)
    (hKr :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z, (midpoint r).retains (channels B.padding) σ z →
        #{y ∈ ({y | Q.right.usage.retains (channels B.padding) σ y} : Finset _) |
          child Q.right σ z y ≠ 0} ≤ KR)
    (hKc :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z, (midpoint r).retains (channels B.padding) σ z →
        #{x ∈ ({x | r.source.retains (channels B.padding) σ x} : Finset _) |
          canonical Q.left σ x z ≠ 0} ≤ Kc) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Z := fun σ z => (midpoint r).retains (channels B.padding) σ z
    let U := fun σ y => Q.right.usage.retains (channels B.padding) σ y
    let wd := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y
    let wp := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.right y * ((midpoint r).rate /
        (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ))
    ∃ A, B.positiveSample history m i .residual r = some A ∧
      rowNormPow 4 P r.source.rate X Y (fun σ x y => A σ x y -
        HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
          r.source (midpoint r) r.terminal (B.binRate i) (fun q => canonical q σ) x y) ≤
      8 * (‖wd‖ ^ 4 * (4 * CD ^ ((3 : ℝ) / 4)) ^ 4 *
        rootDistPow 4 P r.source.rate X
          (fun σ y => Q.direct.usage.retains (channels B.padding) σ y)
          (child Q.direct) (canonical Q.direct) +
        ‖wp‖ ^ 4 * (4 * ((KL : ℝ) * CL * CR) ^ ((3 : ℝ) / 4)) ^ 4 *
          (16384 * (CR * KR * rootDistPow 4 P r.source.rate X Z
            (child Q.left) (canonical Q.left) +
            CL * Kc * ((midpoint r).rate / r.source.rate) *
              rootDistPow 4 P (midpoint r).rate Z U (child Q.right) (canonical Q.right)))) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Z := fun σ z => (midpoint r).retains (channels B.padding) σ z
  let U := fun σ y => Q.right.usage.retains (channels B.padding) σ y
  let wd := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
    r.terminal Q.direct y
  let wp := fun y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
    r.terminal Q.right y * ((midpoint r).rate /
      (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ))
  have hN : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hd := rowNormPow_weighted_sub_le_rootDistPow (mul_pos hN hs).le X Y
    (fun σ y => Q.direct.usage.retains (channels B.padding) σ y)
    (child Q.direct) (canonical Q.direct) wd
    (fun σ x y => (hD σ x y).1) (fun σ x y => (hD σ x y).2) hDo
  have hp := rowNormPow_weighted_product_sub_le_root hN hs hm hCL hCR X Z Y U
    (child Q.left) (canonical Q.left) (child Q.right) (canonical Q.right) wp KL KR Kc
    (fun σ x z => (hL σ x z).1) (fun σ x z => (hL σ x z).2)
    (fun σ z y => (hR σ z y).1) (fun σ z y => (hR σ z y).2)
    (fun σ x => (hK σ x).1) (fun σ x => (hK σ x).2) hKr hKc hRo
  have hz (A : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (ha : ∀ σ x z, ¬ Z σ z → A Q.left σ x z = 0) (σ x y) :
      (∑ z, A Q.left σ x z * A Q.right σ z y) =
        ∑ z ∈ ({z | Z σ z} : Finset _), A Q.left σ x z * A Q.right σ z y := by
    symm
    apply sum_subset (filter_subset _ _)
    intro z _ hz
    rw [ha σ x z (by simpa using hz), zero_mul]
  refine ⟨_, B.positiveSample_of_rows history m i .residual r child hrows, ?_⟩
  have he : (fun σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 i
      .residual r.source (midpoint r) r.terminal (B.binRate i) (fun q => child q σ) x y -
      HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual r.source
        (midpoint r) r.terminal (B.binRate i) (fun q => canonical q σ) x y) =
      (fun σ x y => wd y * (child Q.direct σ x y - canonical Q.direct σ x y) +
        wp y * ((∑ z ∈ ({z | Z σ z} : Finset _), child Q.left σ x z * child Q.right σ z y) -
          ∑ z ∈ ({z | Z σ z} : Finset _), canonical Q.left σ x z * canonical Q.right σ z y)) := by
    funext σ x y
    unfold HierarchyTask.rawPositiveSample
    dsimp only
    rw [hz child (fun σ x z h => (hLo σ x z h).1),
      hz canonical (fun σ x z h => (hLo σ x z h).2)]
    dsimp only [wd, wp, Q]
    ring
  rw [he]
  exact (rowNormPow_add_le (mul_pos hN hs).le _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add hd hp) (by norm_num))

/-- The signed negative endpoint is transported once. Positive-budget execution
and own-usage rooted accuracy are distinct premises. Its original negative sign
is retained in the actual sample and canonical ray. -/
theorem negativeSample_residual_fourth_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (hm : 0 < m) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (Y : Environment P 3 → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (cap : ℝ) (hs : 0 ≤ (P : ℝ) * r.source.rate)
    (hrow : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row history m q = some A)
    (hbound : ∀ σ x y, A σ x y ∈ Set.Icc 0 cap ∧
      B.residualCanonicalChild 0
        ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
          {r.terminal with rate := (midpoint r).rate},
          {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩ σ x y ∈
            Set.Icc 0 cap)
    (hoff : ∀ σ x y,
      ¬ ({r.terminal with rate := min r.terminal.rate (midpoint r).rate}).retains
        (channels B.padding) σ y → A σ x y = B.residualCanonicalChild 0
          ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
            {r.terminal with rate := (midpoint r).rate},
            {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩ σ x y) :
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
    let w := fun y => -(midpoint r).rate *
      HierarchyTask.usageRatio (channels B.padding) r.terminal q y
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x) Y
      (fun σ x y => (B.sample history m .residual r none).getD 0 σ x y -
        B.residualCanonicalRay r none σ x y) ≤
      ‖w‖ ^ 4 * (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 * rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        A (B.residualCanonicalChild 0 q) := by
  dsimp only
  rw [sample, ite_eq_right (by omega)]
  dsimp only
  rw [hrow]
  simp only [bind, pure, Option.bind_some, Option.getD_some, residualCanonicalRay,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests, Pi.neg_apply]
  convert rowNormPow_weighted_sub_le_rootDistPow hs
    (fun σ x => r.source.retains (channels B.padding) σ x) Y
    (fun σ y => ({r.terminal with rate := min r.terminal.rate (midpoint r).rate}).retains
      (channels B.padding) σ y) A _ _
    (fun σ x y => (hbound σ x y).1) (fun σ x y => (hbound σ x y).2) hoff using 1
  congr 1
  funext σ x y
  ring

/-- Both literal endpoint errors pay the transported input's centered relative
fourth moment. Only positive endpoints require a moment allowance; exhausted
endpoints contribute zero. The original pair denominator is retained on the
left and charged explicitly by its finite norm on the right. This finite cost
is not asserted to be paid by a field-independent precision schedule. -/
theorem residualTransportedGroupInput_centered_fourth_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (X Y : Environment P 3 → ZMod P → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] (hNu : 0 ≤ (P : ℝ) * r.source.rate)
    (den : Matrix (ZMod P) (ZMod P) ℝ)
    (q : ℕ → Option ℕ → ℝ)
    (he : ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => (B.sample history m .residual r bin).getD 0 σ x y -
          B.residualCanonicalRay r bin σ x y) ≤ q m bin) :
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      (B.residualTransportedGroupInput history M d r σ x y -
        rowSliceMean X Y (B.residualTransportedGroupInput history M d r) x y) / den x y) ≤
      128 * ‖fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹‖ ^ 4 *
        ((B.bins.card : ℝ) + 1) ^ 3 *
        (∑ bin ∈ insert none (B.bins.image some),
          ((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 then 0
            else q (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin) +
          (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
            then 0 else q (LogSpaceEstimation.lastBudget M (2 * d) B.slack
              (B.sampleScale r bin)) bin))) := by
  let S := insert none (B.bins.image some)
  let E := fun m bin σ x y => (B.sample history m .residual r bin).getD 0 σ x y -
    (if m = 0 then 0 else B.residualCanonicalRay r bin σ x y)
  let f := fun bin => LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
  let c := fun bin => LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  have hS (bin : Option ℕ) : bin ∈ S ↔ bin ∈ B.rays .residual := by
    simp only [S, rays, mem_insert, mem_image, List.mem_append, List.mem_map,
      mem_toList, List.mem_singleton]
    exact or_comm
  have hE (m : ℕ) (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y (E m bin) ≤ if m = 0 then 0 else q m bin := by
    by_cases hm : m = 0
    · subst m
      simp [E, B.sample_zero, rowNormPow]
    · simpa only [E, hm, ↓reduceIte] using he bin ((hS bin).mp hb) m (by omega)
  have hsum (v : Option ℕ → ℝ) :
      ((B.rays .residual).map v).sum = ∑ bin ∈ S, v bin := by
    rw [show S = _ from rfl, sum_insert (by simp), sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_map_toList]
    ring
  have hin : B.residualTransportedGroupInput history M d r =
      fun σ x y => ∑ bin ∈ S, (E (f bin) bin σ x y - E (c bin) bin σ x y) := by
    funext σ x y
    exact hsum _
  have hpair (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y (fun σ x y =>
        E (f bin) bin σ x y - E (c bin) bin σ x y) ≤
      8 * ((if f bin = 0 then 0 else q (f bin) bin) +
        (if c bin = 0 then 0 else q (c bin) bin)) := by
    have hh := rowNormPow_add_le (X := X) (Y := Y) hNu (E (f bin) bin) (-E (c bin) bin)
    simp only [rowNormPow, Pi.neg_apply, abs_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (hE _ _ hb) (hE _ _ hb))
      (by norm_num))
  have hi := rowNormPow_sum_fourth_le S hNu X Y
    (fun bin σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y)
  rw [← hin] at hi
  have hcard : (S.card : ℝ) = (B.bins.card : ℝ) + 1 := by
    simp [S, card_image_of_injective _ (Option.some_injective ℕ), Nat.cast_add, Nat.cast_one]
  have hi' := hi.trans (mul_le_mul_of_nonneg_left (sum_le_sum hpair) (by positivity))
  rw [hcard, ← mul_sum] at hi'
  have hc := rowNormPow_centered_sub_fourth_le hNu X Y
    (B.residualTransportedGroupInput history M d r) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero] at hc
  have hw := rowNormPow_mul_le_pi_norm hNu X Y
    (fun σ x y => B.residualTransportedGroupInput history M d r σ x y -
      rowSliceMean X Y (B.residualTransportedGroupInput history M d r) x y)
    (fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹)
  simp only [div_eq_mul_inv]
  apply hw.trans
  apply (mul_le_mul_of_nonneg_left hc (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_left hi'
    (show 0 ≤ ‖fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹‖ ^ 4 * 16 by positivity)
  nlinarith only [hh]

/-- A centered relative input payment feeds the exact production noise budget.
The finite spectral norm is taken only after preserving the original pair's
joint density, denominator and actual walk length. -/
theorem rawRelativeNoiseBudget_le_of_centered_fourth
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss)
    (A : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) (cost : ℕ → ℝ)
    (hcost : ∀ i ∈ range j,
      rowNormPow 4 P r.source.rate
        (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
        (NormalizedMoments.retainedMask t (side P ku) B.padding su)
        (fun σ x y => (A i σ x y - rowSliceMean
          (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
          (NormalizedMoments.retainedMask t (side P ku) B.padding su) (A i) x y) /
          (rate ku + G x y)) ≤ cost i) :
    B.rawRelativeNoiseBudget M r s t hst ks ku ss su A G j ≤
      (j : ℝ) ^ 3 * ∑ i ∈ range j,
        ‖fun xy : ZMod P × ZMod P => 2 *
          (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
            (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
            xy.1 xy.2).spectralExpansion ^
              (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))‖ * cost i := by
  let X := NormalizedMoments.retainedMask s (side P ks) B.padding ss
  let Y := NormalizedMoments.retainedMask t (side P ku) B.padding su
  let w := fun i (xy : ZMod P × ZMod P) => 2 *
    (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
      (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
      xy.1 xy.2).spectralExpansion ^
        (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  unfold rawRelativeNoiseBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i hi
  apply le_trans _ (mul_le_mul_of_nonneg_left (hcost i hi) (norm_nonneg (w i)))
  rw [rowNormPow_eq_sum_dens_mul_expect]
  simp only [mul_assoc, mul_sum]
  apply sum_le_sum; intro x _
  apply sum_le_sum; intro y _
  have hw : w i (x, y) ≤ ‖w i‖ := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (w i) (x, y))
  have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤
    (({σ | X σ x ∧ Y σ y} : Finset (Environment P 3)).dens : ℝ) *
      (𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset (Environment P 3)),
        |(A i σ x y - rowSliceMean X Y (A i) x y) / (rate ku + G x y)| ^ 4) by positivity)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hNu)
  dsimp only [w, X, Y] at hh'
  nlinarith only [hh']

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
