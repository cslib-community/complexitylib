/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyEndpointMean

/-!
# Actual finite signed clipped means from scalar child root bounds

This consumer executes the finite input using supplied successful rows. It pays the
actual direct and product calls at each bin budget and the negative correction once
at its separate child budget. Minkowski sums rooted payments without a bin count.
Every scalar child bound is on that request's own source and usage masks.
Product payments take the minimum of the coarse clipped and ordinary fine
comparisons, retaining their actual rate powers. Recursive availability and uniform
precision allocation are separate obligations.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Full finite signed execution and clipped mean payment. The child allowances may
be instantiated with their literal own-request precision; they are scalar root IH,
not free direct/product/negative accuracy assumptions. The supplied history and
successful compressed/evaluated calls are explicit, without recursive availability. -/
theorem finiteInput_residual_clipped_scalar_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (hkh : ∀ i ∈ B.bins, ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hlight : ∀ i ∈ B.bins, ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (ε : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ i ∈ B.bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate (B.childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIL : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIR : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ε (B.childBudget M) q ^ 4) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let d := fun i => F *
      ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * ε (B.childBudget M) neg ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ executed, B.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        (ne ^ (4⁻¹ : ℝ) + ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) +
          ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ)) ^ 4 := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let d := fun i => F *
      ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4
  let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let p := fun i => min (pc i) (po i)
  let ne := F * ε (B.childBudget M) neg ^ 4
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y =>
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y
  let pe := fun i x y => B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hiH (i : ℕ) (hi : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hi
    omega
  have hde (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|de i x y| / (rate ka + G x y))) ≤ d i :=
    B.residualDirect_parent_clipped_le n hbins hrate hcutoff hD H M i (depth i (Q i).direct) ks ka
      (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht hks hi
      (hiH i hi) hC hC1 hCf (hkh i hi) hK
      (child i (Q i).direct) (hdirect i hi) (ε (B.binBudget M i r) (Q i).direct) (hID i hi)
  have hpe (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|pe i x y| / (rate ka + G x y))) ≤ p i := by
    apply le_min
    · exact B.residualProduct_parent_clipped_le n hbins hrate hcutoff haux hD H M i
        (depth i (Q i).right) ks ka (ζ i (Q i).right) (floor i (Q i).right)
        r hst hs ht (congrFun hrate i)
        hks hka hi (hiH i hi) hC hC1 hCf (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
    · apply (rowNormPow_clipped_le_of_ordinary hNu (rate_pos ka) X Y (pe i) G
        (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)).trans
      dsimp only [po]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact B.residualProduct_parent_ordinary_le M i (depth i (Q i).right) ks ka
        (ζ i (Q i).right) (floor i (Q i).right) r hst hs ht (congrFun hrate i) (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
  have hne : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|nege x y| / (rate ka + G x y))) ≤ ne := by
    simp only [nege, abs_neg]
    exact B.residualNegative_parent_clipped_le hD H M ks ka r hst hs ht hks hka
      hC hC1 hCf (child 0 neg) hnegative (ε (B.childBudget M) neg) hIN
  let S : Finset (Option (ℕ ⊕ ℕ)) := insert none
    ((B.bins.image (fun i => some (Sum.inl i))) ∪
      (B.bins.image (fun i => some (Sum.inr i))))
  let e : Option (ℕ ⊕ ℕ) → ZMod P → ZMod P → ℝ := fun o =>
    match o with
    | none => nege
    | some (.inl i) => de i
    | some (.inr i) => pe i
  let pay : Option (ℕ ⊕ ℕ) → ℝ := fun o =>
    match o with
    | none => ne
    | some (.inl i) => d i
    | some (.inr i) => p i
  have hsum (v : Option (ℕ ⊕ ℕ) → ℝ) : ∑ o ∈ S, v o =
      v none + ∑ i ∈ B.bins, v (some (.inl i)) + ∑ i ∈ B.bins, v (some (.inr i)) := by
    have hd : Disjoint (B.bins.image (fun i => some (Sum.inl i)))
        (B.bins.image (fun i => some (Sum.inr i))) := by
      simp only [disjoint_left, mem_image]
      rintro o ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
      cases he
    rw [show S = _ from rfl, sum_insert (by simp), sum_union hd,
      sum_image (fun _ _ _ _ h => by simpa using h),
      sum_image (fun _ _ _ _ h => by simpa using h)]
    ring
  have h := rowNormPow_clipped_sum_le_pow_sum S hNu X Y e
    (fun x y => rate ka + G x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka)
      (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)) pay (by
        intro o ho
        cases o with
        | none => exact hne
        | some a =>
          cases a with
          | inl i => exact hde i (by simpa [S] using ho)
          | inr i => exact hpe i (by simpa [S] using ho))
  rw [hsum (fun o => pay o ^ (4⁻¹ : ℝ))] at h
  simp only [pay] at h
  simp_rw [hsum (fun o => e o _ _)] at h
  refine ⟨_, B.finiteInput_residual_of_rows history M r child hrows hnrow, ?_⟩
  have htarget (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
      rowSliceMean X Y A x y - G x y = rowSliceMean X Y
        (fun σ x y => A σ x y - B.residualCanonicalInput r σ x y) x y := by
    have href := B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
      r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      (by change r.source = {r.source with rate := rate ks}; rw [← hs])
      (by change r.terminal = { r.terminal with rate := rate ka}; rw [← ht])
      hks hka hC hC1 hCf x y (fun z => hcover z y)
    change rowSliceMean X Y (B.residualCanonicalInput r) x y = G x y at href
    rw [← href]
    exact (expect_sub_distrib _ _ _).symm
  change rowNormPow 4 P r.source.rate X Y (fun _ x y =>
    min 1 (|rowSliceMean X Y _ x y - G x y| / (rate ka + G x y))) ≤ _
  simp_rw [htarget]
  convert h using 1
  congr 1
  funext σ x y
  congr 2
  congr 1
  simp only [rowSliceMean, residualCanonicalInput, expect_sub_distrib,
    expect_sum_comm, HierarchyTask.rawPositiveSample, expect_add_distrib,
    e, de, pe, nege, residualProductMean, conditionalTableMean, X, Y]
  have hratio (i : ℕ) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal (Q i).direct y = gridMass P ka / gridMass P (max ka i) := by
    apply usageRatio_grid B.padding r.terminal (Q i).direct ka (max ka i) ht
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  dsimp only [Q] at hratio ⊢
  simp_rw [hratio, ← mul_expect]
  simp only [mul_sub, sum_sub_distrib, sum_add_distrib]
  ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
