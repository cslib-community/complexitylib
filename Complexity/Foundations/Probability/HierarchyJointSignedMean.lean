/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyJointProduct

/-!
# The executed signed residual mean at one fixed charge

The genuine target is the signed residual `G = C + EC - E`. This consumer executes
`finiteInput`, uses the direct and active product minima, and pays the negative
correction once. Own-mask accuracy and successful recursive calls are explicit
hypotheses. General RAW paired noise, completion and full recursive IH remain open.
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

/-- The actual finite-input clipped conditional mean meets parent fourth-moment
precision on every admitted grid horizon, conditional on literal own-request IH
and successful calls. `exists_residualJoint_charge` supplies both primitive guards
before the field, exponents, suffixes, depths and budget are selected. -/
theorem finiteInput_residual_clipped_joint_le
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
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIL : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIR : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4)
    (htask : r.task = .residual 0) (hcharge : 0 ≤ B.rankCharge)
    (hfixedD : residualDirectRootCost HP B.binCap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) ≤ 1 / 4)
    (hfixedP : residualProductNegativeRootCost HP B.binCap *
      (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) ≤ 3 / 4) :
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
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨executed, hex, hmean⟩ := B.finiteInput_residual_clipped_direct_min_le
    n hbins hrate hcutoff haux hD H hnH M ks ka r hst hs ht hks hka
    hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
    (fun m q => (2 : ℝ) ^ (-B.requestPrecision m q))
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
  refine ⟨executed, hex, hmean.trans ?_⟩
  have ha : ka ≤ H.maxExponent := hka.trans hks
  have hi (i : ℕ) (hib : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hib
    omega
  have hd := B.residualDirect_min_sum_salary H M ks ka ha hi r hrate hs ht htask
  have hdf := mul_le_mul_of_nonneg_right hfixedD
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-B.requestPrecision M r))
  dsimp only [residualDirectRootCost] at hdf
  have hdpaid := hd.trans (by convert hdf using 1; ring)
  have hp := B.residualProduct_negative_sum_le H M ks ka ha hi r hrate hs ht htask
    hka hcharge hfixedP
  dsimp only at hdpaid hp ⊢
  apply pow_le_pow_left₀ ?_
  · nlinarith [hdpaid, hp]
  · have hcap := B.binCap_nonneg
    have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
    have hterminal : 0 < r.terminal.rate := by rw [ht]; exact rate_pos ka
    have hf := rate_pos ka
    have hmass (i : ℕ) := gridMass_pos (P := P) i
    have hbin (i : ℕ) : 0 < B.binRate i := by rw [hrate]; exact rate_pos i
    apply add_nonneg (add_nonneg ?_ ?_) ?_
    · positivity
    · apply sum_nonneg
      intro i _
      have hb := hbin i
      have hri := rate_pos i
      have hm := hmass ka
      have hmm := hmass (max ka i)
      positivity
    · apply sum_nonneg
      intro i _
      have hb := hbin i
      have hm := hmass ka
      have hmm := hmass (max ka i)
      have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
      split_ifs <;> positivity

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
