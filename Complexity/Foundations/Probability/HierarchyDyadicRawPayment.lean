/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyJointSignedMean
public import Complexity.Foundations.Probability.HierarchyDyadicRawMean
import Complexity.Foundations.Probability.HierarchyApproximateHistory

/-!
# Paid conditional means of the executed RAW residual

The signed dyadic telescope identifies the final RAW conditional mean with the
paid finite-input mean at exactly its bin and negative budgets. All retained
endpoint budgets must be positive; otherwise the literal zero RAW boundary can
differ from finite-input children. Intermediate availability is conditional and
only unequal groups request samples. The genuine target is `C + EC - E`, and
own-request precision and reset-right masks remain in the scalar IH.

This is an original fully active endpoint bridge, not the general omitted-bin
payment, centered RAW noise, later-input accuracy or the full recursive invariant.
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

/-- Actual RAW conditional mean accuracy on a full retained finite horizon with
positive endpoint budgets, using the same fixed primitive charge and literal scalar
IH as the finite-input payment. No error or availability is asserted jointly. -/
theorem raw_residual_clipped_joint_le
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
      (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) ≤ 3 / 4)
    (s u : Fin 3) (hsu : s ≠ u) (ss su : List (ZMod P))
    (hgridS : r.source = gridChannel s ks ss)
    (hgridT : r.terminal = gridChannel u ka su) (husage : r.usage = r.terminal)
    (hlive : ∀ i ∈ B.bins, 0 < B.binBudget M i r) (hnlive : 0 < B.childBudget M)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ executed, B.raw history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨A, hA, hpaid⟩ := B.finiteInput_residual_clipped_joint_le
    n hbins hrate hcutoff haux hD H hnH M ks ka r hst hs ht hks hka
    hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
    htask hcharge hfixedD hfixedP
  have hp (i : ℕ) (hi : i ∈ B.bins) :
      ∃ A, B.positiveSample history (B.binBudget M i r) i .residual r = some A :=
    ⟨_, B.positiveSample_of_rows history (B.binBudget M i r) i .residual r
      (child i) (hrows i hi)⟩
  obtain ⟨R, hR, hm⟩ := B.raw_residual_mean_finiteInput history M r s u hsu
    ks ka ss su hgridS (husage.trans hgridT) hcalls hlive hnlive hp ⟨_, hnrow⟩ A hA
  have hmean (x y : ZMod P) : rowSliceMean
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) R x y =
    rowSliceMean
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) A x y := by
    simpa only [rowSliceMean, hgridS, hgridT, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, H4RankEnvironment.X, H4RankEnvironment.Y] using hm x y
  refine ⟨R, hR, ?_⟩
  simpa only [hmean] using hpaid

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
