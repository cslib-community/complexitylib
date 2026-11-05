/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of the bounded full-rate fixed-charge allocation)
import Complexity.Foundations.Probability.HierarchyFixedCharge
import all ComplexityTests.HierarchySignedClippedMean

/-!
The charge is chosen before the prime and execution coordinates. Positive precision
persists at arbitrarily large budgets. The actual successful-call family remains
conditional; these instances do not construct simultaneous recursive availability.
The imported non-unit E/EC, correlated sources and coarse/fine tests stay in scope.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace FixedChargeRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def B (A : ℝ) : BudgetData HP 5 :=
  { PolynomialBudgetHistory.data HP with bins := {0}, rankCharge := A }
private def r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.residual 0, gridChannel 0 0 [1], gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩

-- The primitive charge precedes all primes, requests, budgets and compression depths.
-- Positive precision is obtained after fixing that charge, rather than assumed impossible.
example : ∃ A : ℝ, 0 ≤ A ∧ BudgetData.fullRateRootCost HP 16 ≤ (2 : ℝ) ^ (A - 1) ∧
    ∀ (P : ℕ) (D : BudgetData HP P), D.rankCharge = A → D.binCap = 16 →
      ∀ q : HierarchyTask.Request HP.k (Fin 3) (ZMod P),
        q.source.rate = rate 0 → q.terminal.rate = rate 0 →
        ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < D.requestPrecision M q := by
  obtain ⟨A, hA, hfixed⟩ := BudgetData.exists_fullRate_charge (HP := HP) 16
  refine ⟨A, hA, hfixed, fun P D _ _ q hs ht => ?_⟩
  exact D.fullRate_precision_eventually_pos q hs ht

-- Both physical bin and once-negative budgets agree at the full-rate boundary.
example (A : ℝ) : (B HP A).binBudget 64 0 (r HP) = 63 ∧
    (B HP A).childBudget 64 = 63 := by
  norm_num [B, r, BudgetData.binBudget, BudgetData.childBudget,
    PolynomialBudgetHistory.data, gridChannel, rate, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff]

-- Fine/coarse endpoints can coincide at exhausted budgets; no extra child is inferred.
example : LogSpaceEstimation.lastBudget 1 1 1 0 =
    LogSpaceEstimation.lastBudget 1 2 1 0 := by
  norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

-- Full-rate does not remove genuine correction/product/negative cancellation.
-- This is the allocation fixture's own base, even after changing its bins and charge.
example (A : ℝ) (x : ZMod 5) :
    let E := HP.toHierarchyParams.correctionIter (canonicalChannel id (rate 0))
      (canonicalChannel id (rate 0)) (rate 0) (B HP A).base HP.k
    0 < E x x ∧ 0 < (E * (B HP A).base) x x ∧
      (B HP A).base + E * (B HP A).base - E = (B HP A).base := by
  change 0 < ProductMeanRegression.E HP x x ∧
    0 < (ProductMeanRegression.E HP * (1 : Matrix (ZMod 5) (ZMod 5) ℝ)) x x ∧
      (1 : Matrix (ZMod 5) (ZMod 5) ℝ) + ProductMeanRegression.E HP * 1 -
        ProductMeanRegression.E HP = 1
  rw [Matrix.mul_one]
  exact ⟨ProductMeanRegression.correction_pos HP x, ProductMeanRegression.correction_pos HP x,
    add_sub_cancel_right _ _⟩

-- A complete source reset retains the actual midpoint role and releases the suffix.
example (A : ℝ) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
      (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate 0)
    Q.direct.source.suffix = [1] ∧ Q.right.source.suffix = [] ∧
      Q.right.source.role = 1 ∧ Q.negative.isSome := by
  norm_num [HierarchyTask.rawRequests, BudgetData.midpoint, BudgetData.midpointRole, r,
    gridChannel]

-- The first coarse bin really loses five samples at exponent one. Its remaining
-- left salary is 5/16 minus the actual 32-slot structural payment.
example (A : ℝ) :
    let r₁ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨.residual 0, gridChannel 0 1 [1], gridChannel 2 1 [2, 3], gridChannel 2 1 [2, 3]⟩
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r₁.source
      (BudgetData.midpoint r₁) r₁.terminal ((B HP A).binRate 0)).left
    (2 : ℝ) ^ (-(B HP A).requestPrecision ((B HP A).binBudget 64 0 r₁) q) =
      (2 : ℝ) ^ (-(B HP A).requestPrecision 64 r₁) *
        (2 : ℝ) ^ (5 / 16 - 32 * A) := by
  dsimp only
  convert (B HP A).requestPrecision_residual_coarse_left 64 1 1
    ⟨.residual 0, gridChannel 0 1 [1], gridChannel 2 1 [2, 3], gridChannel 2 1 [2, 3]⟩
    rfl rfl rfl rfl
    (by norm_num [B, PolynomialBudgetHistory.data]) using 1; norm_num [B]

-- The fixed charge is chosen before the field and the entire supplied-call family.
-- This is an actual consumer client with positive parent precision, not a scalar-only bound.
example : ∃ A : ℝ, 0 ≤ A ∧
    ∀ (P : ℕ) [Fact P.Prime] (D : BudgetData HP P),
    D.rankCharge = A → D.binCap = 16 →
    ∀
    (n : ℕ) (_hbins : D.bins = range (n + 1)) (_hrate : D.binRate = rate)
    (_hcutoff : D.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (_haux : D.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (_hD : D.padding ≠ 0) (H : Horizon P) (_hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (_hst : r.source.role ≠ r.terminal.role)
    (_hs : r.source.rate = rate ks) (_ht : r.terminal.rate = rate ka)
    (_hks : ks ≤ H.maxExponent) (_hka : ka ≤ ks)
    (_hC : ∀ x y, 0 ≤ D.base x y) (_hC1 : D.base *ᵥ 1 ≤ 1)
    (_hCf : ∀ x y, D.base x y ≤ rate ka)
    (_hcover : ∀ z y, D.base z y = 0 ∨ rate n ≤ D.base z y)
    (_hkh : ∀ i ∈ D.bins, ∀ v, D.cutoff i v ≠ 0 → D.auxiliary i v = 1)
    (_hlight : ∀ i ∈ D.bins, ∀ d, d ≤ HP.θ → D.cutoff i d = 0)
    (_hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (_hrows : ∀ i ∈ D.bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history (D.binBudget M i r) q = some (child i q))
    (_hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      BudgetData.row history (D.childBudget M) q = some (child 0 q))
    (_hdirect : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      D.compressedBin (D.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hleft : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      D.evaluate (D.binBudget M i r) q = some (.row (child i q)))
    (_hright : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      D.compressedBin (D.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      D.evaluate (D.childBudget M) q = some (.row (child 0 q)))
    (_hID : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-D.requestPrecision (D.binBudget M i r) q)) ^ 4)
    (_hIL : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-D.requestPrecision (D.binBudget M i r) q)) ^ 4)
    (_hIR : ∀ i ∈ D.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-D.requestPrecision (D.binBudget M i r) q)) ^ 4)
    (_hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child 0 q) (D.residualCanonicalChild 0 q) ≤
        ((2 : ℝ) ^ (-D.requestPrecision (D.childBudget M) q)) ^ 4)
    (_hn : n = 0) (_hks0 : ks = 0) (_hka0 : ka = 0)
    (_htask : r.task = .residual 0)
    (_hpositive : 0 < D.requestPrecision M r),
    0 < D.requestPrecision M r ∧
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) D.base
    ∃ executed, D.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels D.padding) σ x)
        (fun σ y => r.terminal.retains (channels D.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels D.padding) σ x)
          (fun σ y => r.terminal.retains (channels D.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        ((2 : ℝ) ^ (-D.requestPrecision M r)) ^ 4 := by
  obtain ⟨A, hA, hfixed⟩ := BudgetData.exists_fullRate_charge (HP := HP) 16
  refine ⟨A, hA, ?_⟩
  intro P inst D hAE hCE n hbins hrate hcutoff haux hD H hnH M ks ka r hst hs ht
    hks hka hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN hn hks0 hka0 htask hpositive
  refine ⟨hpositive, ?_⟩
  exact D.finiteInput_residual_clipped_fullRate_le n hbins hrate hcutoff haux hD H hnH
    M ks ka r hst hs ht hks hka hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN hn hks0 hka0 htask
    (by simpa only [hAE] using hA) (by simpa only [hAE, hCE] using hfixed)

end FixedChargeRegression
