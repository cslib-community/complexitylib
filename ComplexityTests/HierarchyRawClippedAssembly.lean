/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual RAW clipped mean assembly)
import Complexity.Foundations.Probability.HierarchyRawClippedAssembly
import all ComplexityTests.HierarchyRawSemanticDeficit
import all ComplexityTests.HierarchyDyadicRawMean

/-!
The non-unit actual RAW consumer uses conditional own-request IH only at positive
budgets, and derives the negative guard from parent precision. The growing full-horizon
fixture fixes the joint charge before field and depth and retains a nonzero canonical
fine ray at an exhausted final budget. This does not construct simultaneous child accuracy.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open RawSemanticDeficitRegression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace RawClippedAssemblyRegression
open JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)

example (M : ℕ) (hpositive : 0 < (B HP A).requestPrecision M (r HP))
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) →
      Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℝ)
    (hrows : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((B HP A).binBudget M i (r HP)) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      BudgetData.row history ((B HP A).childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      (B HP A).compressedBin ((B HP A).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      (B HP A).evaluate ((B HP A).binBudget M i (r HP)) q = some (.row (child i q)))
    (hright : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      (B HP A).compressedBin ((B HP A).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (B HP A).evaluate ((B HP A).childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIL : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIR : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child 0 q) ((B HP A).residualCanonicalChild 0 q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q)) ((B HP A).childBudget M) q ^ 4)
    (hA : 1 ≤ A)
    (hfixed : BudgetData.residualRawMeanRootCost HP (B HP A).binCap *
      (2 : ℝ) ^ (-(A : ℝ)) ≤ 1)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ (B HP A).rays .residual,
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d (B HP A).slack
        ((B HP A).sampleScale (r HP) bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) (B HP A).slack
        ((B HP A).sampleScale (r HP) bin)
      f ≠ c → (0 < f → ∃ T, (B HP A).sample history f .residual (r HP) bin = some T) ∧
        (0 < c → ∃ T, (B HP A).sample history c .residual (r HP) bin = some T)) :
    0 < (B HP A).requestPrecision M (r HP) ∧
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base
    ∃ executed, (B HP A).raw history M .residual (r HP) = some executed ∧
      rowNormPow 4 5 (r HP).source.rate
        (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
        (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
          (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
          executed x y - G x y| /
            (rate 1 + G x y))) ≤
        ((2 : ℝ) ^ (-(B HP A).requestPrecision M (r HP))) ^ 4 := by
  refine ⟨hpositive, ?_⟩
  have hbins : (B HP A).bins = range (2 + 1) := by
    ext j
    simp [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hkh (i : ℕ) (_hi : i ∈ (B HP A).bins) (v : ℝ)
      (hv : (B HP A).cutoff i v ≠ 0) : (B HP A).auxiliary i v = 1 :=
    HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hl (i : ℕ) (_hi : i ∈ (B HP A).bins) (d : ℝ) (hd : d ≤ HP.θ) :
      (B HP A).cutoff i d = 0 :=
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun v hv => polynomialSwitch4_of_le (by norm_num) hv) rate_pos rate_antitone
      (hd.trans hθ) i (fun _ => 1)
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  exact (B HP A).raw_residual_clipped_parent_le 2 hbins rfl rfl rfl
    (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data])
    SourceRegression.horizon (by decide) M 2 1 (r HP) (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
    (by decide) (by decide) (TerminalMeanRegression.small_nonneg HP)
    (TerminalMeanRegression.small_mass HP) (TerminalMeanRegression.small_stage HP)
    (by
      intro z y
      by_cases h : z = y
      · right
        norm_num [B, TerminalMeanRegression.smallData, h, rate]
      · left
        norm_num [B, TerminalMeanRegression.smallData, h, rate])
    hkh hl hk history child depth ζ floor
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
    rfl rfl (by change (1 : ℝ) ≤ A; exact_mod_cast hA) hpositive hfixed hcalls

end RawClippedAssemblyRegression

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ A : ℕ, 1 ≤ A ∧
      BudgetData.residualRawMeanRootCost HP 16 * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 ∧
    ∀ depth : ℕ, ∃ (P : ℕ) (hP : P.Prime), let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (n : ℕ),
        depth ≤ H.maxExponent ∧ n ≤ H.maxExponent ∧
        D.rankCharge = A ∧ D.bins = range (H.maxExponent + 1) ∧
        0 < D.requestPrecision (RawSemanticDeficitRegression.budget HP A) r ∧
        D.binBudget (RawSemanticDeficitRegression.budget HP A) n r = 0 ∧
        0 < LogSpaceEstimation.lastBudget (RawSemanticDeficitRegression.budget HP A) 1 D.slack
          (D.sampleScale r none) ∧
        ∀ x : ZMod P, 0 < rowSliceMean
          (fun σ x => r.source.retains (channels D.padding) σ x)
          (fun σ y => r.terminal.retains (channels D.padding) σ y)
          (D.residualCanonicalRay r (some n)) x x := by
  obtain ⟨A, hA, hfixed⟩ := BudgetData.exists_residualRawMean_charge (HP := HP) 16
  refine ⟨A, hA, hfixed, ?_⟩
  intro depth
  let M := RawSemanticDeficitRegression.budget HP A
  let n := M + 1
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max depth n + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D := RawSemanticDeficitRegression.data HP P A H.maxExponent n
  let r := ProductAllocationRegression.request HP P
  have hn : n ≤ H.maxExponent := by rw [hH]; omega
  have hp : 0 < D.requestPrecision M r := by
    rw [D.requestPrecision_grid M 0 0 r rfl rfl]
    dsimp only [D, data, ProductAllocationRegression.data, r,
      ProductAllocationRegression.request]
    norm_num only [Nat.cast_zero, add_zero, mul_zero, sub_zero, Nat.cast_one, mul_one]
    dsimp only [M, budget]
    push_cast
    ring_nf
    positivity
  have hz : D.binBudget M n r = 0 := by
    change LogSpaceEstimation.lastBudget M 1 D.slack (D.sampleScale r (some n)) = 0
    rw [D.sampleScale_grid r 0 n rfl rfl]
    change LogSpaceEstimation.lastBudget M 1 1 (4 * ((0 : ℤ) - n)) = 0
    rw [zero_sub]
    simp only [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast, Nat.one_mul]
    norm_num only
    dsimp only [n]
    omega
  have hCf (x y : ZMod P) : D.base x y ≤ rate 0 := by
    change rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y ≤ rate 0
    by_cases he : x = y
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_one]
      exact rate_antitone (Nat.zero_le n)
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_zero]
      exact (rate_pos 0).le
  have hrank : 1 ≤ r.task.rank := by
    simp only [r, ProductAllocationRegression.request, HierarchyTask.rank]
    omega
  have hcharge : (1 : ℝ) ≤ D.rankCharge := by
    change (1 : ℝ) ≤ A
    exact_mod_cast hA
  refine ⟨P, hP, H, D, r, n, ?_, hn, rfl, rfl, hp, hz,
    D.raw_negative_budget_pos_of_precision hcharge M 0 0 r
      hrank rfl rfl hp, ?_⟩
  · rw [hH]; omega
  · intro x
    rw [D.residualCanonicalRay_positive_mean rfl rfl rfl
      (by norm_num [D, data, ProductAllocationRegression.data]) H r 0 2 (by decide)
      0 0 [1] [2, 3] rfl rfl (by omega) (by omega)
      (RawSemanticDeficitRegression.base_nonneg HP P A H.maxExponent n)
        (RawSemanticDeficitRegression.base_mass HP P A H.maxExponent n)
      hCf n hn x x]
    have hnume : D.cutoff n (D.base x x / D.binRate n) = 1 := by
      change (RawSemanticDeficitRegression.data HP P A H.maxExponent (M + 1)).cutoff (M + 1)
        ((rate (M + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x x) / rate (M + 1)) = 1
      simp only [Matrix.one_apply_eq, mul_one, div_self (rate_pos (M + 1)).ne']
      exact RawSemanticDeficitRegression.fine_numerator HP P A H.maxExponent M
    rw [hnume, mul_one]
    apply add_pos_of_pos_of_nonneg (rate_pos n)
    apply sum_nonneg
    intro z _
    apply mul_nonneg
    · exact (HP.toHierarchyParams.isCorrectionSeq_correctionIter
        (rate_pos 0) (RawSemanticDeficitRegression.base_nonneg HP P A H.maxExponent n)).nonneg
          HP.k x z
    · exact mul_nonneg (rate_pos n).le (D.cutoff_bounds n _).1

private def familyData (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P A : ℕ) (H : Horizon P) := RawSemanticDeficitRegression.data HP P A H.maxExponent
      (RawSemanticDeficitRegression.budget HP A + 1)
private abbrev familyRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) (P : ℕ) :=
  ProductAllocationRegression.request HP P
private abbrev familyBudget (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ) :=
  RawSemanticDeficitRegression.budget HP A

-- Actual conditional consumer on the same growing full-horizon exhausted-ray family.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A P : ℕ) [Fact P.Prime]
    (H : Horizon P) (hn : familyBudget HP A + 1 ≤ H.maxExponent) :
    let D := familyData HP P A H
    let r := familyRequest HP P
    let M := familyBudget HP A
    ∀ (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (_hrows : ∀ i ∈ D.bins, 0 < D.binBudget M i r →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history (D.binBudget M i r) q = some (child i q))
    (_hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      BudgetData.row history (D.childBudget M) q = some (child 0 q))
    (_hdirect : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      D.compressedBin (D.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hleft : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      D.evaluate (D.binBudget M i r) q = some (.row (child i q)))
    (_hright : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      D.compressedBin (D.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      D.evaluate (D.childBudget M) q = some (.row (child 0 q)))
    (_hID : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          (D.binBudget M i r) q ^ 4)
    (_hIL : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          (D.binBudget M i r) q ^ 4)
    (_hIR : ∀ i ∈ D.bins, 0 < D.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          (D.binBudget M i r) q ^ 4)
    (_hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child 0 q) (D.residualCanonicalChild 0 q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q)) (D.childBudget M) q ^ 4)
    (_hA : 1 ≤ A)
    (_hfixed : BudgetData.residualRawMeanRootCost HP D.binCap *
      (2 : ℝ) ^ (-(A : ℝ)) ≤ 1)
    (_hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ D.rays .residual,
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d D.slack
        (D.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) D.slack
        (D.sampleScale r bin)
      f ≠ c → (0 < f → ∃ T, D.sample history f .residual r bin = some T) ∧
        (0 < c → ∃ T, D.sample history c .residual r bin = some T)),
    D.binBudget M (M + 1) r = 0 ∧ 0 < D.requestPrecision M r ∧
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 0))
      (canonicalChannel id (rate 0)) (rate 0) D.base
    ∃ executed, D.raw history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels D.padding) σ x)
        (fun σ y => r.terminal.retains (channels D.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels D.padding) σ x)
          (fun σ y => r.terminal.retains (channels D.padding) σ y)
          executed x y - G x y| /
            (rate 0 + G x y))) ≤
        ((2 : ℝ) ^ (-D.requestPrecision M r)) ^ 4 := by
  dsimp only
  intro history child depth ζ floor hrows hnrow hdirect hleft hright hnegative
    hID hIL hIR hIN hA hfixed hcalls
  let D := RawSemanticDeficitRegression.data HP P A H.maxExponent
    (RawSemanticDeficitRegression.budget HP A + 1)
  let M := RawSemanticDeficitRegression.budget HP A
  let r := ProductAllocationRegression.request HP P
  have hpositive : 0 < D.requestPrecision M r := by
    rw [D.requestPrecision_grid M 0 0 r rfl rfl]
    dsimp only [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data, r,
      ProductAllocationRegression.request]
    norm_num only [Nat.cast_zero, add_zero, mul_zero, sub_zero, Nat.cast_one, mul_one]
    dsimp only [M, RawSemanticDeficitRegression.budget]
    push_cast
    ring_nf
    positivity
  have hz : D.binBudget M (M + 1) r = 0 := by
    change LogSpaceEstimation.lastBudget M 1 D.slack (D.sampleScale r (some (M + 1))) = 0
    rw [D.sampleScale_grid r 0 (M + 1) rfl rfl]
    change LogSpaceEstimation.lastBudget M 1 1 (4 * ((0 : ℤ) - (M + 1))) = 0
    rw [zero_sub]
    simp only [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_neg, Int.natAbs_mul, Nat.one_mul]
    norm_num only
    omega
  refine ⟨hz, hpositive, ?_⟩
  have hbins : D.bins = range (H.maxExponent + 1) := rfl
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hkh (i : ℕ) (_hi : i ∈ D.bins) (v : ℝ)
      (hv : D.cutoff i v ≠ 0) : D.auxiliary i v = 1 :=
    HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hl (i : ℕ) (_hi : i ∈ D.bins) (d : ℝ) (hd : d ≤ HP.θ) : D.cutoff i d = 0 :=
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun v hv => polynomialSwitch4_of_le (by norm_num) hv) rate_pos rate_antitone
      (hd.trans hθ) i (fun _ => 1)
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  have hCf (x y : ZMod P) : D.base x y ≤ rate 0 := by
    change rate (M + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y ≤ rate 0
    by_cases he : x = y
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_one]
      exact rate_antitone (Nat.zero_le _)
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_zero]
      exact (rate_pos 0).le
  exact D.raw_residual_clipped_parent_le H.maxExponent hbins rfl rfl rfl
    (by norm_num [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data])
    H (by omega) M 0 0 r (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
    (Nat.zero_le _) (by omega)
    (RawSemanticDeficitRegression.base_nonneg HP P A H.maxExponent (M + 1))
    (RawSemanticDeficitRegression.base_mass HP P A H.maxExponent (M + 1)) hCf
    (by
      intro z y
      by_cases he : z = y
      · right
        change rate H.maxExponent ≤ rate (M + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) z y
        simpa only [Matrix.one_apply, he, ↓reduceIte, mul_one] using rate_antitone hn
      · left
        change rate (M + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) z y = 0
        simp [he])
    hkh hl hk history child depth ζ floor hrows hnrow hdirect hleft hright hnegative
    hID hIL hIR hIN rfl rfl (by change (1 : ℝ) ≤ A; exact_mod_cast hA)
    hpositive hfixed hcalls
