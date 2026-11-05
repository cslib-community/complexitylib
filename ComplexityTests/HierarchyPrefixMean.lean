/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of literal RAW prefix mean allocation)
import Complexity.Foundations.Probability.HierarchyPrefixMean
import all ComplexityTests.HierarchyRawClippedAssembly
import all ComplexityTests.HierarchyRawSemanticDeficit
import all ComplexityTests.HierarchyDyadicRawMean

/-!
Actual prefix consumers on non-unit signed E/EC and growing full-horizon fixtures.
Only positive prefix endpoints require own-request scalar comparisons. The same
fixed charge precedes fields and horizons; no simultaneous recursive IH is constructed.
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

namespace PrefixMeanRegression
open JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)

theorem nonunit_prefix_consumer (M j : ℕ) (hj : j < Nat.log2 M + 1) (hpositive : 0 < (B HP
  A).requestPrecision M (r HP))
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) →
      Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℝ)
    (hrows : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) q = some (child i q))
    (hnrow : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack
      0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack 0)) q = some (child 0 q))
    (hdirect : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M
      + 1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      (B HP A).compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) i (depth i q) (ζ i q) (floor i q)
          q =
        some (child i q))
    (hleft : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      (B HP A).evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP
        A).slack ((B HP A).sampleScale (r HP) (some i)))) q = some (.row (child i q)))
    (hright : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M
      + 1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      (B HP A).compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) i (depth i q) (ζ i q) (floor i q)
          q =
        some (child i q))
    (hnegative : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP
      A).slack 0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r
        HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (B HP A).evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP
        A).slack 0)) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIL : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIR : ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIN : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack
      0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child 0 q) ((B HP A).residualCanonicalChild 0 q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q)) ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack 0)) q ^ 4)
    (hA : 1 ≤ A)
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
    ∃ Fgroup : ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ,
      (∀ i < Nat.log2 M + 1,
        (B HP A).completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual (r HP) =
          some (Fgroup i)) ∧
      (B HP A).raw history M .residual (r HP) = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧
      rowNormPow 4 5 (r HP).source.rate
        (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
        (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
          (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
          (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| /
            (rate 1 + G x y))) ≤
        (BudgetData.residualRawMeanRootCost HP (B HP A).binCap *
          (2 : ℝ) ^ (-(B HP A).requestPrecision M (r HP)) * (2 : ℝ) ^ (-(A : ℝ)) *
          (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * (B HP A).slack))) ^ 4 := by
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
  exact (B HP A).raw_residual_prefix_clipped_le 2 hbins rfl rfl rfl
    (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data])
    SourceRegression.horizon (by decide) M j 2 1 hj (r HP) (by change (0 : Fin 3) ≠ 2; decide)
      rfl rfl
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
    rfl rfl (by change (1 : ℝ) ≤ A; exact_mod_cast hA) hpositive hcalls


end PrefixMeanRegression

private def familyData (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (P A : ℕ) (H : Horizon P) := RawSemanticDeficitRegression.data HP P A H.maxExponent
      (RawSemanticDeficitRegression.budget HP A + 1)
private abbrev familyRequest (HP : FourthRootHierarchyParams 16 1 16 32 8) (P : ℕ) :=
  ProductAllocationRegression.request HP P
private abbrev familyBudget (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ) :=
  RawSemanticDeficitRegression.budget HP A

-- Actual conditional consumer on the same growing full-horizon exhausted-ray family.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A P : ℕ) [Fact P.Prime]
    (H : Horizon P) (j : ℕ)
    (hj : j < Nat.log2 (familyBudget HP A) + 1) (hn : familyBudget HP A + 1 ≤ H.maxExponent) :
    let D := familyData HP P A H
    let r := familyRequest HP P
    let M := familyBudget HP A
    ∀ (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (_hrows : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          D.slack (D.sampleScale r (some i)))) q = some (child i q))
    (_hnrow : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        D.slack 0)) q = some (child 0 q))
    (_hdirect : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      D.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hleft : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      D.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) q = some (.row (child i q)))
    (_hright : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      D.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (_hnegative : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      D.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack 0)) q
        = some (.row (child 0 q)))
    (_hID : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIL : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIR : ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIN : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child 0 q) (D.residualCanonicalChild 0 q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q)) ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) D.slack 0)) q ^ 4)
    (_hA : 1 ≤ A)
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
    ∃ Fgroup : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        D.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (Fgroup i)) ∧
      D.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels D.padding) σ x)
        (fun σ y => r.terminal.retains (channels D.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels D.padding) σ x)
          (fun σ y => r.terminal.retains (channels D.padding) σ y)
          (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| /
            (rate 0 + G x y))) ≤
        (BudgetData.residualRawMeanRootCost HP D.binCap *
          (2 : ℝ) ^ (-D.requestPrecision M r) * (2 : ℝ) ^ (-(A : ℝ)) *
          (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * D.slack))) ^ 4 := by
  dsimp only
  intro history child depth ζ floor hrows hnrow hdirect hleft hright hnegative
    hID hIL hIR hIN hA hcalls
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
  exact D.raw_residual_prefix_clipped_le H.maxExponent hbins rfl rfl rfl
    (by norm_num [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data])
    H (by omega) M j 0 0 hj r (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
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
    hpositive hcalls

namespace PrefixMeanRegression
open JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)

-- Positive precision, adjacent d=1/d=2 budgets and a fully exhausted d=M
-- prefix coexist on the same non-unit, unequal-source fixture.
example : let e := 32 * (A * (HierarchyTask.residual (k := HP.k) 0).rank + 8)
    let M := 2 ^ e
    0 < (B HP A).requestPrecision M (r HP) ∧
    dyadicSlack (Nat.log2 M + 1) (Nat.log2 M) = 1 ∧
    dyadicSlack (Nat.log2 M + 1) (Nat.log2 M - 1) = 2 ∧
    dyadicSlack (Nat.log2 M + 1) 0 = M ∧
    LogSpaceEstimation.lastBudget M 1 (B HP A).slack 0 = M - 1 ∧
    LogSpaceEstimation.lastBudget M 2 (B HP A).slack 0 = M - 2 ∧
    LogSpaceEstimation.lastBudget M M (B HP A).slack 0 = 0 := by
  dsimp only
  let e := 32 * (A * (HierarchyTask.residual (k := HP.k) 0).rank + 8)
  have he : 1 ≤ e := by dsimp only [e]; omega
  have hpow : e ≤ 2 ^ e := (Nat.lt_two_pow_self (n := e)).le
  have hpowR : (32 : ℝ) * ((A : ℝ) *
      (HierarchyTask.residual (k := HP.k) 0).rank + 8) ≤ (2 ^ e : ℕ) := by
    exact_mod_cast hpow
  have hp : 0 < (B HP A).requestPrecision (2 ^ e) (r HP) := by
    rw [(B HP A).requestPrecision_grid (2 ^ e) 2 1 (r HP) rfl rfl]
    dsimp only [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data, r,
      TerminalMeanRegression.request]
    norm_num only [Nat.cast_one, Nat.cast_ofNat, mul_one]
    change 0 < ((2 ^ e : ℕ) : ℝ) / 16 - 6 -
      (A : ℝ) * (HierarchyTask.residual (k := HP.k) 0).rank
    have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) A)
      (Nat.cast_nonneg (α := ℝ) (HierarchyTask.residual (k := HP.k) 0).rank)
    generalize (2 ^ e : ℕ) = m at hpowR ⊢
    linarith only [hpowR, hprod]
  refine ⟨hp, dyadicSlack_last _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.log2_two_pow]
    simp only [dyadicSlack]
    have hh : e + 1 - (e - 1 + 1) = 1 := by omega
    rw [hh]
    norm_num
  · simp only [Nat.log2_two_pow, dyadicSlack, zero_add, Nat.add_sub_cancel]
  all_goals
    change LogSpaceEstimation.lastBudget _ _ 1 0 = _
    simp [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]

-- The canonical negative ray has nonzero mean; a fully exhausted prefix must
-- retain its sign in the total target deficit.
example (x : ZMod 5) : rowSliceMean
    (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
    (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
    ((B HP A).residualCanonicalRay (r HP) none) x x < 0 := by
  let roles : RoleProfile 3 := ⟨0, 1, 2, by decide, by decide, by decide⟩
  have hn := canonical_rawNegativeSample_mean HP (B HP A).padding id
    (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]) Function.injective_id
    SourceRegression.horizon roles 0 0 2 1 1 0 (by decide) (by decide) [1] [] [2, 3]
    (B HP A).base (TerminalMeanRegression.small_nonneg HP)
    (TerminalMeanRegression.small_mass HP) (TerminalMeanRegression.small_stage HP)
    ((B HP A).cutoff 0) ((B HP A).auxiliary 0) HP.ρ HP.K x x
  have he : rowSliceMean
      (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
      (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
      ((B HP A).residualCanonicalRay (r HP) none) x x =
        -TerminalMeanRegression.smallE HP x x := by
    change (𝔼 σ ∈ _, -_) = _
    rw [expect_neg_distrib]
    exact congrArg Neg.neg hn
  rw [he]
  exact neg_neg_of_pos (TerminalMeanRegression.small_correction_pos HP x)

end PrefixMeanRegression

-- One charge is chosen before every field and full retained horizon.
theorem growing_prefix_exhaustion (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ A : ℕ, 1 ≤ A ∧
      BudgetData.residualRawMeanRootCost HP 16 * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 ∧
    ∀ depth : ℕ, ∃ (P : ℕ) (hP : P.Prime), let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (n : ℕ),
        depth ≤ H.maxExponent ∧ n ≤ H.maxExponent ∧
        D.rankCharge = A ∧ D.bins = range (H.maxExponent + 1) ∧
        0 < D.requestPrecision (RawSemanticDeficitRegression.budget HP A) r ∧
        D.binBudget (RawSemanticDeficitRegression.budget HP A) n r = 0 ∧
        (∀ j, LogSpaceEstimation.lastBudget (RawSemanticDeficitRegression.budget HP A)
          (dyadicSlack (Nat.log2 (RawSemanticDeficitRegression.budget HP A) + 1) j)
          D.slack (D.sampleScale r (some n)) = 0) ∧
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
  have hprefix (j : ℕ) : LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack (D.sampleScale r (some n)) = 0 := by
    have hh := LogSpaceEstimation.lastBudget_antitone M D.slack (D.sampleScale r (some n))
      (show 1 ≤ dyadicSlack (Nat.log2 M + 1) j from dyadicSlack_pos _ _)
    dsimp only at hh
    rw [D.raw_positive_budget, hz] at hh
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
  refine ⟨P, hP, H, D, r, n, ?_, hn, rfl, rfl, hp, hz, hprefix,
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
