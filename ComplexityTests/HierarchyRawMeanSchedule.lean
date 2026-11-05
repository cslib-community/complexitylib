/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual RAW first-mean schedule payments)
import Complexity.Foundations.Probability.HierarchyRawMeanSchedule
import all ComplexityTests.HierarchyPrefixMean

/-!
Complete conditional production consumers on the non-unit positive E/EC fixture
and the growing full-horizon exhausted-bin family. The original prefix regressions
also check positive precision, d=1,2,M, nonzero negative means and exhaustion at
every prefix. No joint child execution or scalar IH is manufactured here.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open RawSemanticDeficitRegression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

namespace RawMeanScheduleRegression
open JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- All four payments and the actual heavy-event tail on unequal sources and positive E/EC.
theorem nonunit_schedule_consumer (M : ℕ) (hpositive : 0 < (B HP
  A).requestPrecision M (r HP))
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5))
    (child : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) →
      Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (depth : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℝ)
    (hrows : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) q = some (child j i q))
    (hnrow : ∀ j < Nat.log2 M + 1, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack
      0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack 0)) q = some (child j 0 q))
    (hdirect : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M
      + 1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      (B HP A).compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) i (depth j i q) (ζ j i q) (floor j i
          q)
          q =
        some (child j i q))
    (hleft : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      (B HP A).evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP
        A).slack ((B HP A).sampleScale (r HP) (some i)))) q = some (.row (child j i q)))
    (hright : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M
      + 1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      (B HP A).compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        (B HP A).slack ((B HP A).sampleScale (r HP) (some i)))) i (depth j i q) (ζ j i q) (floor j i
          q)
          q =
        some (child j i q))
    (hnegative : ∀ j < Nat.log2 M + 1, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M
      + 1) j) (B HP
      A).slack 0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r
        HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (B HP A).evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP
        A).slack 0)) q = some (.row (child j 0 q)))
    (hID : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child j i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIL : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child j i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIR : ∀ j < Nat.log2 M + 1, ∀ i ∈ (B HP A).bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M +
      1) j) (B HP A).slack ((B HP A).sampleScale (r HP) (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child j i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) (B HP A).slack ((B
            HP A).sampleScale (r HP) (some i)))) q ^ 4)
    (hIN : ∀ j < Nat.log2 M + 1, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) (B HP A).slack
      0) → let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child j 0 q) ((B HP A).residualCanonicalChild 0 q) ≤
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
        (0 < c → ∃ T, (B HP A).sample history c .residual (r HP) bin = some T))
    (δ radius z : ℝ) (hδ : 0 < δ)
    (second : Environment 5 3 → ZMod 5 → ℕ → ZMod 5 → ℝ) :
    let m := Nat.log2 M + 1
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base
    let X := retainedMask (r HP).source.role (side 5 2) (B HP A).padding (r HP).source.suffix
    let Y := retainedMask (r HP).terminal.role (side 5 1) (B HP A).padding (r HP).terminal.suffix
    let Δ := firstSignalIncrement ((B HP A).rawFirstPrefixes history M .residual (r HP)) 1 second
    let μ := fun j x y => actualClippedMean HP (r HP).source.role (r HP).terminal.role
      (side 5 2) (side 5 1) (side 5 1) (B HP A).padding (r HP).source.suffix (r HP).terminal.suffix
      1 G z Δ 0 0 j x y
    let b := fun j => rowNormPow 4 5 (r HP).source.rate X Y (fun _ => μ j)
    let E := residualRawMeanRootCost HP (B HP A).binCap * (2 : ℝ) ^ (-(B HP A).requestPrecision M (r
      HP)) *
      (2 : ℝ) ^ (-(B HP A).rankCharge)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z (B HP A).padding id (r HP)
      (((B HP A).completedGroup history M (dyadicSlack m i) .residual (r HP)).getD 0)
      0 σ x y 0) ∧
    (∀ i < m, ∃ F, (B HP A).completedGroup history M (dyadicSlack m i) .residual (r HP) = some F) ∧
    (B HP A).raw history M .residual (r HP) = some ((B HP A).rawFirstPrefixes history M .residual (r
      HP) m) ∧
    (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ)) ≤ δ * E / 511 ∧
    b (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ 2 * E ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * δ ^ 4)) * E ^ 4 / 63 ∧
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor δ m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * b i ^ (4⁻¹ : ℝ)) ≤
      (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 ∧
    vertexNormPow 4 5 (r HP).source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent (r HP).terminal.role (B HP A).padding (r HP).terminal.suffix
        1 m j δ G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail (r HP).terminal.role (side 5 1) (B HP A).padding (r HP).terminal.suffix m j μ
            σ x
        else 0) ≤ ((2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) ^ 4 := by
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
  exact (B HP A).raw_residual_first_mean_schedule 2 hbins rfl rfl rfl
    (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data])
    SourceRegression.horizon (by decide) M 2 1 (r HP) (by change (0 : Fin 3) ≠ 2; decide)
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
    rfl rfl (by change (1 : ℝ) ≤ A; exact_mod_cast hA) hpositive hcalls δ radius z hδ second

end RawMeanScheduleRegression

-- The same arbitrarily growing retained horizon keeps its exhausted fine bin.
theorem growing_schedule_consumer (HP : FourthRootHierarchyParams 16 1 16 32 8) (A P : ℕ) [Fact
  P.Prime]
    (H : Horizon P) (hn : familyBudget HP A + 1 ≤ H.maxExponent) :
    let D := familyData HP P A H
    let r := familyRequest HP P
    let M := familyBudget HP A
    ∀ (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (δ radius z : ℝ) (_hδ : 0 < δ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (_hrows : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          D.slack (D.sampleScale r (some i)))) q = some (child j i q))
    (_hnrow : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      BudgetData.row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        D.slack 0)) q = some (child j 0 q))
    (_hdirect : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1)
      j) D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      D.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) i (depth j i q) (ζ j i q) (floor j i q) q =
        some (child j i q))
    (_hleft : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      D.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) q = some (.row (child j i q)))
    (_hright : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1)
      j) D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      D.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
        (D.sampleScale r (some i)))) i (depth j i q) (ζ j i q) (floor j i q) q =
        some (child j i q))
    (_hnegative : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      D.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack 0)) q
        = some (.row (child j 0 q)))
    (_hID : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child j i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIL : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child j i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIR : ∀ j < Nat.log2 M + 1, ∀ i ∈ D.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      D.slack (D.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (BudgetData.midpoint r) r.terminal (D.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child j i q) (D.residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-D.requestPrecision m q))
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) D.slack
            (D.sampleScale r (some i)))) q ^ 4)
    (_hIN : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) D.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels D.padding) σ x)
        (fun σ y => q.usage.retains (channels D.padding) σ y)
        (child j 0 q) (D.residualCanonicalChild 0 q) ≤
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
    let m := Nat.log2 M + 1
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 0))
      (canonicalChannel id (rate 0)) (rate 0) D.base
    let X := retainedMask r.source.role (side P 0) D.padding r.source.suffix
    let Y := retainedMask r.terminal.role (side P 0) D.padding r.terminal.suffix
    let Δ := firstSignalIncrement (D.rawFirstPrefixes history M .residual r) 0 second
    let μ := fun j x y => actualClippedMean HP r.source.role r.terminal.role
      (side P 0) (side P 0) (side P 0) D.padding r.source.suffix r.terminal.suffix
      0 G z Δ 0 0 j x y
    let b := fun j => rowNormPow 4 P r.source.rate X Y (fun _ => μ j)
    let E := residualRawMeanRootCost HP D.binCap * (2 : ℝ) ^ (-D.requestPrecision M r) *
      (2 : ℝ) ^ (-D.rankCharge)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z D.padding id r
      ((D.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, D.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    D.raw history M .residual r = some (D.rawFirstPrefixes history M .residual r m) ∧
    (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ)) ≤ δ * E / 511 ∧
    b (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ 2 * E ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * δ ^ 4)) * E ^ 4 / 63 ∧
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor δ m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * b i ^ (4⁻¹ : ℝ)) ≤
      (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 ∧
    vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent r.terminal.role D.padding r.terminal.suffix
        0 m j δ G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail r.terminal.role (side P 0) D.padding r.terminal.suffix m j μ σ x
        else 0) ≤ ((2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) ^ 4 := by
  dsimp only
  intro history child depth ζ floor δ radius z hδ second hrows hnrow hdirect hleft hright hnegative
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
  exact D.raw_residual_first_mean_schedule H.maxExponent hbins rfl rfl rfl
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
    hpositive hcalls δ radius z hδ second
