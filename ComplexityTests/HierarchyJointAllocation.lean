/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of joint RAW allocation)
import Complexity.Foundations.Probability.HierarchyJointAllocation
import all ComplexityTests.HierarchyPrefixMean

/-!
A growing budget and bounded field satisfy the noise margin and actual mean
coverage, cutoff-fit and omission guards together. The full bin family is nonempty,
its finest canonical ray has positive diagonal mean, and the full prefix exhausts it.
The combined consumer uses that same depth choice and an honest eighth allowance.
Execution and own-request IH remain separate supplied premises;
this fixture is not recursive availability or a nonzero post-walk noise claim.
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

namespace JointAllocationRegression

-- The field follows the growing budget, and the same horizon covers every bin.
theorem growing_joint_guards (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ (P : ℕ) (hP : P.Prime), let : Fact P.Prime := ⟨hP⟩
      ∃ H : Horizon P,
      let M := 2 ^ N
      let n := M / 8 + 1
      let D := RawSemanticDeficitRegression.data HP P A n n
      let r := ProductAllocationRegression.request HP P
      H.maxExponent = n ∧ P ≤ 2 ^ (n + 1) ∧
      D.slack * (1 + 4 * n) < M ∧ M ≤ 32 * D.slack * n ∧ n ≤ H.maxExponent ∧
      D.bins.Nonempty ∧
      (∀ x y, D.base x y = 0 ∨ rate n ≤ D.base x y) ∧
      (∀ x y, D.base x y ≤ rate 0) ∧
      0 < D.requestPrecision M r ∧
      16 * (D.slack : ℝ) *
        (2 * (((0 : ℕ) : ℝ) + (0 : ℕ)) + D.rankCharge * r.task.rank +
          A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M ∧
      LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) 0)
        D.slack (D.sampleScale r (some n)) = 0 ∧
      0 < LogSpaceEstimation.lastBudget M 1 D.slack (D.sampleScale r none) ∧
      (0 < LogSpaceEstimation.lastBudget M 2 D.slack (D.sampleScale r none) ∧
        LogSpaceEstimation.lastBudget M 1 D.slack (D.sampleScale r none) ≠
          LogSpaceEstimation.lastBudget M 2 D.slack (D.sampleScale r none)) ∧
      ∀ x : ZMod P, 0 < rowSliceMean
        (fun σ x => r.source.retains (channels D.padding) σ x)
        (fun σ y => r.terminal.retains (channels D.padding) σ y)
        (D.residualCanonicalRay r (some n)) x x := by
  let D₀ := RawSemanticDeficitRegression.data HP 5 A 0 0
  obtain ⟨N₀, hfamily⟩ := exists_prefix_joint_depth_family A D₀ rfl 0 0 0 0
    (ProductAllocationRegression.request HP 5) rfl rfl
  refine ⟨max N₀ 6, ?_⟩
  intro N hN'
  have hN : N₀ ≤ N := (le_max_left _ _).trans hN'
  have hN6 : 6 ≤ N := (le_max_right _ _).trans hN'
  have hNM := Nat.lt_two_pow_self (n := N)
  let M := 2 ^ N
  let n := M / 8 + 1
  obtain ⟨P, hP, _, hPupper, H, hH, _⟩ :=
    exists_bounded_depth_prime n 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D := RawSemanticDeficitRegression.data HP P A n n
  let r := ProductAllocationRegression.request HP P
  have hn : n ≤ H.maxExponent := by rw [hH]
  have hb : 16 * (D.slack : ℝ) *
      (2 * (((0 : ℕ) : ℝ) + (0 : ℕ)) + D.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M := by
    simpa only [D, data, ProductAllocationRegression.data, r,
      ProductAllocationRegression.request, D₀, M] using (hfamily N hN).2.2.2.2.2.2.1
  have hp' := D.requestPrecision_prefix_margin A M 0 0 r rfl rfl hb
  have hp : 0 < D.requestPrecision M r := by
    have hzero : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ (Nat.log2 M + 1 : ℕ) := Nat.cast_nonneg _
    linarith only [hp', hzero, hm]
  have hM64 : 64 ≤ M := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hN6
    simpa only [M] using hh
  have hlo : D.slack * (1 + 4 * n) < M := by
    change 1 * (1 + 4 * n) < M
    dsimp only [n]
    omega
  have hhi : M ≤ 32 * D.slack * n := by
    change M ≤ 32 * 1 * n
    dsimp only [n]
    omega
  have hz : LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) 0)
      D.slack (D.sampleScale r (some n)) = 0 := by
    have hd : dyadicSlack (Nat.log2 M + 1) 0 = M := by
      simp only [M, Nat.log2_two_pow, dyadicSlack, Nat.zero_add, Nat.add_sub_cancel]
    rw [hd]
    unfold LogSpaceEstimation.lastBudget
    exact Nat.sub_eq_zero_of_le (le_max_left _ _)
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
  refine ⟨P, hP, H, hH, hPupper, hlo, hhi, hn, ?_, ?_, hCf, hp, hb, hz,
    D.raw_negative_budget_pos_of_precision hcharge M 0 0 r
      hrank rfl rfl hp, ?_, ?_⟩
  · exact ⟨0, by change 0 ∈ range (n + 1); simp⟩
  · intro x y
    by_cases he : x = y
    · right
      change rate n ≤ rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
      simpa only [Matrix.one_apply, he, ↓reduceIte, mul_one] using le_rfl
    · left
      change rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y = 0
      simp [he]
  · rw [D.sampleScale_none_eq_zero r]
    change 0 < M - 2 ∧ M - 1 ≠ M - 2
    dsimp only [M]
    omega
  · intro x
    rw [D.residualCanonicalRay_positive_mean rfl rfl rfl
      (by norm_num [D, data, ProductAllocationRegression.data]) H r 0 2 (by decide)
      0 0 [1] [2, 3] rfl rfl (by omega) (by omega)
      (RawSemanticDeficitRegression.base_nonneg HP P A n n)
        (RawSemanticDeficitRegression.base_mass HP P A n n)
      hCf n hn x x]
    have hnume : D.cutoff n (D.base x x / D.binRate n) = 1 := by
      change (RawSemanticDeficitRegression.data HP P A n n).cutoff n
        ((rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x x) / rate n) = 1
      simp only [Matrix.one_apply_eq, mul_one, div_self (rate_pos n).ne']
      exact RawSemanticDeficitRegression.fine_numerator HP P A n (M / 8)
    rw [hnume, mul_one]
    apply add_pos_of_pos_of_nonneg (rate_pos n)
    apply sum_nonneg
    intro z _
    apply mul_nonneg
    · exact (HP.toHierarchyParams.isCorrectionSeq_correctionIter
        (rate_pos 0) (RawSemanticDeficitRegression.base_nonneg HP P A n n)).nonneg
          HP.k x z
    · exact mul_nonneg (rate_pos n).le (D.cutoff_bounds n _).1

theorem growing_joint_consumer (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (δ cap C Cpre : ℝ) (hδ : 0 < δ) (lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ 1 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (P : ℕ) [Fact P.Prime]
    (H : Horizon P) (_hn : 2 ^ N / 8 + 1 ≤ H.maxExponent),
    let D := RawSemanticDeficitRegression.data HP P A (2 ^ N / 8 + 1) (2 ^ N / 8 + 1)
    let r := familyRequest HP P
    let M := 2 ^ N
    ∀ (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (_hg : ∀ j ∈ range (Nat.log2 M + 1), ∀ bin ∈ D.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          D.slack (D.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          D.slack (D.sampleScale r bin)) → D.ResidualEndpointGates history m r bin)
    (z : ℝ)
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
    (_hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ D.rays .residual,
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d D.slack
        (D.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) D.slack
        (D.sampleScale r bin)
      f ≠ c → (0 < f → ∃ T, D.sample history f .residual r bin = some T) ∧
        (0 < c → ∃ T, D.sample history c .residual r bin = some T)),
    LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) 0) D.slack
      (D.sampleScale r (some (M / 8 + 1))) = 0 ∧
    D.slack * (1 + 4 * (M / 8 + 1)) < M ∧ M ≤ 32 * D.slack * (M / 8 + 1) ∧
    0 < D.requestPrecision M r ∧
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
    let tail := vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent r.terminal.role D.padding r.terminal.suffix
        0 m j δ G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail r.terminal.role (side P 0) D.padding r.terminal.suffix m j μ σ x
        else 0)
    let a := fun j => rowNormPow 4 P r.source.rate X Y
      (actualNoiseEntry r.source.role r.terminal.role (side P 0) (side P 0) (side P 0)
        D.padding r.source.suffix r.terminal.suffix 0 G Δ 0 0 j)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z D.padding id r
      ((D.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, D.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    D.raw history M .residual r = some (D.rawFirstPrefixes history M .residual r m) ∧
    initialSeparatedReserve HP C Cpre
      (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ))
      (b (Nat.log2 M) ^ (4⁻¹ : ℝ)) (tail ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j)
      + initialSeparatedReserve HP C Cpre
        (∑ j ∈ range m, dyadicFloor δ m j * a j ^ (4⁻¹ : ℝ))
        (a (Nat.log2 M) ^ (4⁻¹ : ℝ))
        (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
        (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
          ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
          ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * a j) ≤
      ((2 : ℝ) ^ (-D.requestPrecision M r)) ^ 4 / 8 := by
  obtain ⟨A₀, hlower, hpos, hbound⟩ :=
    exists_residualFirst_joint_charge HP 16 δ cap C Cpre (by norm_num) hδ lower
  refine ⟨A₀, hlower, hpos, ?_⟩
  intro A hAA
  let D₀ := RawSemanticDeficitRegression.data HP 5 A 0 0
  obtain ⟨N₀, hfamily⟩ := exists_prefix_joint_depth_family A D₀ rfl 0 0 0 0
    (ProductAllocationRegression.request HP 5) rfl rfl
  refine ⟨N₀, ?_⟩
  intro N hN P _ H hn
  have hA : 1 ≤ A := hpos.trans hAA
  dsimp only
  intro history child depth ζ floor hg z second hrows hnrow hdirect hleft hright hnegative
    hID hIL hIR hIN hcalls
  let D := RawSemanticDeficitRegression.data HP P A (2 ^ N / 8 + 1)
    (2 ^ N / 8 + 1)
  let M := 2 ^ N
  let r := ProductAllocationRegression.request HP P
  have hb : 16 * (D.slack : ℝ) *
      (2 * (((0 : ℕ) : ℝ) + (0 : ℕ)) + D.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M := by
    simpa only [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data, r,
      ProductAllocationRegression.request, D₀, M] using (hfamily N hN).2.2.2.2.2.2.1
  have hp := D.requestPrecision_prefix_margin A M 0 0 r rfl rfl hb
  have hpositive : 0 < D.requestPrecision M r := by
    have hzero : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ (Nat.log2 M + 1 : ℕ) := Nat.cast_nonneg _
    linarith only [hp, hzero, hm]
  have hz : LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) 0) D.slack
      (D.sampleScale r (some (M / 8 + 1))) = 0 := by
    have hd : dyadicSlack (Nat.log2 M + 1) 0 = M := by
      simp only [M, Nat.log2_two_pow, dyadicSlack, Nat.zero_add, Nat.add_sub_cancel]
    rw [hd]
    unfold LogSpaceEstimation.lastBudget
    exact Nat.sub_eq_zero_of_le (le_max_left _ _)
  have hdepth : D.slack * (1 + 4 * (M / 8 + 1)) < M ∧
      M ≤ 32 * D.slack * (M / 8 + 1) := by
    simpa only [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data,
      D₀, M, Nat.add_zero] using
      And.intro (hfamily N hN).2.2.2.2.1 (hfamily N hN).2.2.2.2.2.1
  refine ⟨hz, hdepth.1, hdepth.2, hpositive, ?_⟩
  have hbins : D.bins = range (M / 8 + 1 + 1) := rfl
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
    change rate (M / 8 + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y ≤ rate 0
    by_cases he : x = y
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_one]
      exact rate_antitone (Nat.zero_le _)
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_zero]
      exact (rate_pos 0).le
  have hactual := D.raw_residual_first_joint_reserve_le_payment (M / 8 + 1) hbins rfl rfl rfl
    (by norm_num [D, RawSemanticDeficitRegression.data, ProductAllocationRegression.data])
    H (by omega) M 0 0 r (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
    (Nat.zero_le _) (by omega)
    (RawSemanticDeficitRegression.base_nonneg HP P A (M / 8 + 1) (M / 8 + 1))
    (RawSemanticDeficitRegression.base_mass HP P A (M / 8 + 1) (M / 8 + 1)) hCf
    (by
      intro z y
      by_cases he : z = y
      · right
        change rate (M / 8 + 1) ≤ rate (M / 8 + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) z y
        simpa only [Matrix.one_apply, he, ↓reduceIte, mul_one] using le_rfl
      · left
        change rate (M / 8 + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) z y = 0
        simp [he])
    hkh hl hk history child depth ζ floor hrows hnrow hdirect hleft hright hnegative
    hID hIL hIR hIN rfl rfl (by change (1 : ℝ) ≤ A; exact_mod_cast hA)
    hpositive hcalls δ cap C Cpre z hδ second A hb hg
  obtain ⟨hsignals, hgroups, hraw, hpay⟩ := hactual
  refine ⟨hsignals, hgroups, hraw, ?_⟩
  have hpayments := (hbound A hAA).2 (D.requestPrecision M r)
  have hsum := add_le_add hpayments.1 hpayments.2
  change _ ≤ ((2 : ℝ) ^ (-D.requestPrecision M r)) ^ 4 / 8
  apply hpay.trans
  change residualFirstMeanPayment HP δ cap C Cpre
    (residualRawMeanRootCost HP D.binCap * (2 : ℝ) ^ (-D.requestPrecision M r) *
      (2 : ℝ) ^ (-D.rankCharge)) +
    residualFirstNoisePayment HP δ cap C Cpre
      ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-D.requestPrecision M r)) ≤ _ at hsum
  exact hsum.trans_eq (by ring)

end JointAllocationRegression
