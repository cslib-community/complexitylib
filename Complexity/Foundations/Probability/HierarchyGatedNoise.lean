/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyGridNoise

/-!
# Successful gate ranges pay transported RAW noise

Only the two actual positive endpoint budgets require whole-row lookups and
range gates. Canonical references are genuine, including the final correction
iteration. No recursive accuracy or approximate canonical support is assumed.
This original per-group payment preserves the production allocator. The semantic
boundary, prefix structural reserve and joint recursive availability remain open.

## Main definitions

* `ResidualEndpointGates`: literal row availability and output ranges.

## Main results

* `residualSample_error_le_of_gates`: both signed ray cases.
* `rawRelativeNoiseGroup_transported_le_of_gates`: the production prefix budget,
  retaining its cube and its eighth-power spectral slack sum.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Actual row lookups and the ranges supplied by compressed-bin and normalized
correction gates. This asserts availability, without asserting recursively accurate children. -/
@[expose] def ResidualEndpointGates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : Option ℕ → Prop
  | some i =>
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)
    ∃ child : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
        Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _), row history m q = some (child q)) ∧
      (∀ σ x y, |child Q.direct σ x y| ≤ 2 * B.binCap) ∧
      (∀ σ x z, |child Q.left σ x z| ≤ B.atomCap) ∧
      (∀ σ z y, |child Q.right σ z y| ≤ 2 * B.binCap)
  | none =>
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
    ∃ A, row history m q = some A ∧ ∀ σ x y, |A σ x y| ≤ B.atomCap

/-- Positive endpoint error against the genuine reference, including the once-negative
ray with its terminal usage and exact weight f. No child accuracy is required. -/
theorem residualSample_error_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (hm : 0 < m) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ka : ℕ) (ht : r.terminal.rate = rate ka) (bin : Option ℕ)
    (hg : B.ResidualEndpointGates history m r bin) :
    ∀ σ x y, |(B.sample history m .residual r bin).getD 0 σ x y -
      B.residualCanonicalRay r bin σ x y| ≤
      2 * (match bin with
        | some i => B.positiveCharge r i y
        | none => rate ka * B.atomCap) := by
  cases bin with
  | some i =>
    obtain ⟨child, hrows, hD, hL, hR⟩ := hg
    exact B.positiveSample_residual_error_le_of_gates history m i hm r child hrows hD hL hR
  | none =>
    obtain ⟨A, hrow, hA⟩ := hg
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
    have hu : q.usage.rate = rate ka := by simp [q, midpoint, ht]
    have hr (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding) r.terminal q y = 1 := by
      rw [usageRatio_grid B.padding r.terminal q ka ka ht hu y]
      exact div_self (gridMass_pos (P := P) ka).ne'
    intro σ x y
    rw [sample, ite_eq_right (by omega)]
    dsimp only
    rw [hrow]
    simp only [bind, pure, Option.bind_some, Option.getD_some]
    have hc := B.residualCanonicalChild_correction_abs_le 0 q rfl σ x y
    simp only [residualCanonicalRay, Pi.neg_apply, HierarchyTask.rawNegativeSample,
      HierarchyTask.rawRequests, ← neg_mul]
    change |-(midpoint r).rate * HierarchyTask.usageRatio (channels B.padding)
      r.terminal q y * A σ x y -
      (-(midpoint r).rate * HierarchyTask.usageRatio (channels B.padding)
        r.terminal q y * B.residualCanonicalChild 0 q σ x y)| ≤ _
    rw [hr]
    simp only [midpoint, ht, mul_one]
    calc
      _ ≤ |-(rate ka) * A σ x y| +
          |-(rate ka) * B.residualCanonicalChild 0 q σ x y| := abs_sub _ _
      _ ≤ rate ka * B.atomCap + rate ka * B.atomCap := by
        simp only [abs_mul, abs_neg, abs_of_pos (rate_pos ka)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hA σ x y) (rate_pos ka).le)
          (mul_le_mul_of_nonneg_left hc (rate_pos ka).le)
      _ = _ := by ring

/-- Per-endpoint denominator-preserving fourth moment from actual gate ranges.
The denominator may be arbitrarily small off a retained pair. -/
theorem residualSample_relative_fourth_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m : ℕ) (hm : 0 < m) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (ht : r.terminal.rate = rate ka) (hrate : ∀ i, B.binRate i = rate i)
    (H : Horizon P) (hs : ks ≤ H.maxExponent) (ha : ka ≤ H.maxExponent)
    (bin : Option ℕ) (hg : B.ResidualEndpointGates history m r bin)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let c := match bin with
      | some i => B.positiveCharge r i 0
      | none => rate ka * B.atomCap
    rowNormPow 4 P (rate ks)
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (fun σ x y => ((B.sample history m .residual r bin).getD 0 σ x y -
        B.residualCanonicalRay r bin σ x y) / (rate ka + G x y)) ≤
      4096 * P * c ^ 4 / rate ka ^ 3 := by
  apply B.residualSample_relative_fourth_le_of_abs s t hst ks ka ss st H hs ha _ G hG
  · cases bin with
    | some i => exact B.positiveCharge_nonneg r i 0
    | none => exact mul_nonneg (rate_pos ka).le (by
        unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _))
  · intro σ x y
    have hh := B.residualSample_error_le_of_gates history m hm r ka ht bin hg σ x y
    cases bin with
    | some i => simpa only [B.positiveCharge_grid_const r ka i ht (hrate i)] using hh
    | none => exact hh

/-- Gate ranges pay transported noise through the original production budget.
Both actual positive endpoints are required; zero endpoints need no gates or IH.
The remaining cube and spectral slack sum are displayed, not absorbed in a reserve. -/
theorem rawRelativeNoiseGroup_transported_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal.rate = rate ka) (hks : ka ≤ ks)
    (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (j : ℕ)
    (hg : ∀ i ∈ range j, ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin) :
    B.rawRelativeNoiseBudget M r s t hst ks ka ss st
      (fun i => B.residualTransportedGroupInput history M
        (dyadicSlack (Nat.log2 M + 1) i) r) G j ≤
      (j : ℝ) ^ 3 * ∑ i ∈ range j,
        64 * (((2 : ℝ) ^ (-B.requestPrecision M r)) *
          (64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) i) ^ 8 := by
  apply B.rawRelativeNoiseBudget_transported_le_of_abs history M r s t hst ks ka ss st hs hks
    H hsource G hG j
  intro i hi
  apply B.residualTransportedGroupInput_abs_le_magnitude_div history M _ r ka ht hrate
  intro bin hb m hm hmc σ x y
  have hh := B.residualSample_error_le_of_gates history m hm r ka ht bin
    (hg i hi bin hb m hm hmc) σ x y
  cases bin with
  | none => exact hh
  | some b =>
    have hbin : b ∈ B.bins := by
      simpa only [rays, List.mem_append, List.mem_map, mem_toList, List.mem_singleton,
        Option.some.injEq, Option.some_ne_none, or_false, exists_eq_right] using hb
    simpa only [B.positiveCharge_grid_const r ka b ht (hrate b hbin)] using hh

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
