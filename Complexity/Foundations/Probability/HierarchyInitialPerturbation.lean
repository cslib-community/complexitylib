/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyApproximateHistory
public import Complexity.Foundations.Probability.RootMetric.FiniteEnvelope
public import Complexity.Foundations.Probability.RootMetric.ClippedMean
public import Complexity.Foundations.Probability.HierarchyInitialMean
import Complexity.Foundations.Data.List.Blocks
import Complexity.Foundations.Probability.GridRowMoment.Rate
import Complexity.Foundations.Probability.HierarchyInitialFeasibility

/-!
# Executed initial group and prefix perturbations

Finite payments sum the actual paired rays before their common completion, then the
executed groups before parent compression. These original finite comparisons retain the
computed history and its changing budgets. They do not prove the simultaneous child IH
or replace production dense leaves. Positive carried-child clipped means integrate onto
own-request rooted precision before signed pairing and correlated prefix addition. The
piecewise coefficient retains rounded masses and sharp fine-bin decay. Actual scheduled
precision pays both endpoints with an explicit slack window. Finite Minkowski removes
bin and prefix cardinality cubes from clipped means. A numerical window condition pays
the finite prefix; its uniform absorption, ordinary sampling progress and saturated
preparation remain separate obligations.
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

/-- Clipped conditional accuracy of a literal positive carried child. Canonical polynomial
support proves domination by `2 * binCap * base`, before any fine/coarse subtraction.
The approximate child can be nonzero at zero target. Reset-right execution is still required.
This local estimate does not pay centered sampling or the second preparation coordinate. -/
theorem positiveSample_initial_compressed_clipped_mean
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hbin : bin ≤ H.maxExponent)
    (hprep : ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      ∀ x y,
        min 1 (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
          (rate ka + B.base x y)) ^ 4 ≤
        (512 * (6 * B.binCap + 3) ^ 3) *
          (B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
            r.terminal Q.direct y / rate ka) *
          𝔼 σ ∈ ({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)),
            |D σ x y ^ (4⁻¹ : ℝ) - C σ x y ^ (4⁻¹ : ℝ)| ^ 4 := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
    HP.ρ HP.K B.base
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let b := fun y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y
  let A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun σ x y => b y * D σ x y
  refine ⟨A, (B.positiveSample_initial_compressed exponent ζ floor M m bin hm r D R hd hr).1,
    ?_⟩
  intro x y
  let S : Finset (Environment P 3) := {σ | Xs σ x ∧ Ya σ y}
  have hb : 0 ≤ b y := by
    dsimp only [b, HierarchyTask.usageRatio]
    rw [hrate]
    exact mul_nonneg (rate_pos bin).le (by positivity)
  have hcanonical : rowSliceMean Xs Ya (B.initialSample r bin) x y =
      B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) :=
    B.initialSample_mean hD H r s t hst ks ka bin bin ss st hs ht hks hbin
      (congrFun hrate bin) hprep hC hC1 hK x y
  have hdom : B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) ≤
      2 * B.binCap * B.base x y := by
    by_cases hz : B.cutoff bin (B.base x y / B.binRate bin) = 0
    · rw [hz, mul_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) B.binCap_nonneg) (hC x y)
    have hsupport : rate bin / 2 < B.base x y := by
      by_contra hn
      apply hz
      rw [hrate, hcutoff]
      apply boundedRoutedBinCutoff_eq_zero (by norm_num)
        (fun v hv => polynomialSwitch4_of_le (by norm_num) hv) rate_pos rate_antitone
      apply (div_le_iff₀ (rate_pos bin)).mpr
      linarith [not_lt.mp hn]
    have hcap := (B.cutoff_bounds bin (B.base x y / B.binRate bin)).2
    rw [hrate] at hcap ⊢
    nlinarith [mul_le_mul_of_nonneg_left hcap (rate_pos bin).le,
      mul_nonneg B.binCap_nonneg (show 0 ≤ 2 * B.base x y - rate bin by linarith)]
  have heq : b y * (𝔼 σ ∈ S, C σ x y) =
      rowSliceMean Xs Ya (B.initialSample r bin) x y := by
    rw [mul_expect]
    rfl
  have hbound : (b y / rate ka) * (𝔼 σ ∈ S, C σ x y) ≤
      (2 * B.binCap) * (B.base x y / rate ka) := by
    rw [div_mul_eq_mul_div, heq, hcanonical]
    exact (div_le_div_of_nonneg_right hdom (rate_pos ka).le).trans_eq (by ring)
  have hru := B.compressedBin_range_usage m bin (exponent Q.direct) ζ floor Q.direct D hd
  have hlocal := min_relative_expect_sub_four_le S
    (C := fun σ => C σ x y) (A := fun σ => D σ x y)
    (div_nonneg hb (rate_pos ka).le) (div_nonneg (hC x y) (rate_pos ka).le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) B.binCap_nonneg)
    (fun σ _ => (normalizedRequest_mem_Icc HP B.padding Q.direct (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) _ _ σ x y).1)
    (fun σ _ => (hru.1 σ x y).1) hbound
  have hmean : rowSliceMean Xs Ya (A - B.initialSample r bin) x y =
      b y * (𝔼 σ ∈ S, (D σ x y - C σ x y)) := by
    rw [mul_expect]
    apply expect_congr rfl
    intro σ _
    change b y * D σ x y - b y * C σ x y = _
    ring
  rw [hmean]
  have he : |(b y / rate ka) * (𝔼 σ ∈ S, (D σ x y - C σ x y))| /
      (1 + B.base x y / rate ka) =
      |b y * (𝔼 σ ∈ S, (D σ x y - C σ x y))| / (rate ka + B.base x y) := by
    rw [div_mul_eq_mul_div, abs_div, abs_of_pos (rate_pos ka), div_div]
    congr 1
    field_simp [(rate_pos ka).ne']
  rw [he] at hlocal
  convert hlocal using 1; ring

/-- Moment coefficient for a positive initial clipped mean. Coarse bins use canonical
mean domination. Fine bins use bounded ordinary conversion and exact terminal density
normalization; on the rate-16 grid their norm factor decays cubically in base two. -/
@[expose] def initialClippedRootCoefficient (ka bin : ℕ) : ℝ :=
  if bin ≤ ka then
    (512 * (6 * B.binCap + 3) ^ 3) *
      (rate bin * (gridMass P ka / gridMass P (max ka bin)) / rate ka)
  else
    (2048 * B.binCap ^ 3) *
      ((rate bin / rate ka) ^ 4 * (gridMass P ka / gridMass P bin))

omit [Fact P.Prime] in
/-- Both branches of the actual rounded-mass coefficient are nonnegative. -/
lemma initialClippedRootCoefficient_nonneg (ka bin : ℕ) :
    0 ≤ B.initialClippedRootCoefficient ka bin := by
  unfold initialClippedRootCoefficient
  have hc := B.binCap_nonneg
  have hm (k : ℕ) : 0 ≤ gridMass P k := by unfold gridMass; positivity
  split_ifs
  · exact mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (rate_pos bin).le (div_nonneg (hm ka) (hm _))) (rate_pos ka).le)
  · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (div_nonneg (hm ka) (hm bin)))

/-- Fine-bin fourth moments decay with the cube of the nominal rate ratio. The factor
sixteen is the actual rounded-grid comparison, not an assumed rate/mass equality. -/
lemma initialClippedRootCoefficient_fine_le (H : Horizon P) (ka bin : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent) (hf : ka < bin) :
    B.initialClippedRootCoefficient ka bin ≤
      (32768 * B.binCap ^ 3) * (rate bin / rate ka) ^ 3 := by
  rw [initialClippedRootCoefficient, ite_eq_right (not_le.mpr hf)]
  have hc := B.binCap_nonneg
  have hm := gridMass_bounds H ha
  have hn := gridMass_bounds H hi
  have hratio : gridMass P ka / gridMass P bin ≤ 16 * rate ka / rate bin :=
    (div_le_div_of_nonneg_left (hm.1.trans' (rate_pos ka).le) (rate_pos bin) hn.1).trans
      (div_le_div_of_nonneg_right hm.2 (rate_pos bin).le)
  calc
    _ ≤ (2048 * B.binCap ^ 3) * ((rate bin / rate ka) ^ 4 *
        (16 * rate ka / rate bin)) := by
      gcongr
    _ = _ := by field_simp [(rate_pos ka).ne', (rate_pos bin).ne']; ring

private lemma rate_ratio_two_rpow (ka bin : ℕ) :
    rate bin / rate ka = (2 : ℝ) ^ (4 * ((ka : ℝ) - bin)) := by
  have he (k : ℕ) : rate k = (2 : ℝ) ^ (-4 * (k : ℝ)) := by
    calc
      rate k = ((2 : ℝ) ^ (k : ℝ))⁻¹ ^ 4 := by rw [Real.rpow_natCast]; rfl
      _ = ((2 : ℝ) ^ (-(k : ℝ))) ^ 4 := by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (-4 * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  rw [he, he, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- A uniform moment envelope for the actual piecewise coefficient. Its fourth root
has exponent `a-i` for coarse bins and `-3(i-a)` for fine bins. -/
lemma initialClippedRootCoefficient_le (H : Horizon P) (ka bin : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent) :
    B.initialClippedRootCoefficient ka bin ≤
      max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) *
        ((2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka))) ^ 4 := by
  by_cases hf : bin ≤ ka
  · rw [ite_eq_left hf, initialClippedRootCoefficient, ite_eq_left hf, max_eq_left hf]
    have hm : gridMass P ka ≠ 0 := ne_of_gt ((rate_pos ka).trans_le (gridMass_bounds H ha).1)
    rw [div_self hm, mul_one, rate_ratio_two_rpow,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    have he : 4 * ((ka : ℝ) - bin) = ((ka : ℝ) - bin) * (4 : ℕ) := by norm_num; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply (B.initialClippedRootCoefficient_fine_le H ka bin ha hi (Nat.lt_of_not_ge hf)).trans
    rw [ite_eq_right hf, rate_ratio_two_rpow,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    have he : 4 * ((ka : ℝ) - bin) * (3 : ℕ) =
        -3 * ((bin : ℝ) - ka) * (4 : ℕ) := by norm_num; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Literal positive conditional means integrated onto the direct child's own source
and usage. Rounded grid masses remain in the linear coefficient. This is the coarse
Fubini payment; it does not claim the sharper fine-bin cubic decay or pay sampling noise. -/
private theorem positiveSample_initial_compressed_clipped_root_coarse
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hbin : bin ≤ H.maxExponent)
    (hprep : ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
          (rate ka + B.base x y))) ≤
        (512 * (6 * B.binCap + 3) ^ 3) *
          (rate bin * (gridMass P ka / gridMass P (max ka bin)) / rate ka) *
        rootDistPow 4 P Q.direct.source.rate
          (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
          (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
    HP.ρ HP.K B.base
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  obtain ⟨A, hA, he⟩ := B.positiveSample_initial_compressed_clipped_mean hrate hcutoff hD H
    exponent ζ floor M m bin hm r s t hst ks ka ss st hs ht hks hbin hprep hC hC1 hK D R hd hr
  refine ⟨A, hA, ?_⟩
  have hratio (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y = gridMass P ka / gridMass P (max ka bin) := by
    apply usageRatio_grid B.padding r.terminal Q.direct ka (max ka bin) (by rw [ht]; rfl)
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate]
    exact rate_min ka bin
  have hx : (fun σ x => Q.direct.source.retains (channels B.padding) σ x) = Xs := by
    funext σ x
    simp only [Q, HierarchyTask.rawRequests, hs, Xs, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X]
  have hru := B.compressedBin_range_usage m bin (exponent Q.direct) ζ floor Q.direct D hd
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  change rowNormPow 4 P r.source.rate Xs Ya _ ≤ _
  change rowNormPow 4 P r.source.rate Xs Ya _ ≤
    _ * rootDistPow 4 P r.source.rate
      (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
      (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C
  simp only [hx]
  apply rowNormPow_le_rootDistPow_of_conditional hNu Xs Ya
    (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C _ _ (by
      have hg : 0 ≤ gridMass P ka / gridMass P (max ka bin) := by unfold gridMass; positivity
      exact mul_nonneg (by have hcap := B.binCap_nonneg; positivity)
        (div_nonneg (mul_nonneg (rate_pos bin).le hg)
        (rate_pos ka).le))
  · intro σ x y hy
    rw [hru.2 σ x y hy]
    exact (normalizedRequest_zero_off_usage B.padding id Q.direct _ _ _ _ _ σ x y hy).symm
  · intro x y
    rw [abs_of_nonneg (show 0 ≤ min 1
      (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| / (rate ka + B.base x y)) by
        have hp := rate_pos ka; have hg := hC x y; positivity)]
    have h := he x y
    change _ ≤ (512 * (6 * B.binCap + 3) ^ 3) *
      (B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y /
        rate ka) * _ at h
    rw [hratio y, hrate] at h
    simpa only [hrate, Q, C, Xs, Ya] using h

/-- Fine bins use bounded ordinary conversion on their own usage slice before
changing terminal normalization. Rounded masses occur once, rather than to the fourth power. -/
private theorem positiveSample_initial_compressed_clipped_root_fine
    (hrate : B.binRate = rate)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hfine : ka ≤ bin) (hC : ∀ x y, 0 ≤ B.base x y)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
          (rate ka + B.base x y))) ≤
        (2048 * B.binCap ^ 3) *
          ((rate bin / rate ka) ^ 4 * (gridMass P ka / gridMass P bin)) *
        rootDistPow 4 P Q.direct.source.rate
          (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
          (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
    HP.ρ HP.K B.base
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let U := Y t (side P bin) (CopyPadding.identifier B.padding st)
  let q := gridMass P bin / gridMass P ka
  let b := rate bin * (gridMass P ka / gridMass P bin)
  have hmpos (k : ℕ) : 0 < gridMass P k := by
    unfold gridMass
    exact pow_pos (div_pos (by exact_mod_cast side_pos P k (Fact.out : P.Prime).pos)
      (by exact_mod_cast (Fact.out : P.Prime).pos)) 4
  have hq : 0 < q := div_pos (hmpos bin) (hmpos ka)
  have hb : 0 ≤ b := mul_nonneg (rate_pos bin).le (div_pos (hmpos ka) (hmpos bin)).le
  have hu : (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) = U := by
    funext σ y
    simp only [Q, HierarchyTask.rawRequests, ht, hrate, gridChannel, rate_min,
      max_eq_right hfine, CorrectionRowTask.Channel.retains, channels, semanticSide_grid, U, Y]
  have hx : (fun σ x => Q.direct.source.retains (channels B.padding) σ x) = Xs := by
    funext σ x
    simp only [Q, HierarchyTask.rawRequests, hs, Xs, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X]
  have hratio (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y = gridMass P ka / gridMass P bin := by
    apply usageRatio_grid B.padding r.terminal Q.direct ka bin (by rw [ht]; rfl)
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate]
    exact (rate_min ka bin).trans (congrArg rate (max_eq_right hfine))
  obtain ⟨hA, _⟩ := B.positiveSample_initial_compressed exponent ζ floor M m bin hm r D R hd hr
  let A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun σ x y => b * D σ x y
  refine ⟨A, ?_, ?_⟩
  · convert hA using 1
    congr 1
    change A = (fun σ x y => B.binRate bin *
      HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * D σ x y)
    funext σ x y
    rw [hratio, hrate]
  have hru := B.compressedBin_range_usage m bin (exponent Q.direct) ζ floor Q.direct D hd
  have hoff (σ : Environment P 3) (x y : ZMod P) (hy : ¬ U σ y) :
      D σ x y = C σ x y := by
    rw [← hu] at hy
    rw [hru.2 σ x y hy]
    exact (normalizedRequest_zero_off_usage B.padding id Q.direct _ _ _ _ _ σ x y hy).symm
  have hside : side P bin ≤ side P ka := by
    rw [side_eq_ceil, side_eq_ceil]
    gcongr
    norm_num
  have hsub (σ : Environment P 3) (y : ZMod P) : U σ y → Ya σ y := by
    intro hy
    apply mem_retentionBox.2
    exact fun i => ((mem_retentionBox.1 hy) i).trans_le hside
  have hdens (k : ℕ) (x y : ZMod P) :
      (({σ | Xs σ x ∧ Y t (side P k) (CopyPadding.identifier B.padding st) σ y} :
        Finset (Environment P 3)).dens : ℝ) = gridMass P ks * gridMass P k := by
    dsimp only [Xs, X, Y]
    have hh := congrArg (fun z : ℚ≥0 => (z : ℝ))
      (independent (P := P) s t hst.symm (side P ks) (side P k)
        (CopyPadding.identifier B.padding ss x) (CopyPadding.identifier B.padding st y))
    have hmarg (j : ℕ) (v : ZMod P) :
        (dens {a : FrameChannel P 4 1 | frameRetains P 4 (side P j) a v} : ℝ) =
          gridMass P j := by
      have hh := congrArg (fun z : ℚ≥0 => (z : ℝ))
        (dens_eval_mem_retentionBox (P := P) (H := 4) (r := 1)
          (by decide) (side_le P j) v)
      push_cast at hh
      simp only [nnratCast_dens] at hh ⊢
      convert hh using 1
      congr 2
    have hl := hmarg ks (CopyPadding.identifier B.padding ss x)
    have hr := hmarg k (CopyPadding.identifier B.padding st y)
    simp only [NNRat.cast_mul, nnratCast_dens] at hh hl hr ⊢
    convert hh.trans (congrArg₂ (· * ·) hl hr) using 1
    congr 2
    apply congrArg Finset.card
    ext σ
    simp only [mem_filter, mem_univ, true_and]
  have hmean (x y : ZMod P) : rowSliceMean Xs Ya (D - C) x y =
      q * rowSliceMean Xs U (D - C) x y := by
    let S : Finset (Environment P 3) := {σ | Xs σ x ∧ Ya σ y}
    let T : Finset (Environment P 3) := {σ | Xs σ x ∧ U σ y}
    have hT : T.Nonempty := by
      apply dens_ne_zero.mp
      have htpos : (0 : ℝ) < T.dens := by
        change 0 < (({σ | Xs σ x ∧ U σ y} : Finset (Environment P 3)).dens : ℝ)
        rw [hdens bin]
        exact mul_pos (hmpos ks) (hmpos bin)
      exact_mod_cast htpos.ne'
    have hh := expect_mul_dens_div_of_subset (S := S) (T := T)
      (by intro σ hσ; simp only [S, T, mem_filter, mem_univ, true_and] at hσ ⊢
          exact ⟨hσ.1, hsub σ y hσ.2⟩) hT
      (fun σ => D σ x y - C σ x y)
      (by intro σ hσ hn
          have hy : ¬ U σ y := by
            simp only [S, mem_filter, mem_univ, true_and] at hσ
            simpa only [T, mem_filter, mem_univ, true_and, hσ.1, true_and] using hn
          exact sub_eq_zero.mpr (hoff σ x y hy))
    rw [← mul_expect] at hh
    have hratio : (S.dens : ℝ) / T.dens = q⁻¹ := by
      change (({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)).dens : ℝ) /
        (({σ | Xs σ x ∧ U σ y} : Finset (Environment P 3)).dens : ℝ) = _
      rw [hdens ka, hdens bin]
      dsimp only [q]
      field_simp [(hmpos ks).ne', (hmpos ka).ne', (hmpos bin).ne']
    rw [hratio] at hh
    change (𝔼 σ ∈ S, (D σ x y - C σ x y)) = q * (𝔼 σ ∈ T, (D σ x y - C σ x y))
    rw [← hh, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hj := rowNormPow_sliceMean_change_terminal_fourth_le hNu hq.le Xs Ya U (D - C)
    hmean (by intro x y; rw [hdens ka, hdens bin]; dsimp only [q]; field_simp [(hmpos ka).ne'])
  have hrange := rowNormPow_sub_le_rootDistPow (s := 4) (by decide) hNu
    (X := Xs) (Y := U) (H := D) (H' := C) (C := 2 * B.binCap)
    (fun σ x y _ _ => hru.1 σ x y)
    (fun σ x y _ _ => normalizedRequest_mem_Icc HP B.padding Q.direct (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) _ _ σ x y)
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hrange
  have hroot : ((2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4 = (2 * B.binCap) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg (by norm_num) B.binCap_nonneg)]
    norm_num
  have hfactor : (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4 = 2048 * B.binCap ^ 3 := by
    rw [mul_pow, hroot]
    ring
  rw [hfactor] at hrange
  have heq (x y : ZMod P) : rowSliceMean Xs Ya (A - B.initialSample r bin) x y =
      b * rowSliceMean Xs Ya (D - C) x y := by
    simp only [rowSliceMean]
    rw [mul_expect]
    apply expect_congr rfl
    intro σ _
    change b * D σ x y - B.binRate bin *
      HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * C σ x y = _
    rw [hratio, hrate]
    change b * D σ x y - rate bin * (gridMass P ka / gridMass P bin) * C σ x y =
      b * (D σ x y - C σ x y)
    dsimp only [b]
    ring
  have hclip : rowNormPow 4 P r.source.rate Xs Ya
      (fun _ x y => min 1 (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
        (rate ka + B.base x y))) ≤
      (b / rate ka) ^ 4 * rowNormPow 4 P r.source.rate Xs Ya
        (fun _ => rowSliceMean Xs Ya (D - C)) := by
    apply rowNormPow_le_mul hNu
    intro σ x y _ _
    rw [abs_of_nonneg (show 0 ≤ min 1
      (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
        (rate ka + B.base x y)) by have := hC x y; have := rate_pos ka; positivity)]
    rw [← mul_pow]
    apply pow_le_pow_left₀ (le_min (by norm_num)
      (div_nonneg (abs_nonneg _) (by linarith [rate_pos ka, hC x y])))
    apply (min_le_right _ _).trans
    rw [heq, abs_mul, abs_of_nonneg hb, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg hb (abs_nonneg _)) (rate_pos ka)
      (by linarith [hC x y])
  change _ ≤ _ * rootDistPow 4 P r.source.rate
    (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
    (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C
  simp only [hx, hu]
  apply hclip.trans
  have hh := mul_le_mul_of_nonneg_left
    (hj.trans (mul_le_mul_of_nonneg_left hrange (pow_nonneg hq.le 3)))
    (pow_nonneg (div_nonneg hb (rate_pos ka).le) 4)
  convert hh using 1
  dsimp only [b, q]
  field_simp [(hmpos ka).ne', (hmpos bin).ne', (rate_pos ka).ne']

/-- Sharp piecewise own-request payment for a literal positive clipped mean. The fine
branch changes terminal normalization before Jensen, retaining cubic norm decay. This
controls clipping after the mean and does not pay centered noise or preparation. -/
theorem positiveSample_initial_compressed_clipped_root
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M m bin : ℕ) (hm : m < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hbin : bin ≤ H.maxExponent)
    (hprep : ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hd :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) m bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (A - B.initialSample r bin) x y| /
          (rate ka + B.base x y))) ≤
        B.initialClippedRootCoefficient ka bin *
        rootDistPow 4 P Q.direct.source.rate
          (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
          (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C := by
  by_cases hf : bin ≤ ka
  · simpa only [initialClippedRootCoefficient, ite_eq_left hf] using
      B.positiveSample_initial_compressed_clipped_root_coarse hrate hcutoff hD H exponent
        ζ floor M m bin hm r s t hst ks ka ss st hs ht hks hbin hprep hC hC1 hK D R hd hr
  · simpa only [initialClippedRootCoefficient, ite_eq_right hf] using
      B.positiveSample_initial_compressed_clipped_root_fine hrate exponent ζ floor M m bin hm
        r s t hst ks ka ss st hs ht (Nat.le_of_lt (Nat.lt_of_not_ge hf)) hC D R hd hr

/-- The sharp coefficient and an actual scheduled child's own precision pay a parent
precision with an explicit slack window. Zero children pay zero. This does not absorb
bin/prefix cubes or the separate ordinary-progress and preparation costs. -/
theorem initialClippedRootEndpoint_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M d ks ka bin : ℕ) (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (coefficient : ℝ) :
    let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    B.initialClippedRootCoefficient ka bin * B.initialEndpointCharge m Q.direct coefficient ≤
      max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) * coefficient ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 -
            3 * |(bin : ℝ) - ka| / 4)) ^ 4 := by
  dsimp only
  let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  have hc := B.binCap_nonneg
  by_cases hz : m = 0
  · simp only [show LogSpaceEstimation.lastBudget M d B.slack
      (B.sampleScale r (some bin)) = m from rfl, hz, initialEndpointCharge, ↓reduceIte,
      mul_zero]
    positivity
  rw [show LogSpaceEstimation.lastBudget M d B.slack
    (B.sampleScale r (some bin)) = m from rfl, initialEndpointCharge, ite_eq_right hz]
  have hp := B.requestPrecision_initial_clipped_adjust hcharge hrate M d ks ka bin r hs ht htask
  calc
    _ ≤ (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) *
        ((2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka))) ^ 4) *
          (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4) :=
      mul_le_mul_of_nonneg_right (B.initialClippedRootCoefficient_le H ka bin ha hi)
        (by positivity)
    _ = max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) * coefficient ^ 4 *
        ((2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) *
          (2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 := by ring
    _ ≤ _ := by gcongr

/-- Conditional clipped payment for the two actual scheduled endpoints. Equal budgets
execute zero, and zero endpoints need no child call. Positive endpoints consume strict
own-request rooted precision and separate reset-right availability. -/
theorem pairedSample_initial_compressed_clipped_precision
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hbin : bin ≤ H.maxExponent)
    (hprep : ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (coefficient : ℝ)
    (ih : ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D n) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D n)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision n Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ A C,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some C ∧
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (A - C) x y| /
          (rate ka + B.base x y))) ≤
        if fine = coarse then 0 else
        8 * (B.initialClippedRootCoefficient ka bin) *
          (B.initialEndpointCharge fine Q.direct coefficient +
            B.initialEndpointCharge coarse Q.direct coefficient) := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let w := fun y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y
  let K := B.initialClippedRootCoefficient ka bin
  let E : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun n σ x y => w y * D n σ x y
  let C := fun n => if n = 0 then 0 else B.initialSample r bin
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
  let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hK0 : 0 ≤ K := B.initialClippedRootCoefficient_nonneg ka bin
  have hend (n : ℕ) (hn : n < M) :
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (E n - C n) x y| /
          (rate ka + B.base x y))) ≤ K * B.initialEndpointCharge n Q.direct coefficient := by
    by_cases hz : n = 0
    · subst n
      simp [E, C, hzero, rowSliceMean, rowNormPow, initialEndpointCharge]
    · obtain ⟨hd, he, R, hr⟩ := ih n hn (Nat.pos_of_ne_zero hz)
      obtain ⟨A, hA, hb⟩ := B.positiveSample_initial_compressed_clipped_root hrate hcutoff hD H
        exponent ζ floor M n bin hn r s t hst ks ka ss st hs ht hks hbin hprep hC hC1 hK
        (D n) R hd hr
      have ha : A = E n := Option.some.inj (hA.symm.trans
        (B.positiveSample_initial_compressed exponent ζ floor M n bin hn r (D n) R hd hr).1)
      rw [ha] at hb
      dsimp only [C]
      rw [ite_eq_right hz]
      exact hb.trans (mul_le_mul_of_nonneg_left
        (by simpa only [initialEndpointCharge, ite_eq_right hz] using he) hK0)
  by_cases heq : fine = coarse
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp only [pairedSample, show LogSpaceEstimation.lastBudget M d B.slack
        (B.sampleScale r (some bin)) = LogSpaceEstimation.lastBudget M (2*d) B.slack
          (B.sampleScale r (some bin)) from heq, ↓reduceIte]
    · simp only [pairedSample, show LogSpaceEstimation.lastBudget M d B.slack
        (B.sampleScale r (some bin)) = LogSpaceEstimation.lastBudget M (2*d) B.slack
          (B.sampleScale r (some bin)) from heq, ↓reduceIte]
    · change _ ≤ if fine = coarse then 0 else _
      rw [ite_eq_left heq]
      simp [rowSliceMean, rowNormPow]
  have hp := B.pairedSample_initial_compressed exponent ζ floor M d bin hM r D hzero
    (fun n hn hp => ⟨(ih n hn hp).1, (ih n hn hp).2.2⟩)
  have hp' : B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
      else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some (E fine - E coarse) := by
    rw [hp]
    congr 1
    funext σ x y
    simp only [Pi.sub_apply, Matrix.sub_apply]
    dsimp only [E, w, fine, coarse, Q]
    ring
  refine ⟨E fine - E coarse, C fine - C coarse, hp',
    B.pairedSample_initial M d hM bin r, ?_⟩
  have hm : rowSliceMean Xs Ya ((E fine - E coarse) - (C fine - C coarse)) =
      fun x y => rowSliceMean Xs Ya (E fine - C fine) x y +
        -rowSliceMean Xs Ya (E coarse - C coarse) x y := by
    funext x y
    simp only [rowSliceMean, Pi.sub_apply, Matrix.sub_apply, expect_sub_distrib]
    ring
  rw [hm, ite_eq_right heq]
  have hb := rowNormPow_clipped_add_le hNu Xs Ya
    (rowSliceMean Xs Ya (E fine - C fine))
    (fun x y => -rowSliceMean Xs Ya (E coarse - C coarse) x y)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))
  simp only [abs_neg] at hb
  apply hb.trans
  have hf := hend fine (B.pairedSample_budgets_lt M d hM r (some bin)).1
  have hc := hend coarse (B.pairedSample_budgets_lt M d hM r (some bin)).2
  change _ ≤ 8 * K * (_ + _)
  nlinarith

/-- Actual initial group assembly from its executed paired rays, on the requested grid.
This identity is shared by ordinary progress and clipped-mean analysis. -/
theorem completedGroup_initial_of_paired
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (T : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hT : ∀ i ∈ B.bins, B.pairedSample history M d (.pilotInput ⟨0, HP.k_pos⟩)
      r (some i) = some (T i)) :
    B.completedGroup history M d (.pilotInput ⟨0, HP.k_pos⟩) r =
      some (conditionalWalk
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ku) (CopyPadding.identifier B.padding su))
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r d) (fun σ x y => ∑ i ∈ B.bins, T i σ x y)) := by
  have he : (B.rays (.pilotInput ⟨0, HP.k_pos⟩)).isEmpty = false := by
    simp only [rays, List.append_nil, List.isEmpty_map]
    exact Bool.eq_false_iff.mpr hbins.not_empty_toList
  unfold completedGroup
  rw [he]
  simp only [Bool.false_eq_true, ↓reduceIte, rays, List.append_nil, List.mapM_map]
  have hm : B.bins.toList.mapM
      (fun i => B.pairedSample history M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i)) =
      some (B.bins.toList.map T) := by
    apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i hi => hT i (mem_toList.mp hi)
  simp only [Function.comp_def]
  rw [hm]
  simp only [bind, Option.bind_some, List.map_map, Function.comp_def,
    Finset.sum_map_toList]
  exact B.complete_grid M r s t hst ks ku ss su hs hu _ d

/-- Sum all actual initial paired rays before completion. Each ray certificate must
identify the executed compressed history and the executed semantic history at this group's
budgets. Its error can be supplied by `pairedSample_initial_compressed_root`. The common
walk contracts their sum; correlation costs only the cube of the number of bins. -/
theorem completedGroup_initial_compressed_error
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (A i))
    (hC : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (C i))
    (herr : ∀ i ∈ B.bins, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y) (A i - C i) ≤ ε i) :
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (F - G) ≤
        (#B.bins : ℝ) ^ 3 * ∑ i ∈ B.bins, ε i := by
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
  let graphV := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  let walk := conditionalWalk Xs Yu graphV (fun _ _ => B.steps M r d)
  let sumA : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun σ x y => ∑ i ∈ B.bins, A i σ x y
  let sumC : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun σ x y => ∑ i ∈ B.bins, C i σ x y
  have hrun := fun history T hT => B.completedGroup_initial_of_paired history M d hbins
    r s t hst ks ku ss su hs hu T hT
  refine ⟨walk sumA, walk sumC, hrun _ A hA, hrun _ C hC, ?_⟩
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hcontract := rowNormPow_conditionalWalk_sub_fourth_le Xs Yu hNu graphV
    (fun _ _ => B.steps M r d) sumA sumC
  have hx : (fun σ x => r.source.retains (channels B.padding) σ x) = Xs := by
    funext σ x
    simp only [hs, Xs, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, X]
  have hy : (fun σ y => r.usage.retains (channels B.padding) σ y) = Yu := by
    funext σ y
    simp only [hu, Yu, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, Y]
  have hc : rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y) (walk sumA - walk sumC) ≤
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (sumA - sumC) := by
    simpa only [hx, hy] using hcontract
  apply hc.trans
  have he : sumA - sumC = fun σ x y => ∑ i ∈ B.bins, (A i - C i) σ x y := by
    funext σ x y
    simp only [sumA, sumC, Pi.sub_apply, Matrix.sub_apply, sum_sub_distrib]
  rw [he]
  apply (rowNormPow_sum_fourth_le B.bins hNu _ _ (fun i => A i - C i)).trans
  exact mul_le_mul_of_nonneg_left (sum_le_sum herr) (by positivity)

/-- Stationarity transfers signed paired clipped means through the actual completion.
No contraction or independence argument is applied to a clipped sampling error. -/
theorem completedGroup_initial_compressed_clipped_mean
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ka st)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (A i))
    (hC : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (C i))
    (a : ZMod P → ZMod P → ℝ) (ha : ∀ x y, 0 < a x y)
    (herr : ∀ i ∈ B.bins,
      rowNormPow 4 P r.source.rate
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ka) (CopyPadding.identifier B.padding st))
        (fun _ x y => min 1 (|rowSliceMean
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ka) (CopyPadding.identifier B.padding st)) (A i - C i) x y| /
          a x y)) ≤ ε i) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate Xs Ya
        (fun _ x y => min 1 (|rowSliceMean Xs Ya (F - G) x y| / a x y)) ≤
        (∑ i ∈ B.bins, ε i ^ (4⁻¹ : ℝ)) ^ 4 := by
  dsimp only
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let graphV := graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
  let walk := conditionalWalk Xs Ya graphV (fun _ _ => B.steps M r d)
  let sumA : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun σ x y => ∑ i ∈ B.bins, A i σ x y
  let sumC : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun σ x y => ∑ i ∈ B.bins, C i σ x y
  refine ⟨walk sumA, walk sumC,
    B.completedGroup_initial_of_paired _ M d hbins r s t hst ks ka ss st hs hu A hA,
    B.completedGroup_initial_of_paired _ M d hbins r s t hst ks ka ss st hs hu C hC, ?_⟩
  have he : rowSliceMean Xs Ya (walk sumA - walk sumC) =
      fun x y => ∑ i ∈ B.bins, rowSliceMean Xs Ya (A i - C i) x y := by
    funext x y
    rw [← conditionalWalk_sub, rowSliceMean_conditionalWalk]
    simp only [rowSliceMean, sumA, sumC, Pi.sub_apply, Matrix.sub_apply,
      ← sum_sub_distrib, expect_sum_comm]
  rw [he]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  exact rowNormPow_clipped_sum_le_pow_sum B.bins hNu Xs Ya
    (fun i => rowSliceMean Xs Ya (A i - C i)) a ha ε herr

/-- Clipped conditional-mean cost at the actual fine/coarse budgets, summed by finite
Minkowski without a bin-count cube. The rounded coefficient uses sharp fine-bin decay.
Equal and exhausted endpoints retain exact zero charges. -/
@[expose] def initialClippedRootGroupCharge
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ka : ℕ) (coefficient : ℝ) : ℝ :=
  (∑ bin ∈ B.bins, (
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    if fine = coarse then 0 else
    8 * (B.initialClippedRootCoefficient ka bin) *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)) ^ (4⁻¹ : ℝ)) ^ 4

/-- Both actual endpoint slacks in the cardinality-free finite allocation. Equal
budgets cost zero; no child accuracy occurs in this numerical window. The remaining
slack growth must be paid before a uniform structural-charge claim. -/
@[expose] def initialClippedRootWindow (M d ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  ∑ bin ∈ B.bins,
    if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) then 0 else
    (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0 then 0 else
      (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 - 3 * |(bin : ℝ) - ka| / 4)) +
      (if LogSpaceEstimation.lastBudget M (2 * d) B.slack
        (B.sampleScale r (some bin)) = 0 then 0 else
        (2 : ℝ) ^ (((2 * d : ℕ) : ℝ) / (16 * B.slack) + 1 / 16 -
          3 * |(bin : ℝ) - ka| / 4))

/-- Sharp scheduled endpoints pay an actual completed-group mean without a bin-count
cube. The explicit finite window retains both endpoint losses and the original guards.
No centered-noise or preparation conclusion follows. -/
theorem initialClippedRootGroupCharge_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M d ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (coefficient : ℝ) :
    B.initialClippedRootGroupCharge M d r ka coefficient ≤
      (2 * (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
        (4⁻¹ : ℝ) * |coefficient| *
        (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        B.initialClippedRootWindow M d ka r) ^ 4 := by
  let C := max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
  let K := C ^ (4⁻¹ : ℝ) * |coefficient| *
    (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let w := fun (δ bin : ℕ) =>
    if LogSpaceEstimation.lastBudget M δ B.slack (B.sampleScale r (some bin)) = 0 then 0 else
      (2 : ℝ) ^ ((δ : ℝ) / (16 * B.slack) + 1 / 16 - 3 * |(bin : ℝ) - ka| / 4)
  have hcap := B.binCap_nonneg
  have hC : 0 ≤ C := le_trans (by positivity : 0 ≤ 32768 * B.binCap ^ 3) (le_max_right _ _)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKpow : K ^ 4 = C * coefficient ^ 4 *
      ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)) ^ 4 := by
    have hc : (C ^ (4⁻¹ : ℝ)) ^ 4 = C := by
      convert Real.rpow_inv_natCast_pow (n := 4) hC (by decide) using 1
    dsimp only [K]
    rw [mul_pow, mul_pow, mul_pow, hc, (by decide : Even 4).pow_abs coefficient]
    ring
  have he (δ bin : ℕ) (hb : bin ∈ B.bins) :
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      let m := LogSpaceEstimation.lastBudget M δ B.slack (B.sampleScale r (some bin))
      B.initialClippedRootCoefficient ka bin * B.initialEndpointCharge m Q.direct coefficient ≤
        (K * w δ bin) ^ 4 := by
    by_cases hz : LogSpaceEstimation.lastBudget M δ B.slack
        (B.sampleScale r (some bin)) = 0
    · simp only [hz, initialEndpointCharge, ↓reduceIte, w, mul_zero, zero_pow (by decide : 4 ≠ 0)]
      exact le_rfl
    have hh := B.initialClippedRootEndpoint_le hcharge hrate H M δ ks ka bin ha (hi bin hb)
      r hs ht htask coefficient
    convert hh using 1
    rw [mul_pow, hKpow]
    simp only [w, ite_eq_right hz]
    dsimp only [C]
    ring
  unfold initialClippedRootGroupCharge
  apply pow_le_pow_left₀ (sum_nonneg fun bin _ => by
    apply Real.rpow_nonneg
    dsimp only
    split_ifs
    · exact le_rfl
    exact mul_nonneg (mul_nonneg (by norm_num) (B.initialClippedRootCoefficient_nonneg _ _))
      (add_nonneg (B.initialEndpointCharge_nonneg _ _ _) (B.initialEndpointCharge_nonneg _ _ _)))
  change _ ≤ 2 * C ^ (4⁻¹ : ℝ) * |coefficient| *
    (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
      B.initialClippedRootWindow M d ka r
  rw [show 2 * C ^ (4⁻¹ : ℝ) * |coefficient| *
    (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) = 2 * K by
      dsimp only [K]; ring]
  rw [initialClippedRootWindow, mul_sum]
  apply sum_le_sum
  intro bin hb
  dsimp only
  by_cases hz : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  · simp only [ite_eq_left hz, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), mul_zero, le_refl]
  rw [ite_eq_right hz, ite_eq_right hz]
  change _ ≤ 2 * K * (w d bin + w (2 * d) bin)
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
  let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  have hwf : 0 ≤ w d bin := by dsimp only [w]; split_ifs <;> positivity
  have hwc : 0 ≤ w (2 * d) bin := by dsimp only [w]; split_ifs <;> positivity
  have hf := he d bin hb
  have hc := he (2 * d) bin hb
  have hsum : 0 ≤ K * (w d bin + w (2 * d) bin) := by positivity
  have hf' : (K * w d bin) ^ 4 ≤ (K * (w d bin + w (2 * d) bin)) ^ 4 := by
    exact pow_le_pow_left₀ (mul_nonneg hK hwf)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hwc) hK) 4
  have hc' : (K * w (2 * d) bin) ^ 4 ≤ (K * (w d bin + w (2 * d) bin)) ^ 4 := by
    exact pow_le_pow_left₀ (mul_nonneg hK hwc)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hwf) hK) 4
  have hh : 8 * B.initialClippedRootCoefficient ka bin *
      (B.initialEndpointCharge f Q.direct coefficient +
        B.initialEndpointCharge c Q.direct coefficient) ≤
      (2 * K * (w d bin + w (2 * d) bin)) ^ 4 := by
    dsimp only at hf hc
    dsimp only [f, c, Q]
    nlinarith [hf', hc']
  have hcoef := B.initialClippedRootCoefficient_nonneg ka bin
  have hff := B.initialEndpointCharge_nonneg f Q.direct coefficient
  have hcc := B.initialEndpointCharge_nonneg c Q.direct coefficient
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 8 * B.initialClippedRootCoefficient ka bin *
      (B.initialEndpointCharge f Q.direct coefficient +
        B.initialEndpointCharge c Q.direct coefficient)) hh (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hroot : ((2 * K * (w d bin + w (2 * d) bin)) ^ 4) ^ (4⁻¹ : ℝ) =
      2 * K * (w d bin + w (2 * d) bin) := by
    convert Real.pow_rpow_inv_natCast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsum)
      (by decide : (4 : ℕ) ≠ 0) using 1 <;> ring
  rw [hroot] at hr
  exact hr

/-- Every actual finite prefix has a numerical scheduled payment without bin or prefix
cardinality cubes. To claim a uniform parent payment one must bound this window sum with
one structural charge fixed before all request exponents and the field width. -/
theorem initialClippedRootPrefix_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M p ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (coefficient : ℝ) :
    (∑ j ∈ range p, (B.initialClippedRootGroupCharge M
      (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) r ka coefficient) ^
        (4⁻¹ : ℝ)) ^ 4 ≤
      (2 * (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
        (4⁻¹ : ℝ) * |coefficient| *
        (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        ∑ j ∈ range p, B.initialClippedRootWindow M
          (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r) ^ 4 := by
  let K := 2 * (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| *
    (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  have hcap := B.binCap_nonneg
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hw (d : ℕ) : 0 ≤ B.initialClippedRootWindow M d ka r := by
    unfold initialClippedRootWindow
    apply sum_nonneg
    intro bin _
    split_ifs <;> positivity
  apply pow_le_pow_left₀ (sum_nonneg fun j _ =>
    Real.rpow_nonneg (by unfold initialClippedRootGroupCharge; positivity) _)
  change _ ≤ K * ∑ j ∈ range p, B.initialClippedRootWindow M
    (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  have hh := Real.rpow_le_rpow
    (by unfold initialClippedRootGroupCharge; positivity)
    (B.initialClippedRootGroupCharge_le hcharge hrate H M
      (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ks ka ha hi r hs ht htask coefficient)
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have he : ((K * B.initialClippedRootWindow M
      (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r) ^ 4) ^ (4⁻¹ : ℝ) =
      K * B.initialClippedRootWindow M
        (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r := by
    convert Real.pow_rpow_inv_natCast (mul_nonneg hK (hw _))
      (by decide : (4 : ℕ) ≠ 0) using 1
  exact hh.trans_eq he

/-- A sufficient joint slack/structural-charge condition for a finite prefix. The condition
is purely numerical and independent of child errors, source precision and field width.
A uniform application must choose the charge first and prove it for every allowed M, p, ka;
this theorem does not assert that the current unbounded schedule satisfies it. -/
theorem initialClippedRootPrefix_paid
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M p ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hwindow : 2 *
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      (∑ j ∈ range p, B.initialClippedRootWindow M
        (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r) ≤
      (2 : ℝ) ^ B.rankCharge) (coefficient : ℝ) :
    (∑ j ∈ range p, (B.initialClippedRootGroupCharge M
      (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) r ka coefficient) ^
        (4⁻¹ : ℝ)) ^ 4 ≤
      coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  apply (B.initialClippedRootPrefix_le hcharge hrate H M p ks ka ha hi r hs ht htask
    coefficient).trans
  have hcancel : (2 : ℝ) ^ (-B.rankCharge) * (2 : ℝ) ^ B.rankCharge = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left hwindow
    (show 0 ≤ |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge) by positivity)
  have hb : 2 *
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
      (∑ j ∈ range p, B.initialClippedRootWindow M
        (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r) ≤
      |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) := by
    calc
      _ ≤ (|coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r)) *
          ((2 : ℝ) ^ (-B.rankCharge) * (2 : ℝ) ^ B.rankCharge) := by
        convert hh using 1 <;> ring
      _ = _ := by rw [hcancel, mul_one]
  have hn : 0 ≤ 2 *
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
      (∑ j ∈ range p, B.initialClippedRootWindow M
        (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ka r) := by
    have hc := B.binCap_nonneg
    apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro j _
    unfold initialClippedRootWindow
    apply sum_nonneg
    intro bin _
    split_ifs <;> positivity
  simpa only [mul_pow, (by decide : Even 4).pow_abs coefficient] using
    pow_le_pow_left₀ hn hb 4

omit [Fact P.Prime] in
/-- Every own-mask clipped group charge is nonnegative. -/
lemma initialClippedRootGroupCharge_nonneg (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ) (coefficient : ℝ) :
    0 ≤ B.initialClippedRootGroupCharge M d r ka coefficient := by
  unfold initialClippedRootGroupCharge
  positivity

omit [Fact P.Prime] in
/-- Exhausted group budgets have zero clipped charge for every request precision. -/
lemma initialClippedRootGroupCharge_eq_zero_of_le (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ) (coefficient : ℝ)
    (hd : M ≤ d) : B.initialClippedRootGroupCharge M d r ka coefficient = 0 := by
  have hf (bin : ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0 :=
    Nat.sub_eq_zero_of_le (hd.trans (le_max_left _ _))
  have hc (bin : ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0 :=
    Nat.sub_eq_zero_of_le ((show M ≤ 2 * d by omega).trans (le_max_left _ _))
  simp only [initialClippedRootGroupCharge, hf, hc, ↓reduceIte,
    Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0),
    sum_const_zero, zero_pow (by decide : 4 ≠ 0)]

/-- Literal group cost from own-request lower-budget precision. Both endpoint budgets,
the sharp fourth-power importance sup norm and the bin cube remain explicit. Zero
endpoints carry zero cost, independently of the coefficient. -/
@[expose] def initialRootGroupCharge
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) : ℝ :=
  (#B.bins : ℝ) ^ 3 * ∑ bin ∈ B.bins,
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    if fine = coarse then 0 else
    8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)

/-- Every literal own-precision group charge is nonnegative, including zero endpoints. -/
lemma initialRootGroupCharge_nonneg (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) :
    0 ≤ B.initialRootGroupCharge M d r coefficient := by
  unfold initialRootGroupCharge
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro bin _
  dsimp only
  split_ifs
  · exact le_rfl
  exact mul_nonneg (by positivity) (add_nonneg
    (B.initialEndpointCharge_nonneg _ _ _) (B.initialEndpointCharge_nonneg _ _ _))

/-- All endpoints vanish when the group slack exhausts the parent budget. This holds
for every coefficient and every request, without an accuracy hypothesis. -/
lemma initialRootGroupCharge_eq_zero_of_le (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) (hd : M ≤ d) :
    B.initialRootGroupCharge M d r coefficient = 0 := by
  have hf (bin : ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0 :=
    Nat.sub_eq_zero_of_le (hd.trans (le_max_left _ _))
  have hc (bin : ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0 :=
    Nat.sub_eq_zero_of_le ((show M ≤ 2 * d by omega).trans (le_max_left _ _))
  simp only [initialRootGroupCharge, hf, hc, ↓reduceIte, sum_const_zero, mul_zero]

/-- All actual initial rays are paid directly by a strict lower-budget own-request
rooted IH at actual precision. Reset-right availability is required on its own request.
The returned completed histories are literal executions, not supplied parent budgets. -/
theorem completedGroup_initial_compressed_precision
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D bin n) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin n)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision n Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (F - G) ≤
        B.initialRootGroupCharge M d r coefficient := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hp (i : {i // i ∈ B.bins}) :=
    B.pairedSample_initial_compressed_precision exponent ζ floor M d i.val hM r hsr
      (D i.val) (hzero i.val) coefficient (ih i.val i.property)
  choose A C hA hC he using hp
  let a := fun i => if hi : i ∈ B.bins then A ⟨i, hi⟩ else 0
  let c := fun i => if hi : i ∈ B.bins then C ⟨i, hi⟩ else 0
  let ε := fun bin =>
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    if fine = coarse then 0 else
    8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)
  exact B.completedGroup_initial_compressed_error exponent ζ floor M d hbins r s t hst
    ks ku ss su hs hu a c ε
    (fun i hi => by simpa only [a, dite_eq_left hi] using hA ⟨i, hi⟩)
    (fun i hi => by simpa only [c, dite_eq_left hi] using hC ⟨i, hi⟩)
    (fun i hi => by simpa only [a, c, dite_eq_left hi] using he ⟨i, hi⟩)

/-- Executed group certificates control every actual prefix before parent compression.
Both lists are the results of the literal history computations, in scheduler order. The
finite prefix payment retains every group cost and the cube of the executed prefix length;
it is not a certificate about an independently supplied prefix family. -/
theorem initial_compressed_prefix_error
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) r = some (A j))
    (hC : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) r = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups reference,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
          else none) M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
          (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
          M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
          (.pilotInput ⟨0, HP.k_pos⟩) r) = some reference ∧
      (∀ p ≤ Nat.log2 M + 1, rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => ((groups.take p).map (fun T => T σ x y)).sum -
          ((reference.take p).map (fun T => T σ x y)).sum) ≤
        (p : ℝ) ^ 3 * ∑ j ∈ range p, ε j) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun _ => finiteEnvelope (range (Nat.log2 M + 2)) (fun _ => 1)
          (fun p => rowSliceMean
            (fun σ x => r.source.retains (channels B.padding) σ x)
            (fun σ y => r.usage.retains (channels B.padding) σ y)
            (fun σ x y => ((groups.take p).map (fun T => T σ x y)).sum -
              ((reference.take p).map (fun T => T σ x y)).sum))) ≤
        ∑ p ∈ range (Nat.log2 M + 2), (p : ℝ) ^ 3 * ∑ j ∈ range p, ε j := by
  refine ⟨(List.range (Nat.log2 M + 1)).map A,
    (List.range (Nat.log2 M + 1)).map C, ?_, ?_, ?_⟩
  · apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun j hj => hA j (List.mem_range.mp hj)
  · apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun j hj => hC j (List.mem_range.mp hj)
  · let E : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun p σ x y =>
      ((((List.range (Nat.log2 M + 1)).map A).take p).map (fun T => T σ x y)).sum -
      ((((List.range (Nat.log2 M + 1)).map C).take p).map (fun T => T σ x y)).sum
    have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
    have hpref (p : ℕ) (hp : p ≤ Nat.log2 M + 1) : rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (E p) ≤
        (p : ℝ) ^ 3 * ∑ j ∈ range p, ε j := by
      dsimp only [E]
      simp only [← List.map_take, List.take_range, min_eq_left hp, List.map_map,
        Function.comp_def, List.sum_map_range_eq_sum_range, ← sum_sub_distrib]
      have h := rowNormPow_sum_fourth_le (range p)
        (mul_nonneg (Nat.cast_nonneg P) hs)
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (fun j => A j - C j)
      simp only [card_range, Pi.sub_apply, Matrix.sub_apply] at h
      apply h.trans
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun j hj =>
        herr j ((mem_range.mp hj).trans_le hp)) (by positivity)
    refine ⟨hpref, ?_⟩
    apply (rowNormPow_finiteEnvelope_le (range (Nat.log2 M + 2)) (fun _ => 1)
      (fun p => rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (E p)) _ _ hNu).trans
    apply sum_le_sum
    intro p hp
    simp only [div_one]
    exact (rowNormPow_sliceMean_fourth_le hNu _ _ (E p)).trans
      (hpref p (by have h := mem_range.mp hp; omega))

/-- Literal correlated prefixes from clipped group-mean payments. This carries no raw
sampling or preparation conclusion. The source and terminal conditioning remain joint. -/
theorem initial_compressed_prefix_clipped_mean
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) r = some (A j))
    (hC : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
        (.pilotInput ⟨0, HP.k_pos⟩) r = some (C j))
    (a : ZMod P → ZMod P → ℝ) (ha : ∀ x y, 0 < a x y)
    (herr : ∀ j < Nat.log2 M + 1,
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.usage.retains (channels B.padding) σ y) (A j - C j) x y| /
          a x y)) ≤ ε j) :
    let Xs := fun σ x => r.source.retains (channels B.padding) σ x
    let Ya := fun σ y => r.usage.retains (channels B.padding) σ y
    ∃ groups reference,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
          else none) M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
          (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
          M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j)
          (.pilotInput ⟨0, HP.k_pos⟩) r) = some reference ∧
      ∀ p ≤ Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate Xs Ya
          (fun _ x y => min 1 (|rowSliceMean Xs Ya
            (fun σ x y => ((groups.take p).map (fun T => T σ x y)).sum -
              ((reference.take p).map (fun T => T σ x y)).sum) x y| / a x y)) ≤
          (∑ j ∈ range p, ε j ^ (4⁻¹ : ℝ)) ^ 4 := by
  dsimp only
  refine ⟨(List.range (Nat.log2 M + 1)).map A,
    (List.range (Nat.log2 M + 1)).map C, ?_, ?_, ?_⟩
  · apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun j hj => hA j (List.mem_range.mp hj)
  · apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun j hj => hC j (List.mem_range.mp hj)
  · intro p hp
    simp only [← List.map_take, List.take_range, min_eq_left hp, List.map_map,
      Function.comp_def, List.sum_map_range_eq_sum_range, ← sum_sub_distrib]
    have hm : rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => ∑ j ∈ range p, (A j σ x y - C j σ x y)) =
        fun x y => ∑ j ∈ range p, rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.usage.retains (channels B.padding) σ y) (A j - C j) x y := by
      funext x y
      simp only [rowSliceMean, expect_sum_comm, Pi.sub_apply, Matrix.sub_apply]
    rw [hm]
    exact rowNormPow_clipped_sum_le_pow_sum (range p) (mul_nonneg (Nat.cast_nonneg P) hs)
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
      (fun j => rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (A j - C j)) a ha ε
      (fun j hj => herr j ((mem_range.mp hj).trans_le hp))

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
