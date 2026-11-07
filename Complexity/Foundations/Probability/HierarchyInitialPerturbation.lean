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
import Complexity.Foundations.Probability.GridRowMoment.JointDensity
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
bin and prefix cardinality cubes from clipped means. The literal signed conditional mean
telescopes before root bounds, leaving only one fine endpoint per bin and a proved zero
start boundary. A bounded surviving slack has a uniform two-sided scale allocation.
Finite weighted endpoint moments retain the compression coefficients; a live endpoint
gives a necessary growth condition for allocating the unconditional rooted tail.
The slope-one window envelope permits deterministic rarity allocation in the computed
reserve; ordinary sampling progress and saturated preparation remain separate obligations.
`completedGroup_initial_compressed_centered_precision` retains spectral contraction on
the actual input difference. `initialRootGroupCharge_le_active` feeds sharp active-pair
own-precision cancellation into that completed-group consumer. Rounded-importance and
bounded full-bin envelopes support the correlated prefix allocation in
`HierarchyTransportedPreparation`. `initial_normalized_importance_precision_le` cancels
absolute terminal exponents pointwise before sup norms; its active-pair variant retains
geometric bin-offset decay. Literal normalized positive/paired samples retain this joint
coefficient through own-mask row conversion. Finite Minkowski and actual completion
contract these moments uniformly over unbounded horizons, with residual norm decay
`16⁻ᵈ`. The earlier counted charge remains a fallback.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression
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
    simpa only [Xs, X, Y, NormalizedMoments.retainedMask] using
      grid_joint_density B.padding s t hst ks k ss st x y
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

/-- Exact signed telescope of successful literal samples, after stationarity of each
completed group. Walk lengths may differ. A shared endpoint is the very same `sample`
call (including history, request, bin and raw budget); no coherence of arbitrary endpoint
approximations is assumed. Equal-budget groups execute zero without calling either child.
Availability of the samples used below is explicit, including the zero boundary. -/
theorem initial_sample_prefix_mean
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ka st)
    (E : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hE : ∀ bin ∈ B.bins, ∀ n < M,
      B.sample history n (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some (E bin n)) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j => B.completedGroup history M
        (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      ∀ j < Nat.log2 M + 1, ∀ x y,
        rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ka) (CopyPadding.identifier B.padding st))
          (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) x y =
        ∑ bin ∈ B.bins, rowSliceMean
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ka) (CopyPadding.identifier B.padding st))
          (E bin (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some bin))) -
           E bin (LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0)
            B.slack (B.sampleScale r (some bin)))) x y := by
  let m := Nat.log2 M + 1
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let endpoint := fun bin d => E bin
    (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)))
  let T := fun j bin => endpoint bin (dyadicSlack m j) - endpoint bin (2 * dyadicSlack m j)
  let A := fun j σ x y => ∑ bin ∈ B.bins, T j bin σ x y
  let G := fun j => conditionalWalk Xs Ya
    (graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
      (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st))
    (fun _ _ => B.steps M r (dyadicSlack m j)) (A j)
  have hp (j bin : ℕ) (hb : bin ∈ B.bins) :
      B.pairedSample history M (dyadicSlack m j) (.pilotInput ⟨0, HP.k_pos⟩)
        r (some bin) = some (T j bin) := by
    unfold pairedSample
    dsimp only
    split_ifs with he
    · simp only [T, endpoint, he, sub_self]
    · rw [hE bin hb _ (LogSpaceEstimation.lastBudget_lt hM B.slack_pos),
        hE bin hb _ (LogSpaceEstimation.lastBudget_lt hM B.slack_pos)]
      rfl
  have hg (j : ℕ) : B.completedGroup history M (dyadicSlack m j)
      (.pilotInput ⟨0, HP.k_pos⟩) r = some (G j) :=
    B.completedGroup_initial_of_paired history M _ hbins r s t hst ks ka ss st hs hu
      (T j) (hp j)
  refine ⟨(List.range m).map G, ?_, ?_⟩
  · apply List.mapM_eq_some_iff_forall₂.mpr
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    exact fun j _ => hg j
  · intro j hj x y
    have htel : ∀ j < m, ∀ bin, ∀ σ x y,
        ∑ i ∈ range (j + 1), T i bin σ x y =
          (endpoint bin (dyadicSlack m j) - endpoint bin (2 * dyadicSlack m 0)) σ x y := by
      intro j hj
      induction j with
      | zero => intro bin σ x y; simp only [Nat.zero_add, sum_range_one, T]
      | succ j ih =>
        intro bin σ x y
        rw [sum_range_succ, ih (by omega)]
        simp only [T, Pi.sub_apply, Matrix.sub_apply]
        rw [dyadicSlack_succ (by omega : j + 1 < m)]
        ring
    change rowSliceMean Xs Ya _ x y = _
    simp only [← List.map_take, List.take_range, min_eq_left (by omega : j + 1 ≤ m),
      List.map_map, Function.comp_def, List.sum_map_range_eq_sum_range]
    simp only [rowSliceMean, expect_sum_comm]
    change (∑ i ∈ range (j + 1), rowSliceMean Xs Ya (G i) x y) = _
    simp_rw [G, rowSliceMean_conditionalWalk]
    simp only [rowSliceMean, A, expect_sum_comm]
    rw [sum_comm]
    apply sum_congr rfl
    intro bin _
    rw [← expect_sum_comm]
    simp_rw [htel j hj bin]
    rfl

/-- Literal compressed initial children supply the endpoint family in the signed mean
telescope. Zero budgets execute zero; positive budgets retain direct precision and the
separately reset right call. Inactive or unavailable positive calls are not filled in. -/
theorem initial_compressed_prefix_mean
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ka st)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0)
    (ih : ∀ bin ∈ B.bins, ∀ n < M, 0 < n →
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin n bin (exponent Q.direct) ζ floor Q.direct = some (D bin n) ∧
      ∃ R, B.compressedBin n bin (exponent Q.right) ζ floor Q.right = some R) :
    let E : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun bin n σ x y =>
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)).direct y * D bin n σ x y
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j => B.completedGroup
        (fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none) M
        (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      ∀ j < Nat.log2 M + 1, ∀ x y,
        rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ka) (CopyPadding.identifier B.padding st))
          (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) x y =
        ∑ bin ∈ B.bins, rowSliceMean
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ka) (CopyPadding.identifier B.padding st))
          (E bin (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some bin))) -
           E bin (LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0)
            B.slack (B.sampleScale r (some bin)))) x y := by
  let E : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun bin n σ x y =>
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
    r.terminal (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)).direct y * D bin n σ x y
  have hE : ∀ bin ∈ B.bins, ∀ n < M,
      B.sample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none)
        n (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some (E bin n) := by
    intro bin hb n hn
    by_cases hz : n = 0
    · subst n
      simp only [sample, ↓reduceIte, E, hzero, Pi.zero_apply, Matrix.zero_apply, mul_zero]
      rfl
    · obtain ⟨hd, R, hr⟩ := ih bin hb n hn (Nat.pos_of_ne_zero hz)
      rw [sample, ite_eq_right hz]
      exact (B.positiveSample_initial_compressed exponent ζ floor M n bin hn r
        (D bin n) R hd hr).1
  exact B.initial_sample_prefix_mean _ M hM hbins r s t hst ks ka ss st hs hu E hE

omit [Fact P.Prime] in
/-- The actual schedule starts strictly above the parent budget. Thus the initial
coarse boundary in the signed telescope is an executed zero sample, for every bin. -/
lemma initial_start_budget (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : ℕ) :
    LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0)
      B.slack (B.sampleScale r (some bin)) = 0 := by
  have h : M < 2 ^ (Nat.log2 M + 1) := Nat.lt_log2_self
  simp only [dyadicSlack, Nat.zero_add, Nat.add_sub_cancel, pow_succ] at h ⊢
  unfold LogSpaceEstimation.lastBudget
  omega

/-- Only the surviving fine endpoints of the exact signed prefix are charged. This
contains no sum over earlier slack windows; exhausted endpoints have zero charge. -/
@[expose] def initialClippedEndpointPrefixCharge
    (M j : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ka : ℕ) (coefficient : ℝ) : ℝ :=
  (∑ bin ∈ B.bins, (
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some bin))
    B.initialClippedRootCoefficient ka bin * B.initialEndpointCharge fine Q.direct coefficient
      ) ^ (4⁻¹ : ℝ)) ^ 4

omit [Fact P.Prime] in
/-- Nonnegativity of the surviving endpoint payment. -/
lemma initialClippedEndpointPrefixCharge_nonneg
    (M j : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ka : ℕ) (coefficient : ℝ) :
    0 ≤ B.initialClippedEndpointPrefixCharge M j r ka coefficient := by
  unfold initialClippedEndpointPrefixCharge
  positivity

/-- The sharp finite window has one surviving endpoint per bin. -/
@[expose] def initialClippedEndpointWindow (M j ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  ∑ bin ∈ B.bins,
    if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
      (B.sampleScale r (some bin)) = 0 then 0 else
      (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack) +
        1 / 16 - 3 * |(bin : ℝ) - ka| / 4)

/-- Own-mask sharp transport pays just the telescoped endpoints. Earlier large slack
windows are absent. This finite inequality does not assert payment of ordinary noise. -/
theorem initialClippedEndpointPrefixCharge_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (coefficient : ℝ) :
    B.initialClippedEndpointPrefixCharge M j r ka coefficient ≤
      ((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
        |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge) * B.initialClippedEndpointWindow M j ka r) ^ 4 := by
  let C := max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
  let K := C ^ (4⁻¹ : ℝ) * |coefficient| *
    (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
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
  unfold initialClippedEndpointPrefixCharge
  apply pow_le_pow_left₀ (sum_nonneg fun bin _ => Real.rpow_nonneg
    (mul_nonneg (B.initialClippedRootCoefficient_nonneg ka bin)
      (B.initialEndpointCharge_nonneg _ _ _)) _) _ 4
  change _ ≤ K * B.initialClippedEndpointWindow M j ka r
  rw [initialClippedEndpointWindow, mul_sum]
  apply sum_le_sum
  intro bin hb
  let d := dyadicSlack (Nat.log2 M + 1) j
  by_cases hz : LogSpaceEstimation.lastBudget M d B.slack
      (B.sampleScale r (some bin)) = 0
  · simp only [show dyadicSlack (Nat.log2 M + 1) j = d from rfl, hz,
      initialEndpointCharge, ↓reduceIte, mul_zero, Real.zero_rpow (by norm_num :
        (4⁻¹ : ℝ) ≠ 0)]
    exact le_rfl
  rw [ite_eq_right hz]
  have hh := B.initialClippedRootEndpoint_le hcharge hrate H M d ks ka bin ha (hi bin hb)
    r hs ht htask coefficient
  have hp : _ ≤ (K * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 -
      3 * |(bin : ℝ) - ka| / 4)) ^ 4 := hh.trans_eq (by rw [mul_pow K, hKpow]; ring)
  have hr := Real.rpow_le_rpow
    (mul_nonneg (B.initialClippedRootCoefficient_nonneg ka bin)
      (B.initialEndpointCharge_nonneg _ _ _)) hp (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have he : ((K * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 -
      3 * |(bin : ℝ) - ka| / 4)) ^ 4) ^ (4⁻¹ : ℝ) =
      K * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 -
        3 * |(bin : ℝ) - ka| / 4) :=
    Real.pow_rpow_inv_natCast (by positivity) (by decide : (4 : ℕ) ≠ 0)
  rwa [he] at hr

/-- Finite weighted fourth-moment allocation for the surviving endpoints. The weights
are literal compression coefficients, and may vary with the prefix. This does not
replace them by a uniform unweighted bound or discount a correlated heavy event. -/
theorem initialClippedEndpointPrefixCharge_weighted_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) (coefficient : ℝ) :
    (∑ j ∈ s, w j * B.initialClippedEndpointPrefixCharge M j r ka coefficient) ≤
      ((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
        |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) ^ 4 *
          ∑ j ∈ s, w j * B.initialClippedEndpointWindow M j ka r ^ 4 := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  exact (mul_le_mul_of_nonneg_left
    (B.initialClippedEndpointPrefixCharge_le hcharge hrate H M j ks ka ha hi r hs ht
      htask coefficient) (hw j hj)).trans_eq (by rw [mul_pow]; ring)

/-- Rooted finite weighted allocation for stationary preloss and deterministic mean
tails. The latter may use the existing outer mean-rarity factor; this theorem does
not introduce such a factor for environment-dependent noise. -/
theorem initialClippedEndpointPrefixCharge_sum_root_le
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) (coefficient : ℝ) :
    (∑ j ∈ s, w j *
      B.initialClippedEndpointPrefixCharge M j r ka coefficient ^ (4⁻¹ : ℝ)) ≤
      ((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
        |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) *
          ∑ j ∈ s, w j * B.initialClippedEndpointWindow M j ka r := by
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have h := Real.rpow_le_rpow (B.initialClippedEndpointPrefixCharge_nonneg M j r ka _)
    (B.initialClippedEndpointPrefixCharge_le hcharge hrate H M j ks ka ha hi r hs ht
      htask coefficient) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hn : 0 ≤ B.initialClippedEndpointWindow M j ka r := by
    unfold initialClippedEndpointWindow
    exact sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hc := B.binCap_nonneg
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  have he : ((K * B.initialClippedEndpointWindow M j ka r) ^ 4) ^ (4⁻¹ : ℝ) =
      K * B.initialClippedEndpointWindow M j ka r :=
    Real.pow_rpow_inv_natCast (by dsimp only [K]; positivity) (by decide : (4 : ℕ) ≠ 0)
  rw [he] at h
  exact (mul_le_mul_of_nonneg_left h (hw j hj)).trans_eq (by ring)

omit [Fact P.Prime] in
/-- A live bin gives a necessary growth condition for any weighted window allocation.
In particular a tail weight at least one supplies no decay for its surviving endpoint.
This is a condition on the numerical envelope, not a lower bound on estimator error. -/
theorem initialClippedEndpointWindow_growth
    (M j ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hbin : bin ∈ B.bins)
    (hlive : LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some bin)) ≠ 0)
    (w A : ℝ) (hw : 1 ≤ w)
    (hpaid : w * B.initialClippedEndpointWindow M j ka r ≤ (2 : ℝ) ^ A) :
    (dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack) +
      1 / 16 - 3 * |(bin : ℝ) - ka| / 4 ≤ A := by
  have hterm : (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack) +
      1 / 16 - 3 * |(bin : ℝ) - ka| / 4) ≤ B.initialClippedEndpointWindow M j ka r := by
    unfold initialClippedEndpointWindow
    have h := single_le_sum (f := fun b =>
      if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some b)) = 0 then (0 : ℝ) else
        (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack) +
          1 / 16 - 3 * |(b : ℝ) - ka| / 4))
      (fun b _ => by split_ifs <;> positivity) hbin
    simpa only [hlive, ↓reduceIte] using h
  have hn : 0 ≤ B.initialClippedEndpointWindow M j ka r :=
    (Real.rpow_pos_of_pos (by norm_num) _).le.trans hterm
  have h := hterm.trans ((le_mul_of_one_le_left hn hw).trans hpaid)
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h

omit [Fact P.Prime] in
/-- Necessary growth condition for the literal unconditional compression tail. Its
coefficient is `28 ^ (m - i)`, with no heavy-rarity discount. A single live endpoint
already constrains any allocation of the entire rooted tail window. -/
theorem initialClippedEndpointWindow_tail_growth
    (M j i ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hi : i ∈ Ico j (Nat.log2 M + 1)) (hbin : bin ∈ B.bins)
    (hlive : LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
      B.slack (B.sampleScale r (some bin)) ≠ 0)
    (A : ℝ)
    (hpaid : (∑ l ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - l) *
      B.initialClippedEndpointWindow M l ka r) ≤ (2 : ℝ) ^ A) :
    (dyadicSlack (Nat.log2 M + 1) i : ℝ) / (16 * B.slack) +
      1 / 16 - 3 * |(bin : ℝ) - ka| / 4 ≤ A := by
  apply B.initialClippedEndpointWindow_growth M i ka bin r hbin hlive
    ((28 : ℝ) ^ (Nat.log2 M + 1 - i)) A (one_le_pow₀ (by norm_num))
  apply le_trans _ hpaid
  apply single_le_sum _ hi
  intro l _
  apply mul_nonneg (by positivity)
  unfold initialClippedEndpointWindow
  exact sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- A structural allocation for the surviving endpoints, fixed before child errors.
The condition has no sum over prefix groups, source exponent or field width. -/
theorem initialClippedEndpointPrefixCharge_paid
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hwindow : (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * B.initialClippedEndpointWindow M j ka r ≤ (2 : ℝ) ^ B.rankCharge)
    (coefficient : ℝ) :
    B.initialClippedEndpointPrefixCharge M j r ka coefficient ≤
      coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  apply (B.initialClippedEndpointPrefixCharge_le hcharge hrate H M j ks ka ha hi
    r hs ht htask coefficient).trans
  have hh := mul_le_mul_of_nonneg_right hwindow
    (show 0 ≤ |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge) by positivity)
  have hc : (2 : ℝ) ^ B.rankCharge * (2 : ℝ) ^ (-B.rankCharge) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
  have hb : (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
      B.initialClippedEndpointWindow M j ka r ≤
      |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) := by
    calc
      _ ≤ (|coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r)) *
          ((2 : ℝ) ^ B.rankCharge * (2 : ℝ) ^ (-B.rankCharge)) := by nlinarith only [hh]
      _ = _ := by rw [hc, mul_one]
  have hw : 0 ≤ B.initialClippedEndpointWindow M j ka r := by
    unfold initialClippedEndpointWindow
    exact sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hcap := B.binCap_nonneg
  exact (pow_le_pow_left₀ (by positivity) hb 4).trans_eq (by
      rw [mul_pow, (by decide : Even 4).pow_abs coefficient])

omit [Fact P.Prime] in
/-- For bounded surviving slack the sharp offset window has a width-, horizon- and
bin-count-independent bound. The structural constant uses the existing summable two-sided
scale majorant; no constant is chosen after the request coordinates or parent budget. -/
theorem initialClippedEndpointWindow_uniform
    (M j ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hd : dyadicSlack (Nat.log2 M + 1) j ≤ 16 * B.slack) :
    B.initialClippedEndpointWindow M j ka r ≤
      4 * ∑' h, LogSpaceEstimation.scaleMajorant h := by
  have hslack : (0 : ℝ) < 16 * B.slack := by have h := B.slack_pos; positivity
  have hd' : (dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack) ≤ 1 := by
    apply (div_le_one hslack).mpr
    exact_mod_cast hd
  have hinj : Set.InjOn (fun bin : ℕ => (bin : ℤ) - ka) B.bins := by
    intro a _ b _ hab
    have hh : (a : ℤ) = b := by linarith only [hab]
    exact_mod_cast hh
  have hsum : (∑ bin ∈ B.bins, LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka)) ≤
      ∑' h, LogSpaceEstimation.scaleMajorant h := by
    rw [← sum_image hinj]
    exact LogSpaceEstimation.summable_scaleMajorant.sum_le_tsum _
      (fun h _ => LogSpaceEstimation.scaleMajorant_nonneg h)
  unfold initialClippedEndpointWindow
  calc
    _ ≤ ∑ bin ∈ B.bins, 4 * LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) := by
      apply sum_le_sum
      intro bin _
      split_ifs
      · exact mul_nonneg (by norm_num) (LogSpaceEstimation.scaleMajorant_nonneg _)
      · have habs : (((bin : ℤ) - ka).natAbs : ℝ) = |(bin : ℝ) - ka| := by simp
        unfold LogSpaceEstimation.scaleMajorant
        rw [habs]
        have he : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
        rw [he, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith [abs_nonneg ((bin : ℝ) - ka)]
    _ = 4 * ∑ bin ∈ B.bins, LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

omit [Fact P.Prime] in
/-- Every endpoint window, including large surviving slack, has a slope-one envelope.
Inside a literal tail the earlier slack dominates every later slack, so deterministic
rarity can pay this growth. This statement does not discount centered sampling noise. -/
theorem initialClippedEndpointWindow_growing
    (M j ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.initialClippedEndpointWindow M j ka r ≤
      (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) *
        (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
  let d := dyadicSlack (Nat.log2 M + 1) j
  have hs : (1 : ℝ) ≤ 16 * B.slack := by
    have h := B.slack_pos
    have hh : (1 : ℝ) ≤ B.slack := by exact_mod_cast h
    linarith
  have hd : (d : ℝ) / (16 * B.slack) ≤ d :=
    div_le_self (Nat.cast_nonneg d) hs
  have hinj : Set.InjOn (fun bin : ℕ => (bin : ℤ) - ka) B.bins := by
    intro a _ b _ hab
    have hh : (a : ℤ) = b := by linarith only [hab]
    exact_mod_cast hh
  have hsum : (∑ bin ∈ B.bins, LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka)) ≤
      ∑' h, LogSpaceEstimation.scaleMajorant h := by
    rw [← sum_image hinj]
    exact LogSpaceEstimation.summable_scaleMajorant.sum_le_tsum _
      (fun h _ => LogSpaceEstimation.scaleMajorant_nonneg h)
  unfold initialClippedEndpointWindow
  calc
    _ ≤ ∑ bin ∈ B.bins, (4 * (2 : ℝ) ^ d) *
        LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) := by
      apply sum_le_sum
      intro bin _
      split_ifs
      · exact mul_nonneg (by positivity) (LogSpaceEstimation.scaleMajorant_nonneg _)
      · have habs : (((bin : ℤ) - ka).natAbs : ℝ) = |(bin : ℝ) - ka| := by simp
        unfold LogSpaceEstimation.scaleMajorant
        rw [habs, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
        dsimp only [d] at hd
        linarith [abs_nonneg ((bin : ℝ) - ka)]
    _ = (4 * (2 : ℝ) ^ d) * ∑ bin ∈ B.bins,
        LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) := (mul_sum _ _ _).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 4 * (2 : ℝ) ^ d)
      dsimp only [d] at h
      nlinarith only [h]

/-- A single structural allocation pays every bounded-slack endpoint window, with no
restriction on parent budget, source/terminal exponents, bin count or field width. Earlier
large-slack prefixes, ordinary progress and preparation still require their own payments. -/
theorem initialClippedEndpointPrefixCharge_uniform_paid
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (halloc : 4 * (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * (∑' h, LogSpaceEstimation.scaleMajorant h) ≤ (2 : ℝ) ^ B.rankCharge)
    (M j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hd : dyadicSlack (Nat.log2 M + 1) j ≤ 16 * B.slack) (coefficient : ℝ) :
    B.initialClippedEndpointPrefixCharge M j r ka coefficient ≤
      coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  apply B.initialClippedEndpointPrefixCharge_paid hcharge hrate H M j ks ka ha hi
    r hs ht htask _ coefficient
  have hcap := B.binCap_nonneg
  have hh := mul_le_mul_of_nonneg_left (B.initialClippedEndpointWindow_uniform M j ka r hd)
    (show 0 ≤ (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) by positivity)
  exact hh.trans (by nlinarith only [halloc])

/-- Signed conditional means telescope before clipping or taking roots. Only one actual
fine child per bin survives; the initial boundary is zero by the schedule. The hypotheses
are successful compressed calls and scalar own-request accuracy, not endpoint coherence.
All masks remain joint, and centered sampled noise is deliberately untouched. -/
theorem initial_compressed_prefix_clipped_endpoint
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hu : r.usage = r.terminal)
    (hks : ks ≤ H.maxExponent) (hbin : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (hprep : ∀ bin ∈ B.bins, ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
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
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    ∃ groups reference,
      (List.range (Nat.log2 M + 1)).mapM (fun j => B.completedGroup
        (fun n q => if n < M then B.compressedHistory exponent ζ floor n q else none) M
        (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      (List.range (Nat.log2 M + 1)).mapM (fun j => B.completedGroup
        (fun n q => if n < M then B.evaluate n q else none) M
        (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩) r) = some reference ∧
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate Xs Ya
          (fun _ x y => min 1 (|rowSliceMean Xs Ya
            (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum -
              ((reference.take (j + 1)).map (fun T => T σ x y)).sum) x y| /
                (rate ka + B.base x y))) ≤
          B.initialClippedEndpointPrefixCharge M j r ka coefficient := by
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let Q := fun bin => HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let E : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ := fun bin n σ x y =>
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
    r.terminal (Q bin).direct y * D bin n σ x y
  let C := fun bin n => if n = 0 then 0 else B.initialSample r bin
  obtain ⟨groups, hg, hm⟩ := B.initial_compressed_prefix_mean exponent ζ floor M hM hbins
    r s t hst ks ka ss st hs (hu.trans ht) D hzero
    (fun bin hb n hn hp => ⟨(ih bin hb n hn hp).1, (ih bin hb n hn hp).2.2⟩)
  obtain ⟨reference, hc, hcm⟩ := B.initial_sample_prefix_mean
    (fun n q => if n < M then B.evaluate n q else none) M hM hbins
    r s t hst ks ka ss st hs (hu.trans ht) C
    (fun bin _ n hn => B.sample_initial_eq M hM n hn bin r)
  refine ⟨groups, reference, hg, hc, ?_⟩
  intro j hj
  let fine := fun bin => LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
    B.slack (B.sampleScale r (some bin))
  have he (x y : ZMod P) : rowSliceMean Xs Ya
      (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum -
        ((reference.take (j + 1)).map (fun T => T σ x y)).sum) x y =
      ∑ bin ∈ B.bins, rowSliceMean Xs Ya (E bin (fine bin) - C bin (fine bin)) x y := by
    simp only [rowSliceMean, expect_sub_distrib]
    change rowSliceMean Xs Ya
      (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) x y -
      rowSliceMean Xs Ya
      (fun σ x y => ((reference.take (j + 1)).map (fun T => T σ x y)).sum) x y = _
    rw [hm j hj x y, hcm j hj x y, ← sum_sub_distrib]
    apply sum_congr rfl
    intro bin _
    simp only [B.initial_start_budget, E, C, hzero, ↓reduceIte,
      Pi.zero_apply, Matrix.zero_apply, mul_zero, sub_zero, rowSliceMean,
      Pi.sub_apply, Matrix.sub_apply, expect_sub_distrib]
    rfl
  change rowNormPow 4 P r.source.rate Xs Ya
    (fun _ x y => min 1 (|rowSliceMean Xs Ya
      (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum -
        ((reference.take (j + 1)).map (fun T => T σ x y)).sum) x y| /
          (rate ka + B.base x y))) ≤ _
  simp_rw [he]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  apply rowNormPow_clipped_sum_le_pow_sum B.bins hNu Xs Ya
    (fun bin => rowSliceMean Xs Ya (E bin (fine bin) - C bin (fine bin)))
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))
    (fun bin => B.initialClippedRootCoefficient ka bin *
      B.initialEndpointCharge (fine bin) (Q bin).direct coefficient)
  intro bin hb
  have hn : fine bin < M := LogSpaceEstimation.lastBudget_lt hM B.slack_pos
  by_cases hz : fine bin = 0
  · simp [hz, E, C, hzero, rowSliceMean, rowNormPow, initialEndpointCharge]
  · obtain ⟨hd, herr, R, hr⟩ := ih bin hb (fine bin) hn (Nat.pos_of_ne_zero hz)
    obtain ⟨A, hA, hbound⟩ := B.positiveSample_initial_compressed_clipped_root hrate hcutoff
      hD H exponent ζ floor M (fine bin) bin hn r s t hst ks ka ss st hs ht hks
      (hbin bin hb) (hprep bin hb) hC hC1 hK (D bin (fine bin)) R hd hr
    have ha : A = E bin (fine bin) := Option.some.inj (hA.symm.trans
      (B.positiveSample_initial_compressed exponent ζ floor M (fine bin) bin hn r
        (D bin (fine bin)) R hd hr).1)
    rw [ha] at hbound
    dsimp only [C]
    rw [ite_eq_right hz]
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (by simpa only [initialEndpointCharge, ite_eq_right hz] using herr)
      (B.initialClippedRootCoefficient_nonneg ka bin))

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

/-- Spectral completion of the actual compressed-minus-semantic input, centered on
its original joint slice. Unlike uncentered contraction this keeps the scheduled gap
factor. Input moments may come from strict own-request child accuracy; no rarity or
independence assumption is introduced. -/
theorem completedGroup_initial_compressed_centered_error
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
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => (F - G) σ x y - rowSliceMean Xs Yu (F - G) x y) ≤
        32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) *
          ((#B.bins : ℝ) ^ 3 * ∑ i ∈ B.bins, ε i) := by
  dsimp only
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
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)
  have hgap (x y : ZMod P) : (graphV x y).spectralExpansion ≤ ρ := by
    dsimp only [graphV]
    unfold graph
    rw [RotationMap.spectralExpansion_reindex, RotationMap.spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le (by decide)
  have hcontract := rowNormPow_conditionalWalk_le_raw Xs Yu hNu graphV hgap
    (B.steps M r d) (sumA - sumC)
  have hmean : rowSliceMean Xs Yu (walk sumA - walk sumC) =
      rowSliceMean Xs Yu (sumA - sumC) := by
    funext x y
    rw [← conditionalWalk_sub, rowSliceMean_conditionalWalk]
  have hx : (fun σ x => r.source.retains (channels B.padding) σ x) = Xs := by
    funext σ x
    simp only [hs, Xs, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, X]
  have hy : (fun σ y => r.usage.retains (channels B.padding) σ y) = Yu := by
    funext σ y
    simp only [hu, Yu, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, Y]
  rw [conditionalWalk_sub] at hcontract
  simp only [hx, hy]
  change rowNormPow 4 P r.source.rate Xs Yu
    (fun σ x y => (walk sumA - walk sumC) σ x y -
      rowSliceMean Xs Yu (walk sumA - walk sumC) x y) ≤ _
  rw [hmean]
  apply hcontract.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he : sumA - sumC = fun σ x y => ∑ i ∈ B.bins, (A i - C i) σ x y := by
    funext σ x y
    simp only [sumA, sumC, Pi.sub_apply, Matrix.sub_apply, sum_sub_distrib]
  rw [he]
  apply (rowNormPow_sum_fourth_le B.bins hNu _ _ (fun i => A i - C i)).trans
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum (fun i hi => by simpa only [hx, hy] using herr i hi)) (by positivity)

/-- Centered contraction after a common normalization and finite Minkowski of the
actual paired inputs. Original joint masks and scheduled graph steps remain literal;
there is no bin-cardinality cube or independence hypothesis. -/
theorem completedGroup_initial_compressed_centered_scaled_error
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (scale : ℝ) (ε : ℕ → ℝ) (hε : ∀ i ∈ B.bins, 0 ≤ ε i)
    (hA : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (A i))
    (hC : ∀ i ∈ B.bins,
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some i) = some (C i))
    (herr : ∀ i ∈ B.bins, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => scale * (A i - C i) σ x y) ≤ ε i ^ 4) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => scale * ((F - G) σ x y - rowSliceMean Xs Yu (F - G) x y)) ≤
        32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) *
          (∑ i ∈ B.bins, ε i) ^ 4 := by
  dsimp only
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
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)
  have hgap (x y : ZMod P) : (graphV x y).spectralExpansion ≤ ρ := by
    dsimp only [graphV]
    unfold graph
    rw [RotationMap.spectralExpansion_reindex, RotationMap.spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le (by decide)
  have hcontract := rowNormPow_conditionalWalk_le_raw Xs Yu hNu graphV hgap
    (B.steps M r d) (sumA - sumC)
  have hmean : rowSliceMean Xs Yu (walk sumA - walk sumC) =
      rowSliceMean Xs Yu (sumA - sumC) := by
    funext x y
    rw [← conditionalWalk_sub, rowSliceMean_conditionalWalk]
  have hx : (fun σ x => r.source.retains (channels B.padding) σ x) = Xs := by
    funext σ x
    simp only [hs, Xs, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, X]
  have hy : (fun σ y => r.usage.retains (channels B.padding) σ y) = Yu := by
    funext σ y
    simp only [hu, Yu, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, Y]
  rw [conditionalWalk_sub] at hcontract
  simp only [hx, hy]
  change rowNormPow 4 P r.source.rate Xs Yu
    (fun σ x y => scale * ((walk sumA - walk sumC) σ x y -
      rowSliceMean Xs Yu (walk sumA - walk sumC) x y)) ≤ _
  rw [hmean, rowNormPow_const_mul]
  have hc := mul_le_mul_of_nonneg_left hcontract (pow_nonneg (abs_nonneg scale) 4)
  apply hc.trans
  rw [← mul_assoc, mul_comm (|scale| ^ 4), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← rowNormPow_const_mul]
  have he : (fun σ x y => scale * (sumA - sumC) σ x y) =
      (fun σ x y => ∑ i ∈ B.bins, 1 * (scale * (A i - C i) σ x y)) := by
    funext σ x y
    simp only [sumA, sumC, Pi.sub_apply, Matrix.sub_apply, sum_sub_distrib, one_mul,
      mul_sub, mul_sum]
  rw [he]
  have hb := rowNormPow_sum_le_pow_sum (X := Xs) (by decide : 4 ≠ 0) hNu Yu B.bins
    (fun i σ x y => scale * (A i - C i) σ x y) (fun _ => 1) ε
    (by intros; norm_num) hε (fun i hi => by simpa only [hx, hy] using herr i hi)
  simpa only [one_mul] using hb

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
    simpa only [mul_pow, hKpow, w, ite_eq_right hz, C, mul_assoc] using hh
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
    exact Real.pow_rpow_inv_natCast (by positivity)
      (by decide : (4 : ℕ) ≠ 0)
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

/-- On an actual grid source the unchanged walk schedule pays its raw spectral factor.
The norm-level slack is literally `64⁻ᵈ = 2^(-6*d)`; precision and the original magnitude
allocator are retained. This comparison does not pay an input discrepancy. -/
theorem initial_completion_gap_payment (M d ks : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : r.source.rate = rate ks) :
    32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r) * (64 : ℝ)⁻¹ ^ d) ^ 4 := by
  have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have hsource1 : r.source.rate ≤ 1 := by
    rw [hs]
    simpa only [rate, pow_zero, inv_one, one_pow] using rate_antitone (Nat.zero_le ks)
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).one_lt.le
  have hNu : 0 < (P : ℝ) * r.source.rate := mul_pos (by linarith) hsource
  have hwidth : 1 ≤ (P : ℝ)^2 / (P * r.source.rate) := by
    apply (le_div_iff₀ hNu).mpr
    nlinarith
  have hm := one_le_pow₀ (B.one_le_magnitude r) (n := 4)
  have hC : 32 ≤ 32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4) := by
    nlinarith [mul_le_mul hwidth hm (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have hr : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4) := by norm_num
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ 32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4) by positivity)
    (Real.rpow_pos_of_pos (by norm_num) _) d (B.steps M r d) (Nat.le_max_right _ _)
  exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans hp

/-- Finite active-pair payment after sharp own-precision cancellation. The ordinary
scale is divided out before bin addition. Equal pairs still cost zero; zero endpoint
precision is never demanded. This finite sum does not assert uniform absorption. -/
@[expose] def initialActiveRootGroupCharge (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ) (coefficient : ℝ) : ℝ :=
  (#B.bins : ℝ) ^ 3 * ∑ bin ∈ B.bins,
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    if fine = coarse then 0 else
    16 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
      (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge) * (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) /
          (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|)) ^ 4)

/-- The literal two-endpoint charge is bounded by sharp active cancellation, keeping
all bin constants and the fixed structural charge explicit. -/
theorem initialRootGroupCharge_le_active (hcharge : 0 ≤ B.rankCharge)
    (hrate : B.binRate = rate) (M d ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (coefficient : ℝ) :
    B.initialRootGroupCharge M d r coefficient ≤
      B.initialActiveRootGroupCharge M d r ka coefficient := by
  unfold initialRootGroupCharge initialActiveRootGroupCharge
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro bin _
  dsimp only
  split_ifs with heq
  · exact le_rfl
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let a := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
    (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) / (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|)
  have hend (e : ℕ) (he : e ∈ ({d, 2 * d} : Finset ℕ)) :
      B.initialEndpointCharge
        (LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin)))
        Q.direct coefficient ≤ coefficient ^ 4 * a ^ 4 := by
    unfold initialEndpointCharge
    split_ifs with hz
    · positivity
    have hp := (B.requestPrecision_initial_active_pay hcharge hrate M d ks ka bin e
      r hs ht htask heq he).1
    have hbound : (2 : ℝ) ^ (-B.requestPrecision
        (LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))) Q.direct) ≤ a := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      simpa only [mul_comm] using hp
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) _).le hbound 4) (by positivity)
  have hf := hend d (by simp only [mem_insert, mem_singleton, true_or])
  have hc := hend (2 * d) (by simp only [mem_insert, mem_singleton, or_true])
  have hh := add_le_add hf hc
  have hmul := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 8 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) by positivity)
  dsimp only [Q, a] at hmul
  nlinarith only [hmul]

/-- On a common admissible horizon, rounded importance is uniformly bounded.
This bound is independent of the field width and of all copy suffixes. -/
theorem initial_importance_norm_le (hrate : B.binRate = rate) (H : Horizon P)
    (ka bin : ℕ) (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ht : r.terminal.rate = rate ka) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    ‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
      r.terminal Q.direct y‖ ≤ 16 := by
  dsimp only
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)).mpr
  intro y
  have hratio := usageRatio_grid B.padding r.terminal
    (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)).direct ka (max ka bin) ht
    (by simpa only [HierarchyTask.rawRequests, hrate, ht] using rate_min ka bin) y
  rw [hratio, hrate, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (rate_pos bin).le (by positivity))]
  have h := gridMass_importance_le H ha hi
  have hone (k : ℕ) : rate k ≤ 1 := by
    simpa only [rate, pow_zero, inv_one, one_pow] using rate_antitone (Nat.zero_le k)
  exact h.trans (by nlinarith [max_le (hone bin) (hone ka)])

/-- Rounded importance and terminal normalization are compared together. The only
remaining rate loss is a bin offset, independent of the absolute terminal exponent.
This is a pointwise bound before any sup norm or bin counting. -/
theorem initial_normalized_importance_le (hrate : B.binRate = rate) (H : Horizon P)
    (ka bin : ℕ) (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ht : r.terminal.rate = rate ka) (y : ZMod P) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y /
        rate ka ≤
      16 * (2 : ℝ) ^ (if bin ≤ ka then 4 * ((ka : ℝ) - bin) else 0) := by
  dsimp only
  have hratio := usageRatio_grid B.padding r.terminal
    (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)).direct ka (max ka bin) ht
    (by simpa only [HierarchyTask.rawRequests, hrate, ht] using rate_min ka bin) y
  rw [hratio, hrate]
  change rate bin * (gridMass P ka / gridMass P (max ka bin)) / rate ka ≤ _
  have h := div_le_div_of_nonneg_right (gridMass_importance_le H ha hi) (rate_pos ka).le
  by_cases hf : bin ≤ ka
  · rw [max_eq_left (rate_antitone hf)] at h
    rw [ite_eq_left hf, ← rate_ratio_two_rpow]
    convert h using 1; ring
  · rw [max_eq_right (rate_antitone (Nat.le_of_lt (Nat.lt_of_not_ge hf)))] at h
    rw [ite_eq_right hf, Real.rpow_zero]
    simpa only [mul_div_cancel_right₀ _ (rate_pos ka).ne', mul_one] using h

/-- Joint ordinary transport at a literal direct child. Terminal normalization,
rounded importance and own-request precision cancel before a sup norm is taken.
Only the actual budget loss and twice the offset remain. The source exponent cancels
and the structural charge is fixed before all request coordinates. -/
theorem initial_normalized_importance_precision_le (hcharge : 0 ≤ B.rankCharge)
    (hrate : B.binRate = rate) (H : Horizon P) (M m ks ka bin : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (y : ZMod P) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y /
      rate ka) * (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      16 * ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (((M : ℝ) - m) / (16 * B.slack) + 2 * |(bin : ℝ) - ka|)) := by
  dsimp only
  have hw := B.initial_normalized_importance_le hrate H ka bin ha hi r ht y
  have hp := B.requestPrecision_initial_clipped_transfer hcharge hrate M m ks ka bin
    r hs ht htask
  dsimp only at hw hp
  let t : ℝ := if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)
  have he : (if bin ≤ ka then 4 * ((ka : ℝ) - bin) else 0) =
      t + 3 * |(bin : ℝ) - ka| := by
    dsimp only [t]
    split_ifs with hf
    · have hh : (bin : ℝ) ≤ ka := by exact_mod_cast hf
      rw [abs_of_nonpos (sub_nonpos.mpr hh)]
      ring
    · have hh : (ka : ℝ) ≤ bin := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hf))
      rw [abs_of_nonneg (sub_nonneg.mpr hh)]
      ring
  have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤ (2 : ℝ) ^
    (-B.requestPrecision m (HierarchyTask.rawRequests 0 bin
      (.pilotInput ⟨0, HP.k_pos⟩) r.source (midpoint r) r.terminal
      (B.binRate bin)).direct) by positivity)
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hh
  have hpaid := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 16 * (2 : ℝ) ^ (3 * |(bin : ℝ) - ka|) by positivity)
  apply hh.trans
  convert hpaid using 1
  · dsimp only [t]; ring
  · rw [show ((M : ℝ) - m) / (16 * B.slack) + 2 * |(bin : ℝ) - ka| =
        3 * |(bin : ℝ) - ka| +
          (((M : ℝ) - m) / (16 * B.slack) - |(bin : ℝ) - ka|) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring

/-- An unequal executed pair turns the joint normalized payment into geometric offset
decay. No terminal bound, bin-cardinality bound, independence, support of approximate
children or weighted IH is assumed. This endpoint estimate alone is not a group sum. -/
theorem initial_normalized_active_precision_le (hcharge : 0 ≤ B.rankCharge)
    (hrate : B.binRate = rate) (H : Horizon P) (M d ks ka bin e : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hne : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) ≠
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)))
    (he : e ∈ ({d, 2 * d} : Finset ℕ)) (y : ZMod P) :
    let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y /
      rate ka) * (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      16 * ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|)) := by
  dsimp only
  apply (B.initial_normalized_importance_precision_le hcharge hrate H M _ ks ka bin
    ha hi r hs ht htask y).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨_, hcut, hloss⟩ := B.initial_active_pair_losses M d ka bin r hrate ht hne
  have hl : (M : ℝ) - LogSpaceEstimation.lastBudget M e B.slack
      (B.sampleScale r (some bin)) ≤ 2 * d := by
    have hn := hloss e he
    have hreal : ((M - LogSpaceEstimation.lastBudget M e B.slack
        (B.sampleScale r (some bin)) : ℕ) : ℝ) ≤ 2 * d := by exact_mod_cast hn
    rw [Nat.cast_sub (show LogSpaceEstimation.lastBudget M e B.slack
      (B.sampleScale r (some bin)) ≤ M from Nat.sub_le _ _)] at hreal
    exact hreal
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hd : (0 : ℝ) ≤ d := by positivity
  have hsmall : ((M : ℝ) - LogSpaceEstimation.lastBudget M e B.slack
      (B.sampleScale r (some bin))) / (16 * B.slack) ≤
      2 * (d : ℝ) / B.slack - 3 * |(bin : ℝ) - ka| := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
    have hdiv : (2 * (d : ℝ) / B.slack) * (16 * B.slack) = 32 * d := by
      field_simp
      ring
    rw [sub_mul, hdiv]
    nlinarith [abs_nonneg ((bin : ℝ) - ka)]
  linarith

/-- A literal positive endpoint consumes its direct child's own rooted IH after joint
normalization. The original parent terminal mask and the direct source/usage masks are
kept through conversion. Reset-right execution is separate; no approximate support or
independence is assumed. Absolute source and terminal exponents are unbounded. -/
theorem positiveSample_initial_compressed_normalized_precision
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d ks ka bin e : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hne : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) ≠
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)))
    (he : e ∈ ({d, 2 * d} : Finset ℕ))
    (hm : LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin)) < M)
    (D R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (coefficient : ℝ)
    (hd :
      let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some D)
    (hr :
      let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (herr :
      let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4) :
    ∃ A, B.positiveSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) (LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin)))
        bin (.pilotInput ⟨0, HP.k_pos⟩) r = some A ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => (A σ x y - B.initialSample r bin σ x y) / rate ka) ≤
        ((4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
          (16 * ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
            (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|)))) ^ 4 := by
  let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let C := denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
    HP.ρ HP.K B.base
  let w := fun y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y / rate ka
  let A := fun σ x y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y * D σ x y
  refine ⟨A, (B.positiveSample_initial_compressed exponent ζ floor M m bin hm r D R hd hr).1,
    ?_⟩
  have heq : (fun σ x y => (A σ x y - B.initialSample r bin σ x y) / rate ka) =
      (fun σ x y => w y * (D σ x y - C σ x y)) := by
    funext σ x y
    dsimp only [A, w, C, initialSample]
    ring
  rw [heq]
  have hru := B.compressedBin_range_usage m bin (exponent Q.direct) ζ floor Q.direct D hd
  apply rowNormPow_weighted_sub_precision_le
    (by change 0 ≤ (P : ℝ) * r.source.rate
        rw [hs]
        exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le)
    (Real.rpow_pos_of_pos (by norm_num) _) (by positivity)
    _ _ (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) D C w hru.1
    (fun σ x y => normalizedRequest_mem_Icc HP B.padding Q.direct (B.cutoff bin)
      B.binCap_nonneg (B.cutoff_bounds bin) _ _ σ x y)
    (fun σ x y hy => by
      rw [hru.2 σ x y hy]
      exact (normalizedRequest_zero_off_usage B.padding id Q.direct _ _ _ _ _ σ x y hy).symm)
    _ herr
  intro y
  have hw : 0 ≤ w y := by
    dsimp only [w, HierarchyTask.usageRatio]
    rw [hrate]
    exact div_nonneg (mul_nonneg (rate_pos bin).le (by positivity)) (rate_pos ka).le
  rw [abs_of_nonneg hw]
  exact B.initial_normalized_active_precision_le hcharge hrate H M d ks ka bin e ha hi
    r hs ht htask hne he y

/-- Actual unequal paired endpoints retain joint normalized precision before bin addition.
Equal pairs execute no child and cost zero, and exhausted endpoints have zero charge.
The IH is required only for actual positive endpoints with separate reset availability. -/
theorem pairedSample_initial_compressed_normalized_precision_at
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : 0 ≤ r.source.rate)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (ks ka : ℕ) (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent)
    (hsource : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (D : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (hzero : D 0 = 0)
    (coefficient : ℝ)
    (ih :
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
      fine ≠ coarse → ∀ n ∈ ({fine, coarse} : Finset ℕ), n < M → 0 < n →
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
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    ∃ A C,
      B.pairedSample (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.pairedSample (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some C ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => (A - C) σ x y / rate ka) ≤
        if fine = coarse then 0 else
        (32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
          ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
            (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|))) ^ 4 := by
  obtain ⟨A, C, hA, hC, hb⟩ := B.pairedSample_initial_compressed_precision_at
    exponent ζ floor M d bin hM r hs D hzero coefficient ih
  refine ⟨A, C, hA, hC, ?_⟩
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let w := fun y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
    (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|)
  let K := (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4))
  have hscale : rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
      (fun σ x y => (A - C) σ x y / rate ka) =
      (rate ka)⁻¹ ^ 4 * rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y) (A - C) := by
    simp only [div_eq_mul_inv, mul_comm _ (rate ka)⁻¹]
    rw [rowNormPow_const_mul, abs_of_pos (inv_pos.mpr (rate_pos ka))]
  rw [hscale]
  by_cases heq : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  · rw [ite_eq_left heq] at hb ⊢
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (mul_zero _)
  rw [ite_eq_right heq] at hb ⊢
  have hratea := rate_pos ka
  have hend (e : ℕ) (he : e ∈ ({d, 2 * d} : Finset ℕ)) :
      ((rate ka)⁻¹ * ‖w‖) ^ 4 *
        B.initialEndpointCharge
          (LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin)))
          Q.direct coefficient ≤ (|coefficient| * (16 * t)) ^ 4 := by
    unfold initialEndpointCharge
    split_ifs with hz
    · simp only [mul_zero]; positivity
    let ε := (2 : ℝ) ^ (-B.requestPrecision
      (LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))) Q.direct)
    have hε : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
    have ht0 : 0 < t := by dsimp only [t]; positivity
    have hn : ‖w‖ ≤ rate ka * (16 * t) / ε :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun y => by
        have hh := B.initial_normalized_active_precision_le hcharge hrate H M d ks ka
          bin e ha hi r hsource ht htask heq he y
        change (w y / rate ka) * ε ≤ 16 * t at hh
        have hw : 0 ≤ w y := by
          dsimp only [w, HierarchyTask.usageRatio]
          rw [hrate]
          exact mul_nonneg (rate_pos bin).le (by positivity)
        rw [Real.norm_eq_abs, abs_of_nonneg hw]
        apply (le_div_iff₀ hε).mpr
        have hh' : w y * ε / rate ka ≤ 16 * t := by convert hh using 1; ring
        exact (div_le_iff₀ (rate_pos ka)).mp hh' |>.trans_eq (mul_comm _ _))
    have hn' : (rate ka)⁻¹ * ‖w‖ * ε ≤ 16 * t := by
      have hh := (le_div_iff₀ hε).mp hn
      have hh' := mul_le_mul_of_nonneg_left hh (inv_pos.mpr (rate_pos ka)).le
      simpa only [← mul_assoc, inv_mul_cancel_left₀ (rate_pos ka).ne'] using hh'
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (rate ka)⁻¹ * ‖w‖ * ε) hn' 4
    have hc := mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg coefficient) 4)
    dsimp only [ε] at hc
    rw [mul_pow, mul_pow, (by decide : Even (4 : ℕ)).pow_abs] at hc
    simpa only [mul_pow, (by decide : Even (4 : ℕ)).pow_abs, mul_assoc, mul_comm,
      mul_left_comm] using hc
  have hf := hend d (by simp)
  have hc := hend (2 * d) (by simp)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hf hc)
    (show 0 ≤ 8 * K ^ 4 by positivity)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (rate ka)⁻¹ ^ 4 by positivity)
  change _ ≤ (32 * K * |coefficient| * t) ^ 4
  dsimp only [w, Q, K, t] at hh hb' ⊢
  rw [mul_pow, mul_pow] at hh
  nlinarith only [hb', hh]

/-- Actual completed initial groups consume only their unequal positive direct endpoints
at own precision. Normalization precedes both the mask conversion and finite Minkowski;
the spectral factor is the actual unchanged completion schedule. -/
theorem completedGroup_initial_compressed_normalized_precision
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku ka : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (ha : ka ≤ H.maxExponent) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins,
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
      fine ≠ coarse → ∀ n ∈ ({fine, coarse} : Finset ℕ), n < M → 0 < n →
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
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => ((F - G) σ x y - rowSliceMean Xs Yu (F - G) x y) / rate ka) ≤
        32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) *
          (∑ bin ∈ B.bins,
            32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
              ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
                (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|))) ^ 4 := by
  dsimp only
  have hsource : r.source.rate = rate ks := by rw [hs]; rfl
  have hsr : 0 ≤ r.source.rate := by rw [hsource]; exact (rate_pos ks).le
  let ε := fun (bin : ℕ) =>
    32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
      ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|))
  have hε (bin : ℕ) : 0 ≤ ε bin := by
    have hcap := B.binCap_nonneg
    dsimp only [ε]
    positivity
  have hp (i : {i // i ∈ B.bins}) :=
    B.pairedSample_initial_compressed_normalized_precision_at exponent ζ floor M d i.val
      hM r hsr hcharge hrate H ks ka ha (hi i.val i.property) hsource ht htask
      (D i.val) (hzero i.val) coefficient (ih i.val i.property)
  choose A C hA hC he using hp
  let a := fun i => if hi : i ∈ B.bins then A ⟨i, hi⟩ else 0
  let c := fun i => if hi : i ∈ B.bins then C ⟨i, hi⟩ else 0
  have herr (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
      (fun σ x y => (rate ka)⁻¹ * (a i - c i) σ x y) ≤ ε i ^ 4 := by
    have hb := he ⟨i, hi⟩
    dsimp only at hb
    split_ifs at hb
    · have hz : (0 : ℝ) ≤ ε i ^ 4 := by positivity
      have hb' : rowNormPow 4 P r.source.rate
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.usage.retains (channels B.padding) σ y)
          (fun σ x y => (rate ka)⁻¹ * (a i - c i) σ x y) ≤ 0 := by
        simpa only [a, c, dite_eq_left hi, div_eq_mul_inv, mul_comm _ (rate ka)⁻¹] using hb
      exact hb'.trans hz
    · simpa only [a, c, dite_eq_left hi, div_eq_mul_inv, mul_comm _ (rate ka)⁻¹, ε] using hb
  obtain ⟨F, G, hF, hG, hb⟩ := B.completedGroup_initial_compressed_centered_scaled_error
    exponent ζ floor M d hbins r s t hst ks ku ss su hs hu a c (rate ka)⁻¹ ε
    (fun i _ => hε i)
    (fun i hi => by simpa only [a, dite_eq_left hi] using hA ⟨i, hi⟩)
    (fun i hi => by simpa only [c, dite_eq_left hi] using hC ⟨i, hi⟩) herr
  refine ⟨F, G, hF, hG, ?_⟩
  simpa only [div_eq_mul_inv, mul_comm _ (rate ka)⁻¹, ε] using hb

omit [Fact P.Prime] in
/-- Finite normalized bin roots retain the actual offset before summation. The
constant is independent of the bin horizon, source, terminal and field. -/
theorem initial_normalized_bin_sum_le (M d ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (coefficient : ℝ) :
    (∑ bin ∈ B.bins,
      32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
        ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|))) ≤
      (32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
        ∑' h, LogSpaceEstimation.scaleMajorant h) *
          ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
            (4 : ℝ) ^ d) := by
  have hcap := B.binCap_nonneg
  have hc : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hd : 2 * (d : ℝ) / B.slack ≤ 2 * d := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < B.slack)).mpr
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hinj : Set.InjOn (fun bin : ℕ => (bin : ℤ) - ka) B.bins := by
    intro a _ b _ hab
    have hh : (a : ℤ) = b := by linarith only [hab]
    exact_mod_cast hh
  have hsum : (∑ bin ∈ B.bins, LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka)) ≤
      ∑' h, LogSpaceEstimation.scaleMajorant h := by
    rw [← sum_image hinj]
    exact LogSpaceEstimation.summable_scaleMajorant.sum_le_tsum _
      (fun h _ => LogSpaceEstimation.scaleMajorant_nonneg h)
  have hterm (bin : ℕ) :
      (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|) ≤
        (4 : ℝ) ^ d * LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) := by
    have habs : (((bin : ℤ) - ka).natAbs : ℝ) = |(bin : ℝ) - ka| := by simp
    rw [LogSpaceEstimation.scaleMajorant, habs,
      show (4 : ℝ) ^ d = (2 : ℝ) ^ (2 * (d : ℝ)) by
        rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith [abs_nonneg ((bin : ℝ) - ka)]
  let K := 32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
    ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  calc
    _ ≤ ∑ bin ∈ B.bins, K * ((4 : ℝ) ^ d *
        LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka)) := by
      apply sum_le_sum
      intro bin _
      simpa only [K, mul_assoc] using mul_le_mul_of_nonneg_left (hterm bin) hK
    _ = K * (4 : ℝ) ^ d *
        ∑ bin ∈ B.bins, LogSpaceEstimation.scaleMajorant ((bin : ℤ) - ka) := by
      simp only [← mul_sum, mul_assoc]
    _ ≤ K * (4 : ℝ) ^ d * ∑' h, LogSpaceEstimation.scaleMajorant h :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [K]; ring

/-- The actual schedule pays the normalized completed group uniformly over unbounded
source, terminal and bin horizons. Geometric offsets are summed before the fourth power;
only a fixed primitive-range/child-coefficient constant remains. -/
theorem completedGroup_initial_compressed_normalized_paid
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku ka : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (ha : ka ≤ H.maxExponent) (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hp : 0 ≤ B.requestPrecision M r)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins,
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
      fine ≠ coarse → ∀ n ∈ ({fine, coarse} : Finset ℕ), n < M → 0 < n →
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
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => ((F - G) σ x y - rowSliceMean Xs Yu (F - G) x y) / rate ka) ≤
        ((32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
          ∑' h, LogSpaceEstimation.scaleMajorant h) *
            ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
              (1 / 16 : ℝ) ^ d)) ^ 4 := by
  obtain ⟨F, G, hF, hG, hb⟩ := B.completedGroup_initial_compressed_normalized_precision
    hcharge hrate H exponent ζ floor M d hM hbins r s t hst ks ku ka ss su hs hu
    ht htask ha hi D hzero coefficient ih
  refine ⟨F, G, hF, hG, ?_⟩
  let K := 32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
    ∑' h, LogSpaceEstimation.scaleMajorant h
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  have hcap := B.binCap_nonneg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have he1 : e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hsum := B.initial_normalized_bin_sum_le M d ka r coefficient
  have hsum0 : 0 ≤ ∑ bin ∈ B.bins,
      32 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) * |coefficient| *
        ((2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ (2 * (d : ℝ) / B.slack - |(bin : ℝ) - ka|)) := by positivity
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 4)
    (show 0 ≤ 32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^
      (2 * B.steps M r d) by positivity)
  have hgap := B.initial_completion_gap_payment M d ks r (by rw [hs]; rfl)
  have hg := mul_le_mul_of_nonneg_right hgap
    (show 0 ≤ (K * (e * a * (4 : ℝ)^d)) ^ 4 by positivity)
  have hprod : (64 : ℝ)⁻¹ ^ d * (4 : ℝ) ^ d = (1 / 16 : ℝ) ^ d := by
    rw [← mul_pow]
    norm_num
  have hpay : (e * (64 : ℝ)⁻¹ ^ d) ^ 4 * (K * (e * a * (4 : ℝ)^d)) ^ 4 ≤
      (K * (e * a * (1 / 16 : ℝ)^d)) ^ 4 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have heq : (e * (64 : ℝ)⁻¹ ^ d) * (K * (e * a * (4 : ℝ)^d)) =
        (K * (e * a * (1 / 16 : ℝ)^d)) * e := by rw [← hprod]; ring
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) he1
  exact hb.trans (hh.trans (hg.trans hpay))

/-- A bounded full bin family has a uniform active envelope chosen before coordinates.
The horizon is used only for rounded importance; the cardinal bound is explicit.
The exponent five is below the unchanged spectral schedule's six binary units. -/
theorem initialActiveRootGroupCharge_bounded (hrate : B.binRate = rate) (H : Horizon P)
    (M d ka L : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent) (hc : #B.bins ≤ L + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ht : r.terminal.rate = rate ka) (coefficient : ℝ) :
    B.initialActiveRootGroupCharge M d r ka coefficient ≤
      (16 * ((L + 1 : ℕ) : ℝ) ^ 4 *
        ((16 : ℝ) ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4)) *
      (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge) * (32 : ℝ) ^ d) ^ 4) := by
  let a : ℝ := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) * (32 : ℝ) ^ d
  let K : ℝ := 16 * ((16 : ℝ) ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
    (coefficient ^ 4 * a ^ 4)
  have he : (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) ≤ (32 : ℝ) ^ d := by
    have hs : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
    have hx : 25 * (d : ℝ) / (8 * B.slack) ≤ 5 * d := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * B.slack)).mpr
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sub_nonneg.mpr hs)]
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hx).trans_eq
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, ← pow_mul,
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hterm (bin : ℕ) (hb : bin ∈ B.bins) :
      (let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (midpoint r) r.terminal (B.binRate bin)
       let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
       let coarse := LogSpaceEstimation.lastBudget M (2*d) B.slack (B.sampleScale r (some bin))
       if fine = coarse then 0 else
       16 * (‖fun y => B.binRate bin * HierarchyTask.usageRatio (channels B.padding)
         r.terminal Q.direct y‖ ^ 4 * (4 * (2 * B.binCap) ^ ((3 : ℝ) / 4)) ^ 4) *
         (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
           (2 : ℝ) ^ (-B.rankCharge) * (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) /
             (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|)) ^ 4)) ≤ K := by
    dsimp only
    split_ifs
    · dsimp only [K]; positivity
    have hn := B.initial_importance_norm_le hrate H ka bin ha (hi bin hb) r ht
    have hd : (1 : ℝ) ≤ 2 ^ (4 * |(bin : ℝ) - ka|) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hx : (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) /
          (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|) ≤ a := by
      apply (div_le_self (by positivity) hd).trans
      exact mul_le_mul_of_nonneg_left he (by positivity)
    dsimp only [K]
    gcongr
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (#B.bins : ℝ) ^ 3)
  have hc' : (#B.bins : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  have hpow := pow_le_pow_left₀ (by positivity) hc' 4
  unfold initialActiveRootGroupCharge
  apply hmul.trans
  have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ K by dsimp only [K]; positivity)
  dsimp only [K, a] at hh ⊢
  nlinarith only [hh]

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

/-- The literal completed group's centered discrepancy consumes the actual bounded
child rooted moments on their own usage and precision. The positive/paired consumers use
`compressedBin_range_usage` before completion; conditional integration then retains the
actual joint densities. Reset-right execution remains separate. Equal pairs and zero
endpoints retain zero charge. The spectral factor uses the unchanged actual walk length. -/
theorem completedGroup_initial_compressed_centered_precision
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ) (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins,
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
      fine ≠ coarse → ∀ n ∈ ({fine, coarse} : Finset ℕ), n < M → 0 < n →
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
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    ∃ F G,
      B.completedGroup (fun n q => if n < M then B.compressedHistory exponent ζ floor n q
        else none) M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
      B.completedGroup (fun n q => if n < M then B.evaluate n q else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r = some G ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.usage.retains (channels B.padding) σ y)
        (fun σ x y => (F - G) σ x y - rowSliceMean Xs Yu (F - G) x y) ≤
        32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)) ^ (2 * B.steps M r d) *
          B.initialRootGroupCharge M d r coefficient ∧
      ∀ ks ka, 0 ≤ B.rankCharge → B.binRate = rate →
        r.source.rate = rate ks → r.terminal.rate = rate ka →
        r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) →
        rowNormPow 4 P r.source.rate
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.usage.retains (channels B.padding) σ y)
          (fun σ x y => (F - G) σ x y - rowSliceMean Xs Yu (F - G) x y) ≤
          ((2 : ℝ) ^ (-B.requestPrecision M r) * (64 : ℝ)⁻¹ ^ d) ^ 4 *
            B.initialActiveRootGroupCharge M d r ka coefficient := by
  dsimp only
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hp (i : {i // i ∈ B.bins}) :=
    B.pairedSample_initial_compressed_precision_at exponent ζ floor M d i.val hM r hsr
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
  obtain ⟨F, G, hf, hg, hb⟩ := B.completedGroup_initial_compressed_centered_error
    exponent ζ floor M d hbins r s t hst
    ks ku ss su hs hu a c ε
    (fun i hi => by simpa only [a, dite_eq_left hi] using hA ⟨i, hi⟩)
    (fun i hi => by simpa only [c, dite_eq_left hi] using hC ⟨i, hi⟩)
    (fun i hi => by simpa only [a, c, dite_eq_left hi] using he ⟨i, hi⟩)
  refine ⟨F, G, hf, hg, hb, ?_⟩
  intro ks ka hcharge hrate hsource hterminal htask
  have hactive := B.initialRootGroupCharge_le_active hcharge hrate M d ks ka r
    hsource hterminal htask coefficient
  exact hb.trans ((mul_le_mul_of_nonneg_left hactive (by positivity)).trans
    (mul_le_mul_of_nonneg_right (B.initial_completion_gap_payment M d ks r hsource)
      ((B.initialRootGroupCharge_nonneg M d r coefficient).trans hactive)))

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
