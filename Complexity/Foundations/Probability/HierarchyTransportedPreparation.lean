/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyInitialPerturbation
public import Complexity.Foundations.Probability.HierarchyInitialIntegrated

/-!
# Preparation payments for computed approximate initial histories

Literal completed-group executions identify both histories. Their finite prefix transport
is added to the semantic omitted/inactive deficit and centered first noise in matrix units.
The polynomial preparation and full-terminal rank gate then pay their actual usage mean
through the existing sensitivity theorem; centered preparation noise is paid separately,
without a rarity factor. Ordinary transport keeps its prefix cube and summed group costs.

These original finite bounds consume strict lower-budget own-request rooted precision,
not a parent accuracy hypothesis. All four moments and the sharp reserve receive explicit
finite numerical payments. The precision route also consumes an own-mask clipped
conditional-mean payment for its first coordinate, keeping the previous ordinary-noise
and preparation costs. Its sharp fine-bin coefficient and finite Minkowski remove bin
and prefix cubes from clipped means. An explicit joint window condition pays that finite
transport part, without asserting the condition uniformly.
Uniform absorption of the displayed costs, simultaneous
changing-request induction and native RL=L remain open.

## Main results

* `initial_compressed_mean_moment`: transported mean discrepancy plus semantic deficit.
* `initial_compressed_prefix_absolute`: actual absolute error before preparation.
* `initial_compressed_first_noise`: centered transport with the actual conditional mean.
* `initial_compressed_preparation`: full-rank sensitivity and actual usage-walk noise.
* `exists_initial_compressed_fourMax`: the shared sharp reserve on computed histories.
* `initial_compressed_precision_reserve`: numerical reserve from own-request rooted IH.
* `initialComputedRelativeMoment_polynomial_firstNoise_le`: actual semantic minimum consumer.
* `initialComputedRelativeMoment`: denominator-retaining semantic first-noise costs.
* `initialComputedPrecisionMoment`: clipped own-mask first-mean cost in the literal reserve.
* `initial_compressed_precision_clipped_first`: actual clipped first-coordinate payment.
* `initialPerturbationFactor`: target-dependent worst-pair transport payment.
* `initialComputedMoment_final_firstNoise_zero`: exact old absolute-envelope noise cost.
* `initialComputedMoment_firstNoise_not_uniform`: a uniform envelope obstruction.
-/
public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Finite matrix-unit payment: transported prefix cost plus the semantic history's
centered noise and omitted/inactive deficit. No claim that this charge is small is built in. -/
@[expose] def initialTransportMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (j : ℕ) : ℝ :=
  8 * (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i + 8 *
          (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
            (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
            rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
              (retainedMask R.terminal (side P ka) B.padding st)
              (fun _ => B.initialPolynomialLoss M n j r)))

/-- Sup norm payment for a fixed-pair inverse denominator. Unlike inverse rate alone,
this retains the target. It is a worst-pair bound, not a pair-weighted recursive IH. -/
@[expose] def initialPerturbationFactor (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) : ℝ :=
  ‖fun xy : ZMod P × ZMod P => (rate ka + G xy.1 xy.2)⁻¹‖ ^ 4

/-- The target-dependent factor never exceeds the inverse-rate payment for a
nonnegative target. A zero target somewhere can still force equality. -/
lemma initialPerturbationFactor_le (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (hG : ∀ x y, 0 ≤ G x y) :
    initialPerturbationFactor ka G ≤ (rate ka)⁻¹ ^ 4 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (rate_pos ka).le : 0 ≤ (rate ka)⁻¹)).mpr
  intro xy
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (add_pos_of_pos_of_nonneg (rate_pos ka) (hG xy.1 xy.2)))]
  exact inv_anti₀ (rate_pos ka) (le_add_of_nonneg_right (hG xy.1 xy.2))

/-- A single zero target entry makes the worst-pair payment exactly inverse rate.
This explains why this refinement alone cannot give uniform absorption on sparse targets. -/
lemma initialPerturbationFactor_eq_of_zero (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (hG : ∀ x y, 0 ≤ G x y) (x y : ZMod P) (hxy : G x y = 0) :
    initialPerturbationFactor ka G = (rate ka)⁻¹ ^ 4 := by
  apply le_antisymm (initialPerturbationFactor_le ka G hG)
  have hw := norm_le_pi_norm (fun xy : ZMod P × ZMod P =>
    (rate ka + G xy.1 xy.2)⁻¹) (x, y)
  simp only [hxy, add_zero, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (rate_pos ka))] at hw
  exact pow_le_pow_left₀ (inv_nonneg.mpr (rate_pos ka).le) hw 4

/-- Constant positive targets expose a strict gain, without asserting that such a lower
bound holds for every admissible matrix. -/
lemma initialPerturbationFactor_const (ka : ℕ) (g : ℝ) :
    initialPerturbationFactor (P := P) ka (fun _ _ => g) = |(rate ka + g)⁻¹| ^ 4 := by
  simp [initialPerturbationFactor, Real.norm_eq_abs]

/-- Centered first noise of the literal computed prefixes. The transported perturbation
is centered at its own conditional mean before adding the semantic completion noise.
Both payments are unconditional; no heavy-event rarity factor is applied to noise.
Returns the absolute payment and a denominator-retaining semantic group payment. -/
theorem initial_compressed_first_noise
    (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1, ∀ (G : Matrix (ZMod P) (ZMod P) ℝ),
        (∀ x y, 0 ≤ G x y) → ∀ (Lt : ℕ)
          (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ),
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
            ka G (firstSignalIncrement F ka second) 0 0 j) ≤
          (rate ka)⁻¹ ^ 4 * (8 * (16 *
            (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
            (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) * (64 / 63)) *
              (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4)) ∧
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) Lt B.padding ss st
            ka G (firstSignalIncrement F ka second) 0 0 j) ≤
          8 * (16 * initialPerturbationFactor ka G *
            (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
              B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
                ks ka ss st G (j + 1)) := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj target htarget Lt second
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hsr
  have hdiff := hpref (j + 1) (by omega)
  simp only [ht, hs, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  have hnoise := B.initialPrefix_noise_dyadic M hM hbins r R.source R.terminal
    R.source_terminal ks ka ss st hs ht G hG (j + 1) (by omega)
  dsimp only at hnoise
  simp only [Nat.add_sub_cancel] at hnoise
  have hb := rowNormPow_centered_fourth_le hNu
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st) (F (j + 1)) (G (j + 1))
  have hn := actualNoiseEntry_first_prefix_row_le R.source R.terminal
    (side P ks) (side P ka) Lt B.padding ss st F ka target htarget second 0
    (by intros; rfl) j hNu
  constructor
  · apply hn.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
      convert hdiff using 1
      congr 8
      exact congrArg (fun c => c.rate) hs
    · convert hnoise using 1; congr 8
  · rw [actualNoiseEntry_first_prefix_row_eq R.source R.terminal
      (side P ks) (side P ka) Lt B.padding ss st F ka target htarget second 0
      (by intros; rfl) j P r.source.rate]
    let normed := fun (T : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) σ x y =>
      T σ x y / (rate ka + target x y)
    have hc := rowNormPow_centered_fourth_le hNu
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (normed (F (j + 1))) (normed (G (j + 1)))
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply add_le_add
    · rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
      have hdifference : rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (F (j + 1) - G (j + 1)) ≤
          ((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i := by
        convert hdiff using 1
        congr 8
        exact congrArg (fun c => c.rate) hs
      have hw := rowNormPow_mul_le_pi_norm hNu
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (F (j + 1) - G (j + 1))
        (fun xy : ZMod P × ZMod P => (rate ka + target xy.1 xy.2)⁻¹)
      have he : normed (F (j + 1)) - normed (G (j + 1)) =
          (fun σ x y => (F (j + 1) - G (j + 1)) σ x y *
            (rate ka + target x y)⁻¹) := by
        funext σ x y
        dsimp only [normed, Pi.sub_apply, Matrix.sub_apply]
        ring
      rw [he]
      exact hw.trans (mul_le_mul_of_nonneg_left hdifference (by positivity))
    · have href := B.initialPrefix_relative_noise M hM hbins r R.source R.terminal
        R.source_terminal ks ka ss st hs ht G hG target (j + 1)
      simpa only [normed, rowSliceMean, ← expect_div, ← sub_div] using href

/-- Four explicit row-moment costs for computed initial history: deterministic first
mean/deficit, preparation mean, centered first noise, and usage noise. Bin importance
and prefix cubes enter through the executed group charges ε, without parent accuracy. -/
@[expose] def initialComputedMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let T := ((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i
  let Z := (((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) * (64 / 63)) *
    (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4
  if noise then
    if ν = 0 then (rate ka)⁻¹ ^ 4 * (8 * (16 * T + Z)) else
      (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4
  else if ν = 0 then (rate ka)⁻¹ ^ 4 * (8 * (T +
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ => B.initialPolynomialLoss M n j r))) else
    P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
      B.initialTransportMoment M n r R ks ka ss st ε j

/-- Nonnegative group payments produce nonnegative costs for each of the four moments. -/
lemma initialComputedMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν := by
  have hs := sum_nonneg (fun i (_ : i ∈ range (j + 1)) => hε i)
  have hr := rate_pos ks
  have hnorm := rowNormPow_nonneg (s := 4)
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (mul_nonneg (Nat.cast_nonneg P) hr.le) (fun _ => B.initialPolynomialLoss M n j r)
  unfold initialComputedMoment initialTransportMoment
  split_ifs <;> positivity

/-- Computed four-statistic payment retaining pairwise semantic normalization. Only the
first noise is sharpened; taking the minimum preserves the previous absolute payment.
The transported error pays the target-dependent worst-pair inverse denominator.
No pair-weighted IH or global absorption is claimed. -/
@[expose] def initialComputedRelativeMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let old := B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν
  if noise ∧ ν = 0 then min old
    (8 * (16 * initialPerturbationFactor ka B.base *
      (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
      B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
        ks ka ss st B.base (j + 1))) else old

/-- The literal computed first-noise minimum consumes the polynomial semantic payment.
The transported child charge is retained unchanged and is not paid by this theorem. -/
theorem initialComputedRelativeMoment_polynomial_firstNoise_le (B : BudgetData HP P)
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hb : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (M n : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st) (ha : ka ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (ε : ℕ → ℝ) (ζ Lh Lρ : ℝ) (j : ℕ) :
    let m := Nat.log2 M + 1
    let q := { r with usage := r.terminal }
    B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0 ≤
      min (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0)
        (8 * (16 * initialPerturbationFactor ka B.base *
          (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i) +
          (256 * B.binCap) ^ 4 * ((min (j + 1) m : ℕ) ^ (3 : ℕ) *
            ∑ i ∈ range (min (j + 1) m),
              ((2 : ℝ) ^ (-B.requestPrecision M q) *
                (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4))) := by
  dsimp only
  simp only [initialComputedRelativeMoment, Fin.isValue]
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add le_rfl
  exact B.initialRelativeNoiseBudget_polynomial_le hrate hcutoff H hb M r
    R.source R.terminal R.source_terminal ks ka ss st hs ht ha hC hC1 (j + 1)

/-- Nonnegative input payments give nonnegative sharpened costs. -/
lemma initialComputedRelativeMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ)
    (hε : ∀ i, 0 ≤ ε i) (ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν := by
  have hold := B.initialComputedMoment_nonneg M n r R ks ka ss st ε hε ζ Lh Lρ j noise ν
  have hrel := B.initialRelativeNoiseBudget_nonneg M r hr R.source R.terminal
    R.source_terminal ks ka ss st B.base (j + 1)
  have hsum := sum_nonneg (fun i (_ : i ∈ range (j + 1)) => hε i)
  unfold initialComputedRelativeMoment initialPerturbationFactor
  split_ifs <;> positivity

/-- Even with no transported child error, the final semantic first-noise payment has
this exact coefficient relative to its own parent precision. Increasing `M` alone does
not shrink the ratio: `rate ka = 2^(-4*ka)` leaves a factor `2^(16*ka)`.
This is an identity for the numerical envelope, not a lower bound on actual noise. -/
theorem initialComputedMoment_final_firstNoise_zero (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ζ Lh Lρ : ℝ) :
    B.initialComputedMoment M n r R ks ka ss st (fun _ => 0) ζ Lh Lρ
      (Nat.log2 M) true 0 =
      (8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
        ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 := by
  simp only [initialComputedMoment, sum_const_zero, mul_zero, ↓reduceIte,
    dyadicSlack_last, pow_one, zero_add, rate, inv_pow, inv_inv]
  ring

/-- No statistical-budget threshold absorbs this envelope by one coefficient uniform
in the terminal exponent. The exponent is chosen before the budget and request; no
changing-request IH is assumed or refuted. Here `ka` is independent of `r.terminal`:
there is no admissibility, horizon/prime bound or successful-execution guard. This does
not give a counterexample on valid recursive calls. Sharper actual conditional-noise
analysis is needed to use this route for the simultaneous invariant. -/
theorem initialComputedMoment_firstNoise_not_uniform (B : BudgetData HP P) (A : ℝ) :
    ∃ ka : ℕ, ∀ (M n : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (R : RoleProfile 3) (ks : ℕ) (ss st : List (ZMod P)) (ζ Lh Lρ : ℝ),
      A * ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 <
        B.initialComputedMoment M n r R ks ka ss st (fun _ => 0) ζ Lh Lρ
          (Nat.log2 M) true 0 := by
  obtain ⟨ka, hk⟩ := pow_unbounded_of_one_lt (A / (8 / 63 ^ 4))
    (by norm_num : (1 : ℝ) < 2 ^ 16)
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 8 / 63 ^ 4)] at hk
  rw [← pow_mul, Nat.mul_comm 16 ka, pow_mul] at hk
  refine ⟨ka, ?_⟩
  intro M n r R ks ss st ζ Lh Lρ
  rw [B.initialComputedMoment_final_firstNoise_zero]
  exact mul_lt_mul_of_pos_right (by simpa only [mul_comm] using hk) (by positivity)

/-- Nonnegative transported costs can only increase the final semantic noise charge.
Its parent-normalized coefficient is independent of the statistical budget. -/
theorem initialComputedMoment_final_firstNoise_ge (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ : ℝ) :
    (8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
        ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4 ≤
      B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ (Nat.log2 M) true 0 := by
  rw [← B.initialComputedMoment_final_firstNoise_zero M n r R ks ka ss st ζ Lh Lρ]
  have hsum := sum_nonneg (fun i (_ : i ∈ range (Nat.log2 M + 1)) => hε i)
  simp only [initialComputedMoment, sum_const_zero, mul_zero, ↓reduceIte, zero_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  exact le_add_of_nonneg_left (by positivity)

/-- This scalar envelope retains a nondecaying final-noise coefficient even after all
three sharp repairs. In particular a depth-only fixed-request limit cannot establish a
single recursive constant for unbounded terminal exponents. This is an envelope lower
bound; actual error might be much smaller. The raw/width/tail terms are still present. -/
theorem initialComputedNumericalReserve_ge_noise (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (ζ Lh Lρ floor cap C Cpre : ℝ) :
    let a := fun j noise ν =>
      B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
    128 * (HP.K : ℝ) * C ^ 4 *
        ((8 / 63 ^ 4 : ℝ) * ((2 : ℝ) ^ ka) ^ 16 *
          ((2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })) ^ 4) ≤
      initialNumericalReserve HP M floor cap C Cpre
        (fun j => (a j false 0 + a j false 1) + (a j true 0 + a j true 1)) := by
  dsimp only
  let cost := B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ (Nat.log2 M)
  have hc (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν :=
    B.initialComputedMoment_nonneg M n r R ks ka ss st ε hε ζ Lh Lρ _ noise ν
  have ha (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν ^ (4⁻¹ : ℝ) :=
    Real.rpow_nonneg (hc noise ν) _
  have hpow : cost true 0 ≤
      ((cost false 0 ^ (4⁻¹ : ℝ) + cost false 1 ^ (4⁻¹ : ℝ)) +
        (cost true 0 ^ (4⁻¹ : ℝ) + cost true 1 ^ (4⁻¹ : ℝ))) ^ 4 := by
    calc
      _ = (cost true 0 ^ (4⁻¹ : ℝ)) ^ 4 :=
        (Real.rpow_inv_natCast_pow (hc true 0) (by decide : 4 ≠ 0)).symm
      _ ≤ _ := pow_le_pow_left₀ (ha true 0)
        (by linarith [ha false 0, ha false 1, ha true 1]) 4
  exact (mul_le_mul_of_nonneg_left
    ((B.initialComputedMoment_final_firstNoise_ge M n r R ks ka ss st ε hε ζ Lh Lρ).trans
      hpow) (by positivity)).trans
    (initialNumericalReserve_ge_final HP M floor cap C Cpre
      (fun j =>
        (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j false 0 ^ (4⁻¹ : ℝ) +
          B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j false 1 ^ (4⁻¹ : ℝ)) +
        (B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 0 ^ (4⁻¹ : ℝ) +
          B.initialComputedMoment M n r R ks ka ss st ε ζ Lh Lρ j true 1 ^ (4⁻¹ : ℝ))))

/-- Four computed costs from own-request precision, using clipped mean transport for
the first coordinate. Ordinary first noise and saturated preparation retain their existing
payments. This minimum is consumed by the literal four-max and raw clipped-error gates. -/
@[expose] def initialComputedPrecisionMoment (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (j : ℕ) (noise : Bool) (ν : Fin 2) : ℝ :=
  let ε := fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
    { r with usage := r.terminal } coefficient
  let old := B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j noise ν
  if !noise ∧ ν = 0 then min old
    (8 * (((∑ i ∈ range (j + 1),
      (B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
        { r with usage := r.terminal } ka coefficient) ^ (4⁻¹ : ℝ)) ^ 4) +
      rowNormPow 4 P r.source.rate
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
          (rate ka + B.base x y))))) else old

/-- The existing first-mean minimum consumes the finite joint allocation condition.
Only the clipped transport part is paid here; the semantic deficit and other three
statistics remain separate. Uniform use requires the window condition uniformly. -/
theorem initialComputedPrecisionMoment_first_paid (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate) (H : Horizon P)
    (M n j ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (R : RoleProfile 3) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ)
    (hwindow : 2 *
      (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      (∑ i ∈ range (j + 1), B.initialClippedRootWindow M
        (dyadicSlack (Nat.log2 M + 1) i) ka { r with usage := r.terminal }) ≤
      (2 : ℝ) ^ B.rankCharge) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 0 ≤
      8 * (coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 +
        rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
            (rate ka + B.base x y)))) := by
  unfold initialComputedPrecisionMoment
  simp only [Bool.not_false, Fin.isValue, and_self, ↓reduceIte]
  apply (min_le_right _ _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  exact B.initialClippedRootPrefix_paid hcharge hrate H M (j + 1) ks ka ha hi
    { r with usage := r.terminal } hs ht htask hwindow coefficient

/-- The new first-mean minimum and all retained costs are nonnegative. -/
lemma initialComputedPrecisionMoment_nonneg (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P))
    (coefficient ζ Lh Lρ : ℝ) (j : ℕ) (noise : Bool) (ν : Fin 2) :
    0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν := by
  have hold := B.initialComputedRelativeMoment_nonneg M n r hr R ks ka ss st
    (fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient)
    (fun i => B.initialRootGroupCharge_nonneg M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient) ζ Lh Lρ j noise ν
  have hsum := sum_nonneg (fun i (_ : i ∈ range (j + 1)) =>
    B.initialClippedRootGroupCharge_nonneg M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } ka coefficient)
  have hrow := rowNormPow_nonneg (s := 4) (mul_nonneg (Nat.cast_nonneg P) hr)
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))
  unfold initialComputedPrecisionMoment
  split_ifs <;> positivity

section Polynomial
variable (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (n : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss)
  (ht : r.terminal = gridChannel R.terminal ka st)
  (hks : ks ≤ H.maxExponent)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)

include hM hbins hrate hcutoff haux hD hn hs ht hks hC hC1

/-- Actual computed histories pay absolute error before the nonlinear preparation.
The group costs can be supplied by `completedGroup_initial_compressed_error`, retaining
its bin-count cube and the strict-IH endpoint importance sums. The semantic deficit and
its centered noise are derived, rather than assumed as parent-error premises. -/
theorem initial_compressed_prefix_absolute
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun σ x y => F (j + 1) σ x y - B.base x y) ≤
        B.initialTransportMoment M n r R ks ka ss st ε j := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj
  dsimp only [initialTransportMoment]
  have hdiff := hpref (j + 1) (by omega)
  simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  have hsemantic := B.initialPrefix_absolute_moment M hM n hbins hrate hcutoff haux hD H hn
    r R ks ka ss st hs ht hks hC hC1 G hG j hj
  dsimp only at hsemantic
  have hadd := rowNormPow_add_le
    (X := retainedMask R.source (side P ks) B.padding ss)
    (Y := retainedMask R.terminal (side P ka) B.padding st)
    (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)
    (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y)
    (fun σ x y => G (j + 1) σ x y - B.base x y)
  have he : (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y +
      (G (j + 1) σ x y - B.base x y)) =
      (fun σ x y => F (j + 1) σ x y - B.base x y) := by
    funext σ x y; ring
  rw [he] at hadd
  apply hadd.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ hsemantic
  convert hdiff using 1; congr 8

/-- The transported conditional-mean discrepancy combines directly with the semantic
history's omitted/inactive deficit. Unlike the absolute preparation input, this deterministic
payment does not charge semantic centered noise. All prefix transport costs remain literal. -/
theorem initial_compressed_mean_moment
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      let Xs := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) Xs Ya
          (fun _ x y => rowSliceMean Xs Ya (F (j + 1)) x y - B.base x y) ≤
        8 * (((j + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (j + 1), ε i +
          rowNormPow 4 P (rate ks) Xs Ya (fun _ => B.initialPolynomialLoss M n j r)) := by
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  obtain ⟨groups, reference, hgroups, href, hpref, _⟩ :=
    B.initial_compressed_prefix_error exponent ζ floor M { r with usage := r.terminal }
      hsr A C ε hA hCrun herr
  let F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let G : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hG : B.initialPrefixes M r = some G := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  change ∀ j < Nat.log2 M + 1, _
  intro j hj
  have hdiff := hpref (j + 1) (by omega)
  simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid] at hdiff
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hm (x y : ZMod P) : B.base x y - rowSliceMean Xs Ya (G (j + 1)) x y =
      B.initialPolynomialLoss M n j r x y := by
    have h := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 G hG j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at h
    convert h using 1; congr 8
  have he : (fun (_σ : Environment P 3) x y => rowSliceMean Xs Ya (G (j + 1)) x y - B.base x y) =
      (fun (_σ : Environment P 3) x y => -B.initialPolynomialLoss M n j r x y) := by
    funext σ x y
    linarith [hm x y]
  have hjensen := rowNormPow_sliceMean_fourth_le hNu Xs Ya
    (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y)
  have hlin : rowSliceMean Xs Ya (fun σ x y => F (j + 1) σ x y - G (j + 1) σ x y) =
      fun x y => rowSliceMean Xs Ya (F (j + 1)) x y -
        rowSliceMean Xs Ya (G (j + 1)) x y := by
    funext x y
    simp only [rowSliceMean, expect_sub_distrib]
  rw [hlin] at hjensen
  have hb := rowNormPow_sub_le_centered (X := Xs) (Y := Ya) hNu
    (fun _ => rowSliceMean Xs Ya (F (j + 1))) (rowSliceMean Xs Ya (G (j + 1))) B.base
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · apply hjensen.trans
    convert hdiff using 1; congr 8
  · rw [he]
    simp only [rowNormPow, abs_neg, Xs, Ya, le_refl]

/-- The actual computed prefix pays polynomial preparation and full-rank gate
sensitivity. The usage walk is executed on that very prefix; its centered noise is paid
unconditionally. Neither a free prefix family nor parent accuracy is a premise. -/
theorem initial_compressed_preparation
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (fun _ => secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ
            (F (j + 1)) B.base) ≤
          P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
            B.initialTransportMoment M n r R ks ka ss st ε j ∧
        ∀ (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)),
          (List.range (Nat.log2 M + 1)).mapM (fun i =>
            B.complete M r (B.binPreparation bin r (F (i + 1)))
              (dyadicSlack (Nat.log2 M + 1) i)) = some W →
          (∀ x y, actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement F ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
            0 1 j x y ≤
            secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ (F (j + 1)) B.base x y) ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base (firstSignalIncrement F ka
                (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
              0 1 j) ≤
            (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
              (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  obtain ⟨groups, hgroups, habs⟩ := B.initial_compressed_prefix_absolute M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro j hj
  refine ⟨(secondMeanEnvelope_moment R B.padding ss st ks ka ku husage hLh hLρ ζ
    _ B.base (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)).trans
      (mul_le_mul_of_nonneg_left (habs j hj) (by positivity)), ?_⟩
  intro W hW
  constructor
  · exact B.initialSecondSignal_clippedMean_le M bin ka ku r R ks ss st hs ht hu
      (congrFun haux bin) _ W hW hLρ hh hρ ζ j hj
  · exact B.initialSecondSignal_noise_moment M bin
      (fun d => by rw [haux]; exact ⟨polynomialPrepCutoff4_nonneg _ _,
        polynomialPrepCutoff4_le_one _ _⟩) r R ks ku ss st hs hu _ W hW ka B.base ζ j hj

/-- All four actual row moments paid on their respective rank and usage masks.
The only supplied error bounds are executed group perturbations, obtainable from strict
own-request rooted precision via `completedGroup_initial_compressed_precision`. -/
theorem initial_compressed_four_moments
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (A C : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hA : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
        else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (A j))
    (hCrun : ∀ j < Nat.log2 M + 1,
      B.completedGroup (fun m q => if m < M then B.evaluate m q else none)
        M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
        { r with usage := r.terminal } = some (C j))
    (herr : ∀ j < Nat.log2 M + 1, rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y) (A j - C j) ≤ ε j)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        ∀ j < Nat.log2 M + 1, ∀ (ν : Fin 2),
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
              (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
            B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j false ν ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base Δ 0 ν j) ≤
            B.initialComputedRelativeMoment M n r R ks ka ss st ε ζ Lh Lρ j true ν := by
  obtain ⟨groups, hgroups, hprep⟩ := B.initial_compressed_preparation M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
    bin ku husage hu hLh hLρ hh hρ
  obtain ⟨gmean, hgmean, hmean⟩ := B.initial_compressed_mean_moment M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C ε hA hCrun herr
  have he := Option.some.inj (hgmean.symm.trans hgroups)
  subst gmean
  have hnonempty : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨gnoise, hgnoise, hnoise⟩ := B.initial_compressed_first_noise M hM hnonempty
    exponent ζ floor r R ks ka ss st hs ht A C ε hA hCrun herr
  have he := Option.some.inj (hgnoise.symm.trans hgroups)
  subst gnoise
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj ν
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  fin_cases ν <;> simp only [Fin.zero_eta, Fin.mk_one]
  · constructor
    · have hb := actualClippedMean_first_prefix_row_le HP R.source R.terminal
        (side P ks) (side P ka) (side P ku) B.padding ss st
        (fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum) ka B.base hC ζ
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) j hNu
      apply hb.trans
      simp only [initialComputedRelativeMoment, initialComputedMoment, Bool.false_eq_true,
        ↓reduceIte, Fin.isValue]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hmean j hj using 1
      congr 8
      exact congrArg (fun c => c.rate) hs
    · have hz := hnoise j hj B.base hC (side P ku)
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
      simpa only [initialComputedRelativeMoment, initialComputedMoment, ↓reduceIte,
        Fin.isValue, and_self] using le_min hz.1 hz.2
  · obtain ⟨hp, hz⟩ := (hprep j hj).2 W hW
    constructor
    · have hb : rowNormPow 4 P r.source.rate
          (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement (fun p σ x y => ((groups.take p).map
              (fun T => T σ x y)).sum) ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)) 0 1 j x y) ≤
          rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ku) B.padding st)
            (fun _ => secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ
              (fun σ x y => ((groups.take (j + 1)).map (fun T => T σ x y)).sum) B.base) := by
        apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
        intro σ x y _ _
        have hnon : 0 ≤ actualClippedMean HP R.source R.terminal
            (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base ζ
            (firstSignalIncrement (fun p σ x y => ((groups.take p).map
              (fun T => T σ x y)).sum) ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)) 0 1 j x y := by
          simp only [actualClippedMean, Fin.isValue, one_ne_zero, ↓reduceIte]
          positivity
        rw [one_mul, abs_of_nonneg hnon]
        exact pow_le_pow_left₀ (by positivity) ((hp x y).trans (le_abs_self _)) 4
      apply hb.trans
      simpa only [initialComputedRelativeMoment, initialComputedMoment, Bool.false_eq_true,
        Fin.isValue, one_ne_zero, and_false, ↓reduceIte, hs, gridChannel] using (hprep j hj).1
    · simpa only [initialComputedRelativeMoment, initialComputedMoment, Fin.isValue,
        one_ne_zero, and_false, ↓reduceIte] using hz

/-- The literal computed first clipped coordinate from own-request scalar rooted IH.
Positive means are compared before signed pairing, then stationary completed group means
and correlated prefixes are summed. Rounded masses, endpoint guards and precision remain
explicit. Ordinary progress and the saturated second coordinate are separate payments. -/
theorem initial_compressed_precision_clipped_first
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (Lt : ℕ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      let Xs := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate Xs Ya
          (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
            Lt B.padding ss st ka B.base ζ (firstSignalIncrement F ka second) 0 0 j x y) ≤
        8 * (((∑ i ∈ range (j + 1),
          (B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
            { r with usage := r.terminal } ka coefficient) ^ (4⁻¹ : ℝ)) ^ 4) +
          rowNormPow 4 P r.source.rate Xs Ya (fun _ x y =>
            min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y)))) := by
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hsr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  have hprep (bin : ℕ) (v : ℝ) (hv : B.cutoff bin v ≠ 0) : B.auxiliary bin v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      bin (fun _ => 1) hv
  let q := { r with usage := r.terminal }
  have hp (j : ℕ) (i : {i // i ∈ B.bins}) :=
    B.pairedSample_initial_compressed_clipped_precision hrate hcutoff hD H exponent ζ floor
      M (dyadicSlack (Nat.log2 M + 1) j) i.val hM q R.source R.terminal R.source_terminal
      ks ka ss st hs ht hks
      (by have hi : i.val ∈ range (n + 1) := by simpa only [hbins] using i.property
          have hb := mem_range.mp hi; omega)
      (hprep i.val) hC hC1 hk (D i.val) (hzero i.val) coefficient (ih i.val i.property)
  choose A C hA hCrun herr using hp
  let a := fun j i => if hi : i ∈ B.bins then A j ⟨i, hi⟩ else 0
  let c := fun j i => if hi : i ∈ B.bins then C j ⟨i, hi⟩ else 0
  let ε := fun j bin =>
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      q.source (midpoint q) q.terminal (B.binRate bin)
    let fine := LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale q (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale q (some bin))
    if fine = coarse then 0 else
    8 * (B.initialClippedRootCoefficient ka bin) *
      (B.initialEndpointCharge fine Q.direct coefficient +
        B.initialEndpointCharge coarse Q.direct coefficient)
  have hg (j : ℕ) := B.completedGroup_initial_compressed_clipped_mean exponent ζ floor M
    (dyadicSlack (Nat.log2 M + 1) j) hne q R.source R.terminal R.source_terminal
    ks ka ss st hs ht (a j) (c j) (ε j)
    (fun i hi => by simpa only [a, dite_eq_left hi] using hA j ⟨i, hi⟩)
    (fun i hi => by simpa only [c, dite_eq_left hi] using hCrun j ⟨i, hi⟩)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))
    (fun i hi => by simpa only [a, c, dite_eq_left hi] using herr j ⟨i, hi⟩)
  choose F G hF hG he using hg
  have hem (j : ℕ) : rowNormPow 4 P r.source.rate
      (fun σ x => q.source.retains (channels B.padding) σ x)
      (fun σ y => q.usage.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|rowSliceMean
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y) (F j - G j) x y| /
        (rate ka + B.base x y))) ≤
      B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) j) q ka coefficient := by
    convert he j using 1 <;>
      simp only [q, hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, X, Y, rowNormPow, rowSliceMean,
        initialClippedRootGroupCharge, ε]
  obtain ⟨groups, reference, hgroups, href, hprefix⟩ :=
    B.initial_compressed_prefix_clipped_mean exponent ζ floor M q hsr F G
      (fun j => B.initialClippedRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) j)
        q ka coefficient) (fun j _ => hF j) (fun j _ => hG j)
      (fun x y => rate ka + B.base x y)
      (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y)) (fun j _ => hem j)
  let f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let g : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
    fun p σ x y => ((reference.take p).map (fun T => T σ x y)).sum
  have hgrun : B.initialPrefixes M r = some g := by
    unfold initialPrefixes
    rw [href]
    rfl
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro j hj
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Ya := retainedMask R.terminal (side P ka) B.padding st
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hsr
  have hm (x y : ZMod P) : B.base x y - rowSliceMean Xs Ya (g (j + 1)) x y =
      B.initialPolynomialLoss M n j r x y := by
    have h := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 g hgrun j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at h
    exact h
  simp_rw [actualClippedMean_first_prefix_eq]
  have hmean (x y : ZMod P) : rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y =
      rowSliceMean Xs Ya (f (j + 1) - g (j + 1)) x y +
        -B.initialPolynomialLoss M n j r x y := by
    simp only [rowSliceMean, Pi.sub_apply, Matrix.sub_apply, expect_sub_distrib]
    have h := hm x y
    unfold rowSliceMean at h
    linarith
  change rowNormPow 4 P r.source.rate Xs Ya
    (fun _ x y => min 1 (|rowSliceMean Xs Ya (f (j + 1)) x y - B.base x y| /
      (rate ka + B.base x y))) ≤ _
  simp_rw [hmean]
  apply (rowNormPow_clipped_add_le hNu Xs Ya
    (rowSliceMean Xs Ya (f (j + 1) - g (j + 1)))
    (fun x y => -B.initialPolynomialLoss M n j r x y)
    (fun x y => rate ka + B.base x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y))).trans
  simp only [abs_neg]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add _ le_rfl
  have hp := hprefix (j + 1) (by omega)
  convert hp using 1;
    simp only [q, hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid, retainedMask, Xs, Ya, f, g, rowNormPow, rowSliceMean,
      Pi.sub_apply]

/-- Literal all-four payment from strict lower-budget own-request rooted precision.
No parent accuracy or four-max budgets are premises. The child hypothesis is conditional:
this does not prove simultaneous recursive availability or uniform numerical absorption. -/
theorem initial_compressed_precision_moments
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        ∀ j < Nat.log2 M + 1, ∀ (ν : Fin 2),
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
              (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
            B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false ν ∧
          rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
            (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base Δ 0 ν j) ≤
            B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true ν := by
  have hnonempty : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hg (j : ℕ) := B.completedGroup_initial_compressed_precision exponent ζ floor M
    (dyadicSlack (Nat.log2 M + 1) j) hM hnonempty { r with usage := r.terminal }
    R.source R.terminal R.source_terminal ks ka ss st hs ht D hzero coefficient ih
  choose A C hA hCrun herr using hg
  obtain ⟨groups, hgroups, hrows⟩ := B.initial_compressed_four_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor A C
    (fun i => B.initialRootGroupCharge M (dyadicSlack (Nat.log2 M + 1) i)
      { r with usage := r.terminal } coefficient)
    (fun j _ => hA j) (fun j _ => hCrun j) (fun j _ => herr j)
    bin ku husage hu hLh hLρ hh hρ
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj ν
  obtain ⟨gmean, hgmean, hmean⟩ := B.initial_compressed_precision_clipped_first M hM n hbins
    hrate hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero
    coefficient ih (side P ku)
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  have he := Option.some.inj (hgmean.symm.trans hgroups)
  subst gmean
  have hold := hrows W hW j hj ν
  constructor
  · by_cases hν : ν = 0
    · subst ν
      simp only [initialComputedPrecisionMoment, Bool.not_false,
        and_self, ↓reduceIte]
      exact le_min hold.1 (hmean j hj)
    · simpa only [initialComputedPrecisionMoment, Bool.not_false, Bool.coe_true,
        hν, and_false, ↓reduceIte] using hold.1
  · simpa only [initialComputedPrecisionMoment, Bool.not_true, Bool.false_eq_true,
      false_and, ↓reduceIte] using hold.2

/-- The four literal row maxima are paid from own-request lower-budget rooted precision.
Minkowski retains all explicit computed costs and their separate masks. -/
theorem initial_compressed_precision_fourMax
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let Δ := firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
        let a := fun j noise ν =>
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
            ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
        ∀ j < Nat.log2 M + 1,
          vertexNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
            (actualFourMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base ζ Δ 0 j) ≤
            ((a j false 0 + a j false 1) + (a j true 0 + a j true 1)) ^ 4 ∧
          rowNormPow 4 P r.source.rate
            (retainedMask R.source (side P ks) B.padding ss)
            (retainedMask R.terminal (side P ka) B.padding st)
            (fun σ x y =>
              let truth := requestSignals ζ B.padding id r (fun _ => B.base)
                (B.binPreparation bin r (fun _ => B.base)) σ x y
              clippedError (truth 0) (truth 1)
                (uncompressedRow (Δ σ x) 0 (j + 1) y)) ≤
            ((a j false 0 + a j false 1) + (a j true 0 + a j true 1)) ^ 4 := by
  obtain ⟨groups, hgroups, hrows⟩ := B.initial_compressed_precision_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW j hj
  let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
  let Δ := firstSignalIncrement F ka
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hnon (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν := by
    cases noise
    · exact (rowNormPow_nonneg hNu _).trans (hrows W hW j hj ν).1
    · exact (rowNormPow_nonneg hNu _).trans (hrows W hW j hj ν).2
  have hpow (noise : Bool) (ν : Fin 2) :
      (cost noise ν ^ (4⁻¹ : ℝ)) ^ 4 = cost noise ν :=
    Real.rpow_inv_natCast_pow (hnon noise ν) (by decide : 4 ≠ 0)
  have hm (ν : Fin 2) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ Δ 0 ν j x y) ≤
      (cost false ν ^ (4⁻¹ : ℝ)) ^ 4 := by
    rw [hpow]; exact (hrows W hW j hj ν).1
  have hz (ν : Fin 2) : rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base Δ 0 ν j) ≤ (cost true ν ^ (4⁻¹ : ℝ)) ^ 4 := by
    rw [hpow]; exact (hrows W hW j hj ν).2
  constructor
  · apply actualFourMax_budget HP R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka B.base ζ Δ 0 j hNu
      (fun ν => cost false ν ^ (4⁻¹ : ℝ)) (fun ν => cost true ν ^ (4⁻¹ : ℝ))
      (fun ν => Real.rpow_nonneg (hnon false ν) _)
      (fun ν => Real.rpow_nonneg (hnon true ν) _)
    · intro ν
      exact (vertex_row_max (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (if ν = 0 then side P ka else side P ku) B.padding st)
        hNu _).trans (hm ν)
    · intro ν
      exact actualNoiseMax_budget _ _ _ _ _ _ _ _ _ B.base hC Δ 0 hNu ν j (hz ν)
  · simp_rw [B.requestSignals_eq_genuineTarget bin ka ku r R ks ss st hs ht hu
      (congrFun haux bin) B.base ζ]
    have hsub : side P ku ≤ side P ka := by
      apply (ceilDiv_le_iff_le_mul (by positivity : 0 < (2 : ℕ) ^ ku)).2
      have h := le_smul_ceilDiv (by positivity : 0 < (2 : ℕ) ^ ka) (b := P)
      exact h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) husage))
    have hb := raw_prefix_four_budget HP R.source R.terminal
      (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base hC ζ Δ 0 j
      (B.preparationPrefix_zero_off M bin ka ku r R ks ss st hs hu F W hW ζ j hj)
      (fun σ y hy => mem_retentionBox.mpr (fun v =>
        (mem_retentionBox.mp hy v).trans_le hsub)) hNu
      (fun ν => cost false ν ^ (4⁻¹ : ℝ)) (fun ν => cost true ν ^ (4⁻¹ : ℝ))
      (fun ν => Real.rpow_nonneg (hnon false ν) _)
      (fun ν => Real.rpow_nonneg (hnon true ν) _) hm hz
    exact hb

/-- The literal decoded-history sharp reserve is paid by explicit numerical costs of
strict lower-budget own-request rooted hypotheses. No parent accuracy, supplied four-max
budget or desired reserve is assumed. The first noise uses the minimum of the absolute
and pairwise conditional payments. Uniform absorption of this finite charge, and the
simultaneous IH, are separate obligations. -/
theorem initial_compressed_precision_reserve
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (hfloor : 0 ≤ floor) (cap Cdecoder Cpre : ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
        (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) = some W →
        let a := fun j noise ν =>
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
            ζ Lh Lρ j noise ν ^ (4⁻¹ : ℝ)
        B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap
          Cdecoder Cpre ≤
          initialNumericalReserve HP M floor cap Cdecoder Cpre
            (fun j => (a j false 0 + a j false 1) + (a j true 0 + a j true 1)) := by
  obtain ⟨groups, hgroups, hpaid⟩ := B.initial_compressed_precision_fourMax M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW
  have hr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  apply B.initialFourMaxReserve_le M bin ka ζ floor hfloor r hr R ks ku ss st B.base _ W
    cap Cdecoder Cpre _ (fun j => by
      have hc (noise : Bool) (ν : Fin 2) :=
        B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st
          coefficient ζ Lh Lρ j noise ν
      exact add_nonneg
        (add_nonneg (Real.rpow_nonneg (hc false 0) _) (Real.rpow_nonneg (hc false 1) _))
        (add_nonneg (Real.rpow_nonneg (hc true 0) _) (Real.rpow_nonneg (hc true 1) _)))
  · intro j hj
    have h := (hpaid W hW j hj).1
    simp only [hs, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid] at h ⊢
    convert h using 1; congr 8
  · intro j hj
    have h := (hpaid W hW j hj).2
    simp only [hs, ht, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid] at h ⊢
    convert h using 1; congr 8

end Polynomial

/-- Sharp parent comparison for literal computed approximate histories, using exactly
`compressedBin`'s shared decoder. This honest finite conditional reserve retains all actual
four-max and false-overflow costs. `initial_compressed_preparation` pays the second mean
and noise; joint allocation of transport costs and the remaining reserve is still open.
Constants are fixed before width, budget, history and children, in the shared kernel's order. -/
theorem exists_initial_compressed_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {cap ζ scale : ℝ} (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max cap 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (b : ℕ → ℝ), (∀ i, 0 < b i) → (∀ i, b i = 16 * b (i + 1)) →
      ∀ (M bin k : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      Admissible r → r.terminal.rate = rate k →
      B.cutoff bin = boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
        (fun _ => 1) → B.auxiliary bin = polynomialPrepCutoff4 HP.θ →
      ∀ (G : Matrix (ZMod P) (ZMod P) ℝ), (∀ x y, 0 ≤ G x y) →
      ∀ (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
        (childζ childFloor : ℝ)
        (groups : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)),
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then
          B.compressedHistory exponent childζ childFloor m q else none) M
          (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups →
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.complete M r (B.binPreparation bin r (F (j + 1)))
          (dyadicSlack (Nat.log2 M + 1) j)) = some W →
      ∀ (R : RoleProfile 3) (ks ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss →
      r.terminal = gridChannel R.terminal k st →
      r.usage = gridChannel R.terminal ku st →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (B.decodePrefixes M bin k ζ floor r F W)
        (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K G) ≤
        B.initialFourMaxReserve M bin k ζ floor r R ks ku ss st G F W cap C Cpre := by
  obtain ⟨C, hC, hscales⟩ := exists_decodePrefixes_fourMax HP hcap hζ hs hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hscales floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B b hb hstep M bin k r hr hrate hcut haux G hG exponent childζ childFloor
    groups _
  dsimp only
  intro W hW R ks ku ss st hsource hterminal husage
  exact hbound B b hb hstep M bin k r hr hrate hcut haux G hG _ W hW R ks ku ss st
    hsource hterminal husage

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
