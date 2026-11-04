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
without a rarity factor. Every prefix cube and summed group cost remains explicit.

These original finite bounds consume certified actual children, not a parent accuracy
hypothesis. They do not allocate the displayed importance/bin/prefix costs jointly with
recursive reserves or establish simultaneous changing-request induction or native RL=L.

## Main results

* `initial_compressed_mean_moment`: transported mean discrepancy plus semantic deficit.
* `initial_compressed_prefix_absolute`: actual absolute error before preparation.
* `initial_compressed_preparation`: full-rank sensitivity and actual usage-walk noise.
* `exists_initial_compressed_fourMax`: the shared sharp reserve on computed histories.
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
