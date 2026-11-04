/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialMeanPayment
public import Complexity.Foundations.Probability.NormalizedAtomRows.SecondEnvelope

/-!
# Preparation bias of actual initial histories

Polynomial preparation and the hierarchy's full-terminal rank gate act on the literal
postincrement first prefix. The existing absolute preparation sensitivity and conditional
Jensen estimates apply on the original source × usage environment. Its matrix-unit error
splits into the canonical omitted/inactive/coarse deficit and centered scheduled first noise.
The width and inverse rank-rate costs remain explicit. These original assembly results do
not pay second walk noise, global allocation, the parent induction or native RL=L.

## Main results

* `initialPrefix_absolute_moment`: actual deficit plus centered scheduled first noise.
* `preparationWalks_mean`: shared stationarity of successful literal preparation walks.
* `initialSecondSignal_clippedMean_le`: deterministic envelope for executed preparation walks.
* `initialSecondSignal_mean_moment`: same-environment conditional Jensen payment.
* `initial_requestSignals_two_envelopes`: actual compressed-bin raw-prefix consumer.
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

/-- The executed dense preparation is the existing full-rank selected preparation.
Usage does not replace the rank mask. -/
lemma binPreparation_eq_selected (B : BudgetData HP P) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ka : ℕ) (st : List (ZMod P)) (ht : r.terminal = gridChannel R.terminal ka st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    B.binPreparation bin r A = selectedPreparation HP B.padding R st ka A := by
  funext σ x y
  simp only [binPreparation, densePreparation, selectedPreparation, haux, ht,
    DenseRowRecipe.preparation, splitTerminal, gridChannel, coordinate, semanticSide_grid,
    retainedMask, id_eq]

/-- Successful preparation executions expose exactly the postincrement walk used by
`compressedBin`. All walks retain the original source and usage suffixes. -/
theorem preparationWalks_get (B : BudgetData HP P) (M bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    W[j]?.getD 0 = conditionalWalk
      (X R.source (side P ks) (CopyPadding.identifier B.padding ss))
      (Y R.terminal (side P ku) (CopyPadding.identifier B.padding st))
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
        (CopyPadding.identifier B.padding st))
      (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) j))
      (B.binPreparation bin r (F (j + 1))) := by
  have hc (i : ℕ) := B.complete_grid M r R.source R.terminal R.source_terminal
    ks ku ss st hs hu (B.binPreparation bin r (F (i + 1)))
    (dyadicSlack (Nat.log2 M + 1) i)
  simp_rw [hc] at hW
  have hm (l : List ℕ) (f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
      l.mapM (fun i => some (f i)) = some (l.map f) := List.mapM_pure
  rw [hm] at hW
  have he := Option.some.inj hW
  subst W
  simp [List.getElem?_map, List.getElem?_range hj]

/-- Stationarity for a successful preparation-list entry on its original usage slice. -/
theorem preparationWalks_mean (B : BudgetData HP P) (M bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (j : ℕ) (hj : j < Nat.log2 M + 1) (x y : ZMod P) :
    rowSliceMean (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st) (W[j]?.getD 0) x y =
    rowSliceMean (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (B.binPreparation bin r (F (j + 1))) x y := by
  rw [B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj]
  convert rowSliceMean_conditionalWalk
    (X R.source (side P ks) (CopyPadding.identifier B.padding ss))
    (Y R.terminal (side P ku) (CopyPadding.identifier B.padding st))
    (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
      (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
      (CopyPadding.identifier B.padding st))
    (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) j))
    (B.binPreparation bin r (F (j + 1))) x y using 1 <;> congr 8

/-- Actual preparation bias at an executed second prefix. Stationarity removes only
its usage walk; sensitivity still charges the completed full-rank first history. -/
theorem initialSecondSignal_clippedMean_le (B : BudgetData HP P) (M bin ka ku : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    {Lh Lρ : ℝ} (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) (x y : ZMod P) :
    actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
      B.padding ss st ka B.base ζ
      (firstSignalIncrement F ka
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j x y ≤
      secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ (F (j + 1)) B.base x y := by
  have hK := FourthRootHierarchyParams.NormalizedRow.rank_pos HP
  unfold actualClippedMean twoMaskMean
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, actualPrefix_twoSignal_second,
    Nat.add_sub_cancel]
  unfold rowSliceMean
  rw [← mul_expect]
  change min 1 |ζ * rowSliceMean _ _ (W[j]?.getD 0) x y - ζ * _| ≤ _
  have hmean := B.preparationWalks_mean M bin r R ks ku ss st hs hu F W hW j hj x y
  rw [hmean, ← mul_sub, abs_mul]
  apply min_le_min_left
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
  have hb := preparation_mean_bias_le HP hK R B.padding ss st ks ka ku hLρ hh hρ
    (F (j + 1)) B.base x y
  rw [B.binPreparation_eq_selected bin r R ka st ht haux]
  convert hb using 1; congr 8

/-- A successful literal preparation entry vanishes outside its actual usage mask. -/
theorem preparationPrefix_zero_off (B : BudgetData HP P) (M bin ka ku : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (hu : r.usage = gridChannel R.terminal ku st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1)
    (σ : Environment P 3) (x y : ZMod P)
    (hy : ¬retainedMask R.terminal (side P ku) B.padding st σ y) :
    actualPrefix (firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
      (fun _ _ _ _ => 0) j σ x y 1 = 0 := by
  rw [actualPrefix_twoSignal_second]
  simp only [Nat.add_sub_cancel]
  rw [B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj]
  have hzero := conditionalWalk_zero_off
    (X R.source (side P ks) (CopyPadding.identifier B.padding ss))
    (Y R.terminal (side P ku) (CopyPadding.identifier B.padding st))
    (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
      (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
      (CopyPadding.identifier B.padding st))
    (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) j))
    (B.binPreparation bin r (F (j + 1))) σ x y hy
  rw [hzero, mul_zero]

/-- The actual request truth is the genuine two-mask target on the original environment.
The rank gate uses terminal, while the preparatory mean uses usage. -/
theorem requestSignals_eq_genuineTarget (B : BudgetData HP P) (bin ka ku : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ) :
    requestSignals ζ B.padding id r (fun _ => G)
      (B.binPreparation bin r (fun _ => G)) =
      genuineTarget HP R.source R.terminal (side P ks) (side P ku)
        B.padding ss st ka G ζ := by
  have hr : Admissible r := by
    simp only [Admissible, hs, ht, hu, gridChannel]
    exact ⟨R.source_terminal, trivial, trivial⟩
  have hbp : B.binPreparation bin r (fun _ => G) =
      NormalizedMoments.genuinePrep HP r.terminal.role B.padding
        r.terminal.suffix ka G := by
    rw [B.binPreparation_eq_selected bin r R ka st ht haux]
    rw [ht]
    unfold selectedPreparation NormalizedMoments.genuinePrep
    funext τ a b
    simp only [DenseRowRecipe.preparation, gridChannel, retainedMask]
  rw [hbp]
  funext τ a b ν
  simp only [requestSignals, genuineTarget, id_eq]
  rw [request_genuineMean_eq HP B.padding r hr ks ku ka
    (by rw [hs]; rfl) (by rw [hu]; rfl)]
  simp only [hs, ht, hu, gridChannel, CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid, retainedMask]
  congr 8

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
  (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  (hF : B.initialPrefixes M r = some F) (j : ℕ) (hj : j < Nat.log2 M + 1)
include hM hbins hrate hcutoff haux hD hn hs ht hks hC hC1 hF hj

/-- Absolute history error, before preparation, paid in matrix units. The deterministic
term is the actual canonical deficit; the other term is unconditional correlated noise. -/
theorem initialPrefix_absolute_moment :
    let Xs := retainedMask R.source (side P ks) B.padding ss
    let Ya := retainedMask R.terminal (side P ka) B.padding st
    rowNormPow 4 P (rate ks) Xs Ya (fun σ x y => F (j + 1) σ x y - B.base x y) ≤
      8 * (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
        (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
        rowNormPow 4 P (rate ks) Xs Ya (fun _ => B.initialPolynomialLoss M n j r)) := by
  dsimp only
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  apply (rowNormPow_sub_le_centered hNu (F (j + 1))
    (rowSliceMean (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st) (F (j + 1))) B.base).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  apply add_le_add
  · have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
    have hh := B.initialPrefix_noise_dyadic M hM hne r R.source R.terminal R.source_terminal
      ks ka ss st hs ht F hF (j + 1) (by omega)
    simp only [hs, gridChannel, Nat.add_sub_cancel] at hh
    convert hh using 1 <;> congr 8
  · apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
    intro σ x y _ _
    have hm := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
      r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 F hF j hj x y
    change B.base x y - _ = B.initialPolynomialLoss M n j r x y at hm
    have hm' : B.base x y - rowSliceMean
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st) (F (j + 1)) x y =
        B.initialPolynomialLoss M n j r x y := by
      convert hm using 1; congr 8
    rw [one_mul, abs_sub_comm, hm']

/-- Conditional Jensen pays the second deterministic envelope on the original usage
slice, with full-rank sensitivity. No preparation-walk noise or final output error is
assumed. The explicit loss row norm remains an allocation obligation. -/
theorem initialSecondMeanEnvelope_moment (ku : ℕ) (husage : ka ≤ ku)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (ζ : ℝ) :
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (fun _ => secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ (F (j + 1)) B.base) ≤
      P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 * (8 *
        (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
          (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ => B.initialPolynomialLoss M n j r))) := by
  exact (secondMeanEnvelope_moment R B.padding ss st ks ka ku husage hLh hLρ ζ
    (F (j + 1)) B.base (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)).trans
    (mul_le_mul_of_nonneg_left (B.initialPrefix_absolute_moment M hM n hbins hrate hcutoff
      haux hD H hn r R ks ka ss st hs ht hks hC hC1 F hF j hj) (by positivity))

/-- Both deterministic envelopes for the real compressed-bin signal history. Only the
centered noise of each actual signal remains. The second noise is kept on usage, and
neither noise is discounted by heavy-event rarity. -/
theorem initial_requestSignals_two_envelopes (bin ku : ℕ)
    (hu : r.usage = gridChannel R.terminal ku st)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    {Lh Lρ : ℝ} (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (ζ : ℝ) (σ : Environment P 3) (x y : ZMod P) :
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let truth := requestSignals ζ B.padding id r (fun _ => B.base)
      (B.binPreparation bin r (fun _ => B.base))
    clippedError (truth σ x y 0) (truth σ x y 1)
      (uncompressedRow (Δ σ x) 0 (j + 1) y) ≤
      B.initialMeanCharge M n j ka r +
      (if retainedMask R.terminal (side P ku) B.padding st σ y then
        secondMeanEnvelope R B.padding ss st ks ka ku Lh Lρ ζ (F (j + 1)) B.base x y
        else 0) +
      actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base Δ 0 0 j σ x y +
      (if retainedMask R.terminal (side P ku) B.padding st σ y then
        actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka B.base Δ 0 1 j σ x y else 0) := by
  let Δ := firstSignalIncrement F ka
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  have hz := B.preparationPrefix_zero_off M bin ka ku r R ks ss st hs hu F W hW ζ j hj
  have he := actual_two_mask_clipped_split HP R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st ka B.base hC ζ (actualPrefix Δ (fun _ _ _ _ => 0) j)
    hz σ x y
  have hf := B.initialFirstSignal_clippedMean_le M hM n hbins hrate hcutoff haux hD H hn r
    R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1 F hF j hj
    (side P ku) ζ (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) x y
  have hp := B.initialSecondSignal_clippedMean_le M bin ka ku r R ks ss st hs ht hu
    (congrFun haux bin) F W hW hLρ hh hρ ζ j hj x y
  have htgt := B.requestSignals_eq_genuineTarget bin ka ku r R ks ss st hs ht hu
    (congrFun haux bin) B.base ζ
  dsimp only at he ⊢
  rw [htgt]
  apply he.trans
  unfold actualClippedMean at hf hp
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hf hp
  unfold actualNoiseEntry
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, div_one]
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact hf
      · split_ifs
        · exact hp
        · exact le_rfl
    · apply le_of_eq; congr 8
  · apply le_of_eq; congr 8

/-- The executed second deterministic statistic consumes the Jensen payment. This is
before payment of its centered usage walk noise, which remains separate. -/
theorem initialSecondSignal_mean_moment (bin ku : ℕ) (husage : ka ≤ ku)
    (hu : r.usage = gridChannel R.terminal ku st)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) (ζ : ℝ) :
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal
        (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base ζ
        (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j x y) ≤
      P * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 * (8 *
        (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
          (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
        rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ka) B.padding st)
          (fun _ => B.initialPolynomialLoss M n j r))) := by
  apply le_trans _ (B.initialSecondMeanEnvelope_moment M hM n hbins hrate hcutoff haux hD H
    hn r R ks ka ss st hs ht hks hC hC1 F hF j hj ku husage hLh hLρ ζ)
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have hb := B.initialSecondSignal_clippedMean_le M bin ka ku r R ks ss st hs ht hu
    (congrFun haux bin) F W hW hLρ hh hρ ζ j hj x y
  have hn0 : 0 ≤ actualClippedMean HP R.source R.terminal
      (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base ζ
      (firstSignalIncrement F ka
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
      (fun _ _ _ _ => 0) 1 j x y := by
    simp only [actualClippedMean, Fin.isValue, one_ne_zero, ↓reduceIte]
    exact le_min zero_le_one (abs_nonneg _)
  rw [one_mul, abs_of_nonneg hn0, abs_of_nonneg (hn0.trans hb)]
  exact pow_le_pow_left₀ hn0 hb 4

end Polynomial
end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
