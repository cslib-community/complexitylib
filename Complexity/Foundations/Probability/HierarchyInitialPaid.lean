/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialIntegrated

/-!
# A finite paid bound for actual initial compressed outputs

The actual successful output is compared with its genuine dense polynomial bin.
First means use the canonical initial charge; second means use preparation Jensen on
usage, retaining the full-rank deficit moment. Both centered noises are unconditional.
Only the selected deterministic heavy-tail norm remains for a subsequent rarity payment.
These original finite assembly results do not allocate global reserves or prove induction.

## Main results

* `initialFirstMean_moments`: canonical charge pays the first maximum and raw row moment.
* `exists_compressedBin_paid`: one output inequality with all finite payments substituted.
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

section Polynomial
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (n : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss)
  (ht : r.terminal = gridChannel R.terminal ka st) (hks : ks ≤ H.maxExponent)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
  (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  (hF : B.initialPrefixes M r = some F) (j : ℕ) (hj : j < Nat.log2 M + 1)

include hM hbins hrate hcutoff haux hD hn hs ht hks hC hC1 hF hj

/-- The canonical charge pays both the first row maximum and its raw row moment.
No first-mean moment or output accuracy is supplied by the caller. -/
theorem initialFirstMean_moments (ku : ℕ) (ζ : ℝ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    let X := retainedMask R.source (side P ks) B.padding ss
    let Y := retainedMask R.terminal (side P ka) B.padding st
    let Δ := firstSignalIncrement F ka second
    let q := B.initialMeanCharge M n j ka r
    vertexNormPow 4 P (rate ks) X
      (actualMeanMax HP R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka B.base ζ Δ 0 0 j) ≤
      vertexNormPow 4 P (rate ks) X (fun _ _ => q) ∧
    rowNormPow 4 P (rate ks) X Y
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ Δ 0 0 j x y) ≤
      rowNormPow 4 P (rate ks) X Y (fun _ _ _ => q) := by
  extract_lets X Y Δ q
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have he (x y : ZMod P) := B.initialFirstSignal_clippedMean_le M hM n hbins hrate hcutoff
    haux hD H hn r R.source R.terminal R.source_terminal ks ka ss st hs ht hks hC hC1
    F hF j hj (side P ku) ζ second x y
  have hnon (x y : ZMod P) : 0 ≤ actualClippedMean HP R.source R.terminal
      (side P ks) (side P ka) (side P ku) B.padding ss st ka B.base ζ Δ 0 0 j x y := by
    simp only [actualClippedMean, Fin.isValue, ↓reduceIte]
    exact le_min zero_le_one (div_nonneg (abs_nonneg _)
      (by linarith [div_nonneg (hC x y) (rate_pos ka).le]))
  have hq : 0 ≤ q := (hnon 0 0).trans (he 0 0)
  constructor
  · apply vertex_mono_nonneg X hNu _ _ (fun _ _ => kthLargest_nonneg)
    intro σ x
    apply kthLargest_le hq
    intro y _
    rw [abs_of_nonneg (hnon x y)]
    exact he x y
  · apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
    intro σ x y _ _
    rw [one_mul, abs_of_nonneg (hnon x y), abs_of_nonneg hq]
    exact pow_le_pow_left₀ (hnon x y) (he x y) 4

end Polynomial

/-- A single finite bound for the successful actual compressed output. Stationary,
final, raw false-charge and both noise payments are substituted. The selected mean-tail
norm is explicit and receives no rarity gain here. Global allocation is still open.
The decoder constant precedes the positive floor, and its stationary coefficient follows it. -/
theorem exists_compressedBin_paid (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hscl : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max (1 : ℝ) 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (M n : ℕ), 0 < M → B.bins = range (n + 1) → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      B.auxiliary = (fun _ => polynomialPrepCutoff4 HP.θ) → B.padding ≠ 0 →
      ∀ (H : Horizon P), n ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), Admissible r →
      ∀ (R : RoleProfile 3) (ks ka ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      r.usage = gridChannel R.terminal ku st → ks ≤ H.maxExponent → ka ≤ ku →
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      ∀ (bin : ℕ) F, B.initialPrefixes M r = some F → ∀ W,
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.complete M r (B.binPreparation bin r (F (i + 1)))
          (dyadicSlack (Nat.log2 M + 1) i)) = some W →
      ∀ A, B.compressedBin M bin ka ζ floor r = some A →
      ∀ Lh Lρ : ℝ, 0 ≤ Lh → 0 ≤ Lρ →
      (∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|) →
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) →
      let m := Nat.log2 M + 1
      let X := retainedMask R.source (side P ks) B.padding ss
      let Ya := retainedMask R.terminal (side P ka) B.padding st
      let Δ := firstSignalIncrement F ka
        (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
      let q := fun i => B.initialMeanCharge M n i ka r
      let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
        (64 / 63) / rate ka
      let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
      let deficit := fun i => rowNormPow 4 P (rate ks) X Ya
        (fun _ => B.initialPolynomialLoss M n i r)
      let prep := fun i => (P : ℝ) * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
        (8 * ((e₀ * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 + deficit i))
      let a := fun i => (vertexNormPow 4 P (rate ks) X (fun _ _ => q i)) ^ (4⁻¹ : ℝ) +
        (prep i) ^ (4⁻¹ : ℝ)
      let meanTail := fun σ x => ∑ j ∈ range m,
        if meanFirstEvent R.terminal B.padding st ka m j floor B.base
            (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail R.terminal (side P ka) B.padding st m j
            (actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base ζ Δ 0 0) σ x +
          meanRowTail R.terminal (side P ku) B.padding st m j
            (actualClippedMean HP R.source R.terminal (side P ks) (side P ka) (side P ku)
              B.padding ss st ka B.base ζ Δ 0 1) σ x
        else 0
      let radius := (2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ)
      let w := fun i => 64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor floor m i ^ 4)
      let c := 64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4
      rootDistPow 4 P (rate ks) X Ya A
        (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K B.base) ≤
        128 * (HP.K : ℝ) *
          (Cpre ^ 4 * ((∑ i ∈ range m, dyadicFloor floor m i * a i) +
            floor * (e₀ + e₁) / 511) ^ 4 +
          C ^ 4 * (a (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 +
          C ^ 4 * (vertexNormPow 4 P (rate ks) X meanTail ^ (4⁻¹ : ℝ) +
            (e₀ + e₁) * (7 / 9)) ^ 4) +
        64 * ((∑ i ∈ range m, w i *
          (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) + prep i)) +
          (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
  obtain ⟨C, hC, hfloor⟩ := exists_compressedBin_fourMax HP
    (by norm_num : (0 : ℝ) ≤ 1) hζ hscl hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hfloor floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B M n hM hbins hrate hcutoff haux hD H hn r hr R ks ka ku ss st
    hs ht hu hks husage hbase hbase1 bin F hF W hW A hA Lh Lρ hLh hLρ hh hρ
  extract_lets m X Ya Δ q e₀ e₁ deficit prep a meanTail radius w c
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have haux' (d : ℝ) : B.auxiliary bin d ∈ Set.Icc 0 1 := by
    rw [haux]; exact ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩
  have hsr : r.source.rate = rate ks := by rw [hs]; rfl
  have htr : r.terminal.rate = rate ka := by rw [ht]; rfl
  have hY : (fun σ y => r.terminal.retains (channels B.padding) σ y) = Ya := by
    simp only [ht, Ya, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid]
    rfl
  have hX : (fun σ x => r.source.retains (channels B.padding) σ x) = X := by
    simp only [hs, X, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid]
    rfl
  let μ := fun i ν => actualMeanMax HP R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st ka B.base ζ Δ 0 ν i
  let ε := actualFourMax HP R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st ka B.base ζ Δ 0
  let olda := fun i ν => vertexNormPow 4 P (rate ks) X (μ i ν) ^ (4⁻¹ : ℝ)
  have hfirst (i : ℕ) (hi : i < m) := B.initialFirstMean_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hbase hbase1 F hF i hi ku ζ
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  have hprep (i : ℕ) (hi : i < m) : rowNormPow 4 P (rate ks) X
      (retainedMask R.terminal (side P ku) B.padding st)
      (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
        (side P ku) B.padding ss st ka B.base ζ Δ 0 1 i x y) ≤ prep i := by
    have hb := B.initialSecondSignal_mean_moment M hM n hbins hrate hcutoff haux hD H hn
      r R ks ka ss st hs ht hks hbase hbase1 F hF i hi bin ku husage hu W hW hLh hLρ hh hρ ζ
    simpa only [X, Ya, Δ, deficit, m, prep, e₀,
      div_mul_cancel₀ _ (rate_pos ka).ne', Pi.zero_def] using hb
  have hmeans (i : ℕ) (hi : i < m) : olda i 0 + olda i 1 ≤ a i := by
    apply add_le_add
    · exact Real.rpow_le_rpow (vertexNormPow_nonneg hNu _) (hfirst i hi).1 (by positivity)
    · apply Real.rpow_le_rpow (vertexNormPow_nonneg hNu _) _ (by positivity)
      exact (vertex_row_max X (retainedMask R.terminal (side P ku) B.padding st) hNu
        (fun _ x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
          (side P ku) B.padding ss st ka B.base ζ Δ 0 1 i x y)).trans (hprep i hi)
  have ha (i : ℕ) : 0 ≤ olda i 0 + olda i 1 :=
    add_nonneg (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _)
      (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _)
  have hra := rate_pos ka
  have he : 0 ≤ e₀ + e₁ := by dsimp only [e₀, e₁]; positivity
  have hp := B.initialFourMax_preloss M bin ka hM hne haux' r R ks ku ss st
    hs ht hu F hF W hW B.base hbase ζ hf
  rw [hsr] at hp
  have hpaidPre : vertexNormPow 4 P (rate ks) X
      (fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * ε i σ x) ≤
      ((∑ i ∈ range m, dyadicFloor floor m i * a i) + floor * (e₀ + e₁) / 511) ^ 4 := by
    apply hp.trans
    apply pow_le_pow_left₀ (add_nonneg (sum_nonneg fun i _ =>
      mul_nonneg (dyadicFloor_nonneg hf.le m i) (ha i)) (by positivity)) _ 4
    apply add_le_add _ le_rfl
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (hmeans i (mem_range.mp hi)) (dyadicFloor_nonneg hf.le m i)
  have hfinal := B.initialFourMax_moment M bin ka hM hne haux' r R ks ku ss st
    hs ht hu F hF W hW B.base hbase ζ (Nat.log2 M) (by omega)
  rw [hsr] at hfinal
  have hpaidFinal : vertexNormPow 4 P (rate ks) X (ε (Nat.log2 M)) ≤
      (a (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 := by
    apply hfinal.trans
    simp only [dyadicSlack_last, pow_one]
    apply pow_le_pow_left₀ (add_nonneg (ha _) (by positivity)) _ 4
    convert add_le_add_right (hmeans (Nat.log2 M) (by omega)) ((e₀ + e₁) / 64) using 1 <;> ring
  have htail := B.initialFourMax_tail M bin ka hM hne haux' r R ks ku ss st
    hs ht hu F hF W hW B.base hbase ζ floor
  rw [hsr] at htail
  have hside : side P ku ≤ side P ka := by
    rw [side_eq_ceil, side_eq_ceil]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) husage)) (by positivity))
  have hfalse := B.initialSignals_falseBudget M bin ka hM hne haux' r R ks ku ss st
    hs ht hu F hF W hW B.base hbase ζ hside hf radius
  rw [hsr] at hfalse
  have hpaidFalse : (∑ i ∈ range m, w i * rowNormPow 4 P (rate ks) X Ya
      (fun σ x y => clippedError (B.base x y / rate ka)
        (genuineTarget HP R.source R.terminal (side P ks) (side P ku)
          B.padding ss st ka B.base ζ σ x y 1) (actualPrefix Δ 0 i σ x y))) ≤
      64 * ((∑ i ∈ range m, w i *
        (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) + prep i)) +
        (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
    apply hfalse.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 64)
    apply add_le_add _ le_rfl
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (add_le_add (hfirst i (mem_range.mp hi)).2 (hprep i (mem_range.mp hi)))
      (by dsimp only [w]; positivity)
  have hout := hbound B rate rate_pos (fun i => by
    simp only [rate, pow_succ, _root_.mul_inv_rev]; ring) M bin ka r hr htr
    (congrFun hcutoff bin) (congrFun haux bin) B.base hbase F hF W hW A hA
    R ks ku ss st hs ht hu
  dsimp only at hout
  simp only [hsr, hX, hY] at hout
  have htgt := B.requestSignals_eq_genuineTarget bin ka ku r R ks ss st hs ht hu
    (congrFun haux bin) B.base ζ
  rw [htgt] at hout
  simp only [genuineTarget, Fin.isValue, ↓reduceIte] at hout
  have hno : vertexNormPow 4 P (rate ks) X (fun σ x =>
      if ∀ i < m, stepThreshold {y | Ya σ y} (compatibleCapacity HP.K m)
        (fun _ => HP.K) (dyadicFloor floor m) (Δ σ x) ⟨0, 0⟩ i ≤ dyadicFloor floor m i
      then ε (Nat.log2 M) σ x else 0) ≤
      (a (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 := by
    apply (vertex_mono_nonneg X hNu _ _ ?_ ?_).trans hpaidFinal
    · intro σ x
      split_ifs <;> first
      | exact actualFourMax_nonneg HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | exact le_rfl
    · intro σ x
      split_ifs <;> first
      | exact le_rfl
      | exact actualFourMax_nonneg HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  apply hout.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · exact add_le_add (mul_le_mul_of_nonneg_left hpaidPre (by positivity))
        (mul_le_mul_of_nonneg_left hno (by positivity))
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert htail using 1
      simp only [X, Ya, meanFirstEvent]
      congr 3
      funext σ x
      apply sum_congr rfl
      intro j _
      split_ifs <;> rfl
  · convert hpaidFalse using 1; rfl

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
