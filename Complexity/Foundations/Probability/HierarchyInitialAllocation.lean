/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialPaid
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduledMeanTail

/-!
# Scheduled initial deficit payments

The full-rank deficit is bounded in matrix units by actual omitted coverage and inactive
bins. Sufficient budget removes inactive charges only at positive groups; group zero stays
explicit. These original finite bounds retain depth, rank, source and field dependencies.
They do not establish the general lower-budget induction or native RL=L.

## Main results

* `initialPolynomialLoss_moment`: full-rank fourth moment paid by the actual charges.
* `initialMeanCharge_le_schedule`: sufficient-budget envelope retaining group zero.
* `initialMeanCharge_tail_schedule`: the early inactive group keeps its exact weight.
* `exists_compressedBin_allocated`: actual output with deterministic rarity payments.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Full-rank fourth moment, preserving the original source and terminal masks. This
pays the literal deficit used by preparation Jensen, rather than a clipped substitute. -/
theorem initialPolynomialLoss_moment [Fact P.Prime] (B : BudgetData HP P) (M n j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hC : ∀ x y, 0 ≤ B.base x y)
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P)) :
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ => B.initialPolynomialLoss M n j r) ≤
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ _ _ => rate n + B.initialInactiveCharge M j r) := by
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
  intro σ x y _ _
  have hn := B.initialPolynomialLoss_nonneg M n j r hrate hC x y
  have hb := B.initialPolynomialLoss_le M n j r hrate hC x y
  rw [one_mul, abs_of_nonneg hn, abs_of_nonneg (hn.trans hb)]
  exact pow_le_pow_left₀ hn hb 4

/-- Sufficient budget leaves only the first inactive group. Its payment must retain its
schedule weight; replacing it by a uniform norm need not shrink as the budget grows. -/
theorem initialMeanCharge_le_schedule (B : BudgetData HP P) (M n j ka : ℕ)
    (hM : 1 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : ∀ bin, 0 ≤ B.binRate bin)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M) :
    B.initialMeanCharge M n j ka r ≤ rate n / rate ka +
      if j = 0 then (B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka else 0 := by
  by_cases hz : j = 0
  · subst j
    simp only [initialMeanCharge, ↓reduceIte, ← add_div]
    exact div_le_div_of_nonneg_right
      (add_le_add le_rfl (B.initialInactiveCharge_le M 0 r hrate)) (rate_pos ka).le
  · rw [initialMeanCharge, B.initialInactiveCharge_eq_zero_of_pos M j hM
        (by omega) r hc, add_zero, ite_eq_right hz, add_zero]

/-- In the finite deterministic tail the possible early inactive charge has exactly the
weight of group zero. The retained-depth term pays every later prefix separately. -/
theorem initialMeanCharge_tail_schedule (B : BudgetData HP P) (M n ka : ℕ)
    (hM : 1 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : ∀ bin, 0 ≤ B.binRate bin)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    (v : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) :
    let m := Nat.log2 M + 1
    (∑ j ∈ range m, v j * ∑ i ∈ Ico j m,
      (28 : ℝ) ^ (m - i) * B.initialMeanCharge M n i ka r) ≤
      rate n / rate ka * (∑ j ∈ range m, v j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i)) +
      v 0 * 28 ^ m * ((B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka) := by
  extract_lets m
  let a := rate n / rate ka
  let b := (B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka
  have hb (j : ℕ) :
      (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * (a + if i = 0 then b else 0)) =
        a * (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i)) +
          if j = 0 then 28 ^ m * b else 0 := by
    simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_Ico,
      Nat.le_zero, m, Nat.zero_lt_succ, and_true, Nat.sub_zero]
    rw [← sum_mul, mul_comm]
  calc
    _ ≤ ∑ j ∈ range m, v j * ∑ i ∈ Ico j m,
        (28 : ℝ) ^ (m - i) * (a + if i = 0 then b else 0) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hv j)
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (B.initialMeanCharge_le_schedule M n i ka hM r hrate hc) (by positivity)
    _ = _ := by
      simp_rw [hb]
      simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_range,
        m, Nat.zero_lt_succ, ↓reduceIte]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        ring
      · dsimp only [b]
        ring

/-- Actual successful-output bound with the full-rank deficit paid by omitted/inactive
charges and both deterministic mean tails paid by actual heavy rarity. The finite double
sum retains the early inactive group's weight. Rank must lie in the stated field horizon.
Noise is still unconditional; global reserve allocation and full induction remain open. -/
theorem exists_compressedBin_allocated (HP : FourthRootHierarchyParams 16 1 16 32 8)
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
      r.usage = gridChannel R.terminal ku st → ks ≤ H.maxExponent → ka ≤ H.maxExponent → ka ≤ ku →
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
      let q := fun i => B.initialMeanCharge M n i ka r
      let e₀ := (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
        (64 / 63) / rate ka
      let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
      let deficit := fun i => rowNormPow 4 P (rate ks) X Ya
        (fun _ _ _ => rate n + B.initialInactiveCharge M i r)
      let prep := fun i => (P : ℝ) * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
        (8 * ((e₀ * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 + deficit i))
      let a := fun i => (vertexNormPow 4 P (rate ks) X (fun _ _ => q i)) ^ (4⁻¹ : ℝ) +
        (prep i) ^ (4⁻¹ : ℝ)
      let rarity := fun j => ((2 + 256 / dyadicFloor floor m j) /
        (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)
      let tail := ∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
        ((rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i)) ^ (4⁻¹ : ℝ) +
          (prep i) ^ (4⁻¹ : ℝ))
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
          C ^ 4 * (tail +
            (e₀ + e₁) * (7 / 9)) ^ 4) +
        64 * ((∑ i ∈ range m, w i *
          (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) + prep i)) +
          (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) := by
  obtain ⟨C, hC, hfloor⟩ := exists_compressedBin_paid HP hζ hscl hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hfloor floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B M n hM hbins hrate hcutoff haux hD H hn r hr R ks ka ku ss st
    hs ht hu hks hka husage hbase hbase1 bin F hF W hW A hA Lh Lρ hLh hLρ hh hρ
  extract_lets m X Ya q e₀ e₁ deficit prep a rarity tail radius w c
  let Δ := firstSignalIncrement F ka
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  let μ := fun ν i x y => actualClippedMean HP R.source R.terminal (side P ks) (side P ka)
    (side P ku) B.padding ss st ka B.base ζ Δ 0 ν i x y
  let olddef := fun i => rowNormPow 4 P (rate ks) X Ya
    (fun _ => B.initialPolynomialLoss M n i r)
  let oldprep := fun i => (P : ℝ) * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 *
    (8 * ((e₀ * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 + olddef i))
  let olda := fun i => vertexNormPow 4 P (rate ks) X (fun _ _ => q i) ^ (4⁻¹ : ℝ) +
    oldprep i ^ (4⁻¹ : ℝ)
  let meanTail := fun ν σ x => ∑ j ∈ range m,
    if meanFirstEvent R.terminal B.padding st ka m j floor B.base
        (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
      meanRowTail R.terminal (side P (if ν = 0 then ka else ku)) B.padding st m j (μ ν) σ x
    else 0
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hd (i : ℕ) : olddef i ≤ deficit i :=
    B.initialPolynomialLoss_moment M n i r hrate hbase R ks ka ss st
  have hp (i : ℕ) : oldprep i ≤ prep i := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hd i)) (by norm_num)
  have hpn (i : ℕ) : 0 ≤ oldprep i := by
    have hd0 : 0 ≤ olddef i := rowNormPow_nonneg hNu _
    dsimp only [oldprep]
    positivity
  have ha (i : ℕ) : olda i ≤ a i := by
    exact add_le_add le_rfl (Real.rpow_le_rpow (hpn i) (hp i) (by norm_num : (0 : ℝ) ≤ 4⁻¹))
  have hfirst (i : ℕ) (hi : i < m) := B.initialFirstMean_moments M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hbase hbase1 F hF i hi ku ζ
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
  have hsecond (i : ℕ) (hi : i < m) : rowNormPow 4 P (rate ks) X
      (retainedMask R.terminal (side P ku) B.padding st) (fun _ => μ 1 i) ≤ prep i := by
    have hb := B.initialSecondSignal_mean_moment M hM n hbins hrate hcutoff haux hD H hn
      r R ks ka ss st hs ht hks hbase hbase1 F hF i hi bin ku husage hu W hW hLh hLρ hh hρ ζ
    apply le_trans _ (hp i)
    simpa only [μ, X, Ya, Δ, olddef, m, oldprep, e₀,
      div_mul_cancel₀ _ (rate_pos ka).ne', Pi.zero_def] using hb
  let e := fun (ν : Fin 2) i => if ν = 0 then
    rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) ^ (4⁻¹ : ℝ)
    else prep i ^ (4⁻¹ : ℝ)
  have hen (ν : Fin 2) (i : ℕ) : 0 ≤ e ν i := by
    dsimp only [e]
    split_ifs
    · exact Real.rpow_nonneg (rowNormPow_nonneg hNu _) _
    · exact Real.rpow_nonneg ((hpn i).trans (hp i)) _
  have hbudget (ν : Fin 2) (i : ℕ) (hi : i < m) :
      rowNormPow 4 P (rate ks) X
        (retainedMask R.terminal (side P (if ν = 0 then ka else ku)) B.padding st)
        (fun _ => μ ν i) ≤ e ν i ^ 4 := by
    by_cases hz : ν = 0
    · subst ν
      change rowNormPow 4 P (rate ks) X Ya (fun _ => μ 0 i) ≤
        (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) ^ (4⁻¹ : ℝ)) ^ 4
      rw [show (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) ^ (4⁻¹ : ℝ)) ^ 4 =
        rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) from
          Real.rpow_inv_natCast_pow (rowNormPow_nonneg hNu _) (by decide : (4 : ℕ) ≠ 0)]
      exact (hfirst i hi).2
    · have hv : ν = 1 := by omega
      subst ν
      change rowNormPow 4 P (rate ks) X
        (retainedMask R.terminal (side P ku) B.padding st) (fun _ => μ 1 i) ≤
          (prep i ^ (4⁻¹ : ℝ)) ^ 4
      rw [show (prep i ^ (4⁻¹ : ℝ)) ^ 4 = prep i from
        Real.rpow_inv_natCast_pow ((hpn i).trans (hp i)) (by decide : (4 : ℕ) ≠ 0)]
      exact hsecond i hi
  have hTailOne (ν : Fin 2) : vertexNormPow 4 P (rate ks) X (meanTail ν) ^ (4⁻¹ : ℝ) ≤
      ∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e ν i := by
    have hb := integrated_mean_tail_schedule R.source R.terminal
      (Ne.symm R.source_terminal) (side P ks) (side P (if ν = 0 then ka else ku))
      B.padding hD ss st H hka (side_le P _) B.base hbase hf hNu
      (fun x => by simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hbase1 x)
      m (compatibleCapacity HP.K m) (fun _ => HP.K)
      (fun j _ => by unfold compatibleCapacity; positivity) Δ 0 (μ ν) (e ν)
      (fun i _ => hen ν i) (hbudget ν)
    have hb' := Real.rpow_le_rpow (vertexNormPow_nonneg hNu _) hb (by positivity : (0 : ℝ) ≤ 4⁻¹)
    have hn : 0 ≤ ∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m,
        (28 : ℝ) ^ (m - i) * e ν i := by
      apply sum_nonneg
      intro j _
      exact mul_nonneg (Real.rpow_nonneg (by
        have hfl := (dyadicFloor_pos hf m j).le
        positivity) _) (sum_nonneg fun i _ => mul_nonneg (by positivity) (hen ν i))
    simp only [mul_one] at hb'
    change vertexNormPow 4 P (rate ks) X (meanTail ν) ^ (4⁻¹ : ℝ) ≤
      ((∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e ν i) ^ 4) ^ (4⁻¹ : ℝ) at hb'
    have hroot : ((∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m,
        (28 : ℝ) ^ (m - i) * e ν i) ^ 4) ^ (4⁻¹ : ℝ) =
        ∑ j ∈ range m, rarity j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e ν i := by
      convert Real.pow_rpow_inv_natCast hn (by decide : (4 : ℕ) ≠ 0) using 1
    rwa [hroot] at hb'
  have htail : vertexNormPow 4 P (rate ks) X
      (fun σ x => meanTail 0 σ x + meanTail 1 σ x) ^ (4⁻¹ : ℝ) ≤ tail := by
    apply (vertexNormPow_add_rpow_le (by decide : (4 : ℕ) ≠ 0) hNu _ _).trans
    apply (add_le_add (hTailOne 0) (hTailOne 1)).trans_eq
    dsimp only [tail, e]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, ← sum_add_distrib, ← mul_add]
  have hout := hbound B M n hM hbins hrate hcutoff haux hD H hn r hr R ks ka ku ss st
    hs ht hu hks husage hbase hbase1 bin F hF W hW A hA Lh Lρ hLh hLρ hh hρ
  change rootDistPow 4 P (rate ks) X Ya A _ ≤ _ at hout
  have htailEq : (fun σ x => ∑ j ∈ range m,
      if meanFirstEvent R.terminal B.padding st ka m j floor B.base
        (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
        meanRowTail R.terminal (side P ka) B.padding st m j (μ 0) σ x +
        meanRowTail R.terminal (side P ku) B.padding st m j (μ 1) σ x else 0) =
      (fun σ x => meanTail 0 σ x + meanTail 1 σ x) := by
    funext σ x
    dsimp only [meanTail]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    split_ifs <;> simp only [add_zero]
  change rootDistPow 4 P (rate ks) X Ya A _ ≤
    128 * (HP.K : ℝ) *
      (Cp ^ 4 * ((∑ i ∈ range m, dyadicFloor floor m i * olda i) + floor * (e₀ + e₁) / 511) ^ 4 +
      C ^ 4 * (olda (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 +
      C ^ 4 * (vertexNormPow 4 P (rate ks) X _ ^ (4⁻¹ : ℝ) + (e₀ + e₁) * (7 / 9)) ^ 4) +
      64 * ((∑ i ∈ range m, w i *
        (rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => q i) + oldprep i)) +
        (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63)) at hout
  rw [htailEq] at hout
  have hra := (rate_pos ka).le
  have he0 : 0 ≤ e₀ := by dsimp only [e₀]; positivity
  have he1 : 0 ≤ e₁ := by dsimp only [e₁]; positivity
  have ho (i : ℕ) : 0 ≤ olda i := add_nonneg
    (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _) (Real.rpow_nonneg (hpn i) _)
  have hs0 : 0 ≤ ∑ i ∈ range m, dyadicFloor floor m i * olda i :=
    sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf.le m i) (ho i)
  have hv0 := Real.rpow_nonneg
    (vertexNormPow_nonneg (s := 4) (X := X) hNu
      (fun σ x => meanTail 0 σ x + meanTail 1 σ x)) (4⁻¹ : ℝ)
  apply hout.trans
  gcongr
  all_goals first
  | exact ha _
  | exact hp _
  | exact dyadicFloor_nonneg hf.le _ _
  | exact add_nonneg (ho _) (div_nonneg (add_nonneg he0 he1) (by norm_num))

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
