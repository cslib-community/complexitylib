/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialAllocation
public import Complexity.Foundations.Probability.HierarchyInitialFeasibility
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduleAllocation

/-!
# Geometric payments for the actual initial charges

The actual omitted/inactive charge has a constant retained-depth part and a single possible
inactive first group. Both its deterministic rarity tail and its raw false-charge sum have
horizon-independent coefficients. This is a finite allocation step, not arbitrary requested
accuracy or the general lower-budget induction.

## Main definitions

* `initialGeometricRHS`: complete computed successful-output payment.

## Main results

* `initialMeanCharge_geometric`: actual charge sums with the first group isolated.
* `initialAllocation_sums_le`: both means and preparation in the literal output sums.
* `exists_compressedBin_geometric`: successful actual output with those sums paid.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The charge used by the successful actual-output theorem receives explicit geometric
rarity and false-charge payments. No output accuracy is assumed and noise is not restricted
to a rare event. The first-group coefficients remain the literal capacity/floor values. -/
theorem initialMeanCharge_geometric (B : BudgetData HP P) (M n ka : ℕ)
    (hM : 1 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : ∀ bin, 0 ≤ B.binRate bin)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    {η : ℝ} (hη : 0 < η) (R : ℝ) :
    let m := Nat.log2 M + 1
    let a := rate n / rate ka
    let b := (B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka
    let v := fun j => ((2 + 256 / dyadicFloor η m j) /
      (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)
    let w := fun j => 64 * (HP.K : ℝ) * R ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor η m j ^ 4)
    (∑ j ∈ range m, v j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
      B.initialMeanCharge M n i ka r) ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * a / 63 + v 0 * 28 ^ m * b ∧
    (∑ i ∈ range m, w i * B.initialMeanCharge M n i ka r ^ 4) ≤
      (64 * (HP.K : ℝ) * R ^ 4 / η ^ 4) * a ^ 4 / 63 + w 0 * (a + b) ^ 4 := by
  extract_lets m a b v w
  have ha : 0 ≤ a := div_nonneg (rate_pos n).le (rate_pos ka).le
  have hb : 0 ≤ b := div_nonneg
    (mul_nonneg B.binCap_nonneg (sum_nonneg fun i _ => hrate i)) (rate_pos ka).le
  have hq (i : ℕ) : 0 ≤ B.initialMeanCharge M n i ka r := by
    unfold initialMeanCharge initialInactiveCharge
    exact div_nonneg (add_nonneg (rate_pos n).le
      (mul_nonneg B.binCap_nonneg (sum_nonneg fun j _ => by
        split_ifs
        · exact hrate j
        · exact le_rfl)))
      (rate_pos ka).le
  have he (i : ℕ) : B.initialMeanCharge M n i ka r ≤ a + if i = 0 then b else 0 :=
    B.initialMeanCharge_le_schedule M n i ka hM r hrate hc
  constructor
  · exact compatible_mean_tail_le hη ha HP.K m (by dsimp only [m]; omega)
      (fun i => B.initialMeanCharge M n i ka r) (fun i _ => he i)
  · apply compatible_false_charge_le hη (pow_nonneg ha 4) HP.K m
      ((a + b) ^ 4) (by dsimp only [m]; omega)
      (fun i => B.initialMeanCharge M n i ka r ^ 4)
    intro i _
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceIte] at he ⊢
      exact (pow_le_pow_left₀ (hq 0) (he 0) 4).trans
        (le_add_of_nonneg_left (pow_nonneg ha 4))
    · have hei := he i
      simp only [hi, ↓reduceIte, add_zero] at hei ⊢
      exact pow_le_pow_left₀ (hq i) hei 4

/-- Both literal sums in `exists_compressedBin_allocated`, including preparation, paid
without a horizon factor. The two computed late envelopes retain the width, rank and source
normalizations of the actual row moments. The exceptional first envelope has its own exact
weight. This does not assert those width-dependent envelopes meet a requested accuracy. -/
theorem initialAllocation_sums_le [Fact P.Prime] (B : BudgetData HP P) (M n ka ks : ℕ)
    (hM : 1 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : ∀ bin, 0 ≤ B.binRate bin)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    (R : RoleProfile 3) (ss st : List (ZMod P))
    {η : ℝ} (hη : 0 < η) (ζ L radius : ℝ) :
    let m := Nat.log2 M + 1
    let X := retainedMask R.source (side P ks) B.padding ss
    let Y := retainedMask R.terminal (side P ka) B.padding st
    let row := fun t => rowNormPow 4 P (rate ks) X Y (fun _ _ _ => t)
    let q := fun i => B.initialMeanCharge M n i ka r
    let inactive := B.binCap * ∑ bin ∈ B.bins, B.binRate bin
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal }) *
      (64 / 63) / rate ka
    let sensitivity := (P : ℝ) * (|ζ| * L / rate ka) ^ 4 * 8
    let prep := fun i => sensitivity *
      ((e₀ * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 +
        row (rate n + B.initialInactiveCharge M i r))
    let latePrep := sensitivity * ((e₀ * rate ka / 64) ^ 4 + row (rate n))
    let earlyPrep := sensitivity * ((e₀ * rate ka / 64) ^ 4 + row (rate n + inactive))
    let lateRow := row (rate n / rate ka)
    let earlyRow := row ((rate n + inactive) / rate ka)
    let lateRoot := lateRow ^ (4⁻¹ : ℝ) + latePrep ^ (4⁻¹ : ℝ)
    let earlyRoot := earlyRow ^ (4⁻¹ : ℝ) + earlyPrep ^ (4⁻¹ : ℝ)
    let v := fun j => ((2 + 256 / dyadicFloor η m j) /
      (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)
    let w := fun i => 64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor η m i ^ 4)
    (∑ j ∈ range m, v j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
      (row (q i) ^ (4⁻¹ : ℝ) + prep i ^ (4⁻¹ : ℝ))) ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * lateRoot / 63 + v 0 * 28 ^ m * earlyRoot ∧
    (∑ i ∈ range m, w i * (row (q i) + prep i)) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / η ^ 4) * (lateRow + latePrep) / 63 +
        w 0 * (earlyRow + earlyPrep) := by
  extract_lets m X Y row q inactive e₀ sensitivity prep latePrep earlyPrep
    lateRow earlyRow lateRoot earlyRoot v w
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have hrow (t : ℝ) : 0 ≤ row t := rowNormPow_nonneg hNu _
  have hmono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : row a ≤ row b := by
    apply (rowNormPow_le_mul hNu (c := 1) ?_).trans_eq (one_mul _)
    intro σ x y _ _
    rw [one_mul, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
    exact pow_le_pow_left₀ ha hab 4
  have hinactive : 0 ≤ inactive :=
    mul_nonneg B.binCap_nonneg (sum_nonneg fun i _ => hrate i)
  have hsn : 0 ≤ sensitivity := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg P) (by positivity : 0 ≤ (|ζ| * L / rate ka) ^ 4)) (by norm_num)
  have he0 : 0 ≤ e₀ := div_nonneg (by positivity) (rate_pos ka).le
  have hpn (i : ℕ) : 0 ≤ prep i := mul_nonneg hsn (add_nonneg (by positivity) (hrow _))
  have hlate : 0 ≤ latePrep := mul_nonneg hsn (add_nonneg (by positivity) (hrow _))
  have hearly : 0 ≤ earlyPrep := mul_nonneg hsn (add_nonneg (by positivity) (hrow _))
  have hnoise (i : ℕ) :
      (e₀ * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 ≤
        (e₀ * rate ka / 64) ^ 4 := by
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg he0 (rate_pos ka).le)
      (pow_nonneg (by norm_num) _))
    have hd := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by norm_num : (1 / 64 : ℝ) ≤ 1) (dyadicSlack_pos m i)
    simp only [pow_one] at hd
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hd
      (mul_nonneg he0 (rate_pos ka).le)
  have hcharge (i : ℕ) : 0 ≤ B.initialInactiveCharge M i r := by
    unfold initialInactiveCharge
    apply mul_nonneg B.binCap_nonneg
    apply sum_nonneg
    intro bin _
    split_ifs
    · exact hrate bin
    · exact le_rfl
  have hq0 (i : ℕ) : 0 ≤ q i :=
    div_nonneg (add_nonneg (rate_pos n).le (hcharge i)) (rate_pos ka).le
  have hbound (i : ℕ) : row (q i) ≤ earlyRow ∧ prep i ≤ earlyPrep := by
    have hi := B.initialInactiveCharge_le M i r hrate
    constructor
    · apply hmono (hq0 i)
      exact div_le_div_of_nonneg_right (add_le_add le_rfl hi) (rate_pos ka).le
    · apply mul_le_mul_of_nonneg_left _ hsn
      exact add_le_add (hnoise i) (hmono
        (add_nonneg (rate_pos n).le (hcharge i)) (add_le_add le_rfl hi))
  have hpos (i : ℕ) (hi : i ≠ 0) : row (q i) = lateRow ∧ prep i ≤ latePrep := by
    have hz := B.initialInactiveCharge_eq_zero_of_pos M i hM (by omega) r hc
    constructor
    · simp only [q, initialMeanCharge, hz, add_zero, lateRow]
    · dsimp only [prep, latePrep]
      rw [hz, add_zero]
      exact mul_le_mul_of_nonneg_left (add_le_add (hnoise i) le_rfl) hsn
  have hroot (i : ℕ) : row (q i) ^ (4⁻¹ : ℝ) + prep i ^ (4⁻¹ : ℝ) ≤
      lateRoot + if i = 0 then earlyRoot else 0 := by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      apply le_trans _ (le_add_of_nonneg_left
        (add_nonneg (Real.rpow_nonneg (hrow _) _) (Real.rpow_nonneg hlate _)))
      exact add_le_add
        (Real.rpow_le_rpow (hrow _) (hbound 0).1 (by norm_num))
        (Real.rpow_le_rpow (hpn 0) (hbound 0).2 (by norm_num))
    · simp only [hi, ↓reduceIte, add_zero, (hpos i hi).1]
      exact add_le_add le_rfl (Real.rpow_le_rpow (hpn i) (hpos i hi).2 (by norm_num))
  have hraw (i : ℕ) : row (q i) + prep i ≤
      (lateRow + latePrep) + if i = 0 then earlyRow + earlyPrep else 0 := by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      exact (add_le_add (hbound 0).1 (hbound 0).2).trans
        (le_add_of_nonneg_left (add_nonneg (hrow _) hlate))
    · simp only [hi, ↓reduceIte, add_zero, (hpos i hi).1]
      exact add_le_add le_rfl (hpos i hi).2
  exact ⟨compatible_mean_tail_le hη
      (add_nonneg (Real.rpow_nonneg (hrow _) _) (Real.rpow_nonneg hlate _)) HP.K m
      (by dsimp only [m]; omega) _ (fun i _ => hroot i),
    compatible_false_charge_le hη (add_nonneg (hrow _) hlate) HP.K m _
      (by dsimp only [m]; omega) _ (fun i _ => hraw i)⟩

/-- The complete computed right-hand side of the successful geometric output bound.
It retains stationary, final, tail and raw false-charge payments and both noises. -/
@[expose] def initialGeometricRHS [Fact P.Prime] (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (R : RoleProfile 3) (ks ka : ℕ) (ss st : List (ZMod P))
    (ζ floor Lh Lρ C Cpre : ℝ) : ℝ :=
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
  let row := fun t => rowNormPow 4 P (rate ks) X Ya (fun _ _ _ => t)
  let inactive := B.binCap * ∑ bin ∈ B.bins, B.binRate bin
  let sensitivity := (P : ℝ) * (|ζ| * (Lh + Lρ) / rate ka) ^ 4 * 8
  let latePrep := sensitivity * ((e₀ * rate ka / 64) ^ 4 + row (rate n))
  let earlyPrep := sensitivity * ((e₀ * rate ka / 64) ^ 4 + row (rate n + inactive))
  let lateRow := row (rate n / rate ka)
  let earlyRow := row ((rate n + inactive) / rate ka)
  let rarity₀ := ((2 + 256 / dyadicFloor floor m 0) /
    (compatibleCapacity HP.K m 0 : ℝ)) ^ (4⁻¹ : ℝ)
  let tail := (2 + 256 / floor) ^ (4⁻¹ : ℝ) *
    (lateRow ^ (4⁻¹ : ℝ) + latePrep ^ (4⁻¹ : ℝ)) / 63 +
    rarity₀ * 28 ^ m * (earlyRow ^ (4⁻¹ : ℝ) + earlyPrep ^ (4⁻¹ : ℝ))
  let radius := (2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ)
  let w := fun i => 64 * (HP.K : ℝ) * radius ^ 4 /
    ((compatibleCapacity HP.K m i : ℝ) * dyadicFloor floor m i ^ 4)
  let c := 64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4
  128 * (HP.K : ℝ) *
    (Cpre ^ 4 * ((∑ i ∈ range m, dyadicFloor floor m i * a i) +
      floor * (e₀ + e₁) / 511) ^ 4 +
    C ^ 4 * (a (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 +
    C ^ 4 * (tail +
      (e₀ + e₁) * (7 / 9)) ^ 4) +
  64 * (c * (lateRow + latePrep) / 63 + w 0 * (earlyRow + earlyPrep) +
    (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63))

/-- Successful actual output with both deterministic tails and both raw mean charges
paid by geometric sums. Width-dependent late envelopes and the exact exceptional first-group
weights remain explicit. Both centered noises keep their unconditional payments. -/
theorem exists_compressedBin_geometric (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hscl : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max (1 : ℝ) 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (M n : ℕ), 1 < M → B.bins = range (n + 1) → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      B.auxiliary = (fun _ => polynomialPrepCutoff4 HP.θ) → B.padding ≠ 0 →
      ∀ (H : Horizon P), n ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), Admissible r →
      ∀ (R : RoleProfile 3) (ks ka ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      r.usage = gridChannel R.terminal ku st → ks ≤ H.maxExponent → ka ≤ H.maxExponent → ka ≤ ku →
      B.slack * (1 + 4 * (n + ka)) < M →
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      ∀ (bin : ℕ) F, B.initialPrefixes M r = some F → ∀ W,
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.complete M r (B.binPreparation bin r (F (i + 1)))
          (dyadicSlack (Nat.log2 M + 1) i)) = some W →
      ∀ A, B.compressedBin M bin ka ζ floor r = some A →
      ∀ Lh Lρ : ℝ, 0 ≤ Lh → 0 ≤ Lρ →
      (∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|) →
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) →
      rootDistPow 4 P (rate ks)
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st) A
        (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K B.base) ≤
        B.initialGeometricRHS M n r R ks ka ss st ζ floor Lh Lρ C Cpre := by
  obtain ⟨C, hC, hfloor⟩ := exists_compressedBin_allocated HP hζ hscl hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, hbound⟩ := hfloor floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro P _ B M n hM hbins hrate hcutoff haux hD H hn r hr R ks ka ku ss st
    hs ht hu hks hka husage hbudget hbase hbase1 bin F hF W hW A hA Lh Lρ hLh hLρ hh hρ
  have hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M := by
    intro bin hi
    have hb : bin ≤ n := by rw [hbins, mem_range] at hi; omega
    exact B.retained_scaleCutoff_lt { r with usage := r.terminal } M n ka hrate
      (by simp only [ht, gridChannel]) hbudget bin hb
  have hsum := B.initialAllocation_sums_le M n ka ks hM r
    (by intro bin; rw [hrate]; exact (rate_pos bin).le) hc R ss st hf ζ (Lh + Lρ)
    ((2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ))
  have hout := hbound B M n (by omega) hbins hrate hcutoff haux hD H hn r hr R ks ka ku
    ss st hs ht hu hks hka husage hbase hbase1 bin F hF W hW A hA Lh Lρ hLh hLρ hh hρ
  unfold initialGeometricRHS
  extract_lets m X Ya q e₀ e₁ deficit prep a row inactive sensitivity latePrep earlyPrep
    lateRow earlyRow rarity₀ tail radius w c
  have hsums :
      (∑ j ∈ range m, (((2 + 256 / dyadicFloor floor m j) /
        (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)) *
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
          (row (q i) ^ (4⁻¹ : ℝ) + prep i ^ (4⁻¹ : ℝ))) ≤ tail ∧
      (∑ i ∈ range m, w i * (row (q i) + prep i)) ≤
        c * (lateRow + latePrep) / 63 + w 0 * (earlyRow + earlyPrep) := by
    simpa only [m, X, Ya, row, q, prep, deficit, e₀, sensitivity, latePrep, earlyPrep,
      lateRow, earlyRow, inactive, tail, rarity₀, w, c, radius, mul_assoc] using hsum
  have hNu := mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le
  have he0 : 0 ≤ e₀ := div_nonneg (by positivity) (rate_pos ka).le
  have he1 : 0 ≤ e₁ := by dsimp only [e₁]; positivity
  have hpn (i : ℕ) : 0 ≤ prep i := by
    have hd : 0 ≤ deficit i := rowNormPow_nonneg hNu _
    dsimp only [prep]
    positivity
  have htail : 0 ≤ ∑ j ∈ range m,
      (((2 + 256 / dyadicFloor floor m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
          (row (q i) ^ (4⁻¹ : ℝ) + prep i ^ (4⁻¹ : ℝ)) := by
    apply sum_nonneg
    intro j _
    apply mul_nonneg (Real.rpow_nonneg (by
      have hd := (dyadicFloor_pos hf m j).le
      positivity) _)
    exact sum_nonneg fun i _ => mul_nonneg (by positivity)
      (add_nonneg (Real.rpow_nonneg (rowNormPow_nonneg hNu _) _)
        (Real.rpow_nonneg (hpn i) _))
  apply hout.trans
  change _ ≤ 128 * (HP.K : ℝ) *
    (Cp ^ 4 * ((∑ i ∈ range m, dyadicFloor floor m i * a i) +
      floor * (e₀ + e₁) / 511) ^ 4 +
    C ^ 4 * (a (Nat.log2 M) + (e₀ + e₁) / 64) ^ 4 +
    C ^ 4 * (tail + (e₀ + e₁) * (7 / 9)) ^ 4) +
    64 * (c * (lateRow + latePrep) / 63 + w 0 * (earlyRow + earlyPrep) +
      (c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63))
  gcongr
  · exact hsums.1
  · exact hsums.2

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
