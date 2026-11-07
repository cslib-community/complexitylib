/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialPreparation

/-!
# Noise payments for executed preparation walks

Each literal preparation input has range [0,1], so the existing derived magnitude and
scheduled completion allocation pay its centered usage-walk noise. The walk stays on the
original source × usage environment; the full-terminal first history is not reseeded.
These original bounds pay only second noise, unconditionally even at heavy overflow.
Deterministic deficits, global rate allocation and the parent induction remain open.

## Main results

* `preparationWalks_noise`: completion payment for the actual list entry.
* `initialSecondSignal_noise_moment`: zeta-scaled noise at the actual prefix j+1.
* `initialSecondSignal_noise`: row-maximum noise on usage.
* `initialSecondSignal_preloss`: weighted stationary noise payment.
* `initialSecondSignal_overflowNoise`: unconditional overflow-selected tail payment.
* `initialSecondSignal_falseNoise`: postincrement false-overflow noise charges.
* `initialSignals_falseNoise`: both noise charges with separate rank and usage masks.
* `compressedBin_secondNoise`: noise contract extracted from successful compression.
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

section Walks
variable (B : BudgetData HP P) (M bin : ℕ)
  (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ks ku : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss)
  (hu : r.usage = gridChannel R.terminal ku st)
  (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
  (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
    B.complete M r (B.binPreparation bin r (F (i + 1)))
      (dyadicSlack (Nat.log2 M + 1) i)) = some W)
include haux hs hu hW

/-- No first-history accuracy premise is needed: bounded preparation alone pays the
literal usage completion with its original allocated length and precision. -/
theorem preparationWalks_noise (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let Xs := retainedMask R.source (side P ks) B.padding ss
    let Yu := retainedMask R.terminal (side P ku) B.padding st
    rowNormPow 4 P r.source.rate Xs Yu (fun σ x y => W[j]?.getD 0 σ x y -
      rowSliceMean Xs Yu (W[j]?.getD 0) x y) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  dsimp only
  simp_rw [B.preparationWalks_mean M bin r R ks ku ss st hs hu F W hW j hj]
  rw [B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj]
  have hr : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have hb (σ : Environment P 3) (x y : ZMod P) :
      |B.binPreparation bin r (F (j + 1)) σ x y| ≤ B.magnitude r := by
    have hp := B.binPreparation_mem_Icc bin haux r (F (j + 1)) σ x y
    rw [abs_of_nonneg hp.1]
    exact hp.2.trans (B.one_le_magnitude r)
  convert B.completion_noise M r R.source R.terminal R.source_terminal ks ku ss st hr
    (B.binPreparation bin r (F (j + 1))) hb (dyadicSlack (Nat.log2 M + 1) j) using 1 <;>
    congr 8; norm_num

/-- The actual second-channel statistic is centered at the literal usage mean at
postincrement prefix j+1. The first channel and rank denominator are unchanged. -/
theorem initialSecondSignal_noise_moment (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j) ≤
      (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  let Xs := retainedMask R.source (side P ks) B.padding ss
  let Yu := retainedMask R.terminal (side P ku) B.padding st
  let graphs := graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
    (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
    (CopyPadding.identifier B.padding st)
  let times := fun i (_ _ : ZMod P) => B.steps M r (dyadicSlack (Nat.log2 M + 1) (i - 1))
  let input := fun i => B.binPreparation bin r (F i)
  have hw := B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj
  have he (σ : Environment P 3) (x y : ZMod P) :=
    actualNoiseEntry_secondSignalIncrement R.source R.terminal (side P ks) (side P ka)
      (side P ku) B.padding ss st (fun _ => graphs) times input F ka ζ G j σ x y
  have heq (σ : Environment P 3) (x y : ZMod P) :
      actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j σ x y =
      |ζ| * |W[j]?.getD 0 σ x y - rowSliceMean Xs Yu (W[j]?.getD 0) x y| := by
    dsimp only at he
    simp only [actualNoiseEntry, twoMaskMean, Fin.isValue, one_ne_zero, ↓reduceIte,
      div_one, actualPrefix_twoSignal_second, Nat.add_sub_cancel] at he ⊢
    dsimp only [Xs, Yu]
    rw [B.preparationWalks_mean M bin r R ks ku ss st hs hu F W hW j hj, hw]
    have he' := he σ x y
    convert he' using 1 <;> congr 8
  rw [funext fun σ => funext fun x => funext fun y => heq σ x y]
  rw [rowNormPow]
  simp only [abs_mul, abs_abs, mul_pow, ← mul_sum, ← mul_expect]
  have hn := B.preparationWalks_noise M bin haux r R ks ku ss st hs hu F W hW j hj
  dsimp only at hn
  have hm := mul_le_mul_of_nonneg_left hn (pow_nonneg (abs_nonneg ζ) 4)
  unfold rowNormPow at hm
  convert hm using 1 <;> ring

section Scheduled
variable (ka : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
include hG

/-- Row-maximum second noise on usage, with the unchanged request precision. -/
theorem initialSecondSignal_noise (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    vertexNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
      (actualNoiseMax R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G Δ (fun _ _ _ _ => 0) 1 j) ≤
      (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  apply actualNoiseMax_budget R.source R.terminal (side P ks) (side P ka) (side P ku)
    B.padding ss st ka G hG _ _ hNu 1 j
  simpa only [Fin.isValue, one_ne_zero, ↓reduceIte] using
    B.initialSecondSignal_noise_moment M bin haux r R ks ku ss st hs hu F W hW ka G ζ j hj

/-- The second-noise stationary payment keeps the inverse-floor contribution explicit. -/
theorem initialSecondSignal_preloss {floor L : ℝ} (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let Xs := retainedMask R.source (side P ks) B.padding ss
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let γ := fun i => actualNoiseMax R.source R.terminal (side P ks) (side P ka)
      (side P ku) B.padding ss st ka G Δ (fun _ _ _ _ => 0) 1 i
    let e := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    (36 * L + 72 * L / floor) ^ 4 * vertexNormPow 4 P r.source.rate Xs
      (fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * γ i σ x) ≤
      ((36 * L * floor + 72 * L) * e / 511) ^ 4 := by
  extract_lets m Xs Δ γ e
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hbudget (i : ℕ) (hi : i ∈ range m) :
      vertexNormPow 4 P r.source.rate Xs (γ i) ≤ (e * 2 ^ dyadicSlack m i) ^ 4 := by
    have hn := B.initialSecondSignal_noise M bin haux r R ks ku ss st hs hu F W hW
      ka G hG ζ i (mem_range.mp hi)
    refine hn.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he
  have hp := vertexNormPow_sum_le_pow_sum (X := Xs) (by decide : 4 ≠ 0) hNu
    (range m) γ (dyadicFloor floor m) (fun i => e * 2 ^ dyadicSlack m i)
    (fun i _ => dyadicFloor_nonneg hf.le m i) (fun _ _ => by positivity) hbudget
  have hsched := pre_schedule_sum hf.le he m
  have hsum : 0 ≤ ∑ i ∈ range m, dyadicFloor floor m i * (e * 2 ^ dyadicSlack m i) :=
    sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf.le m i) (by positivity)
  have hp' := hp.trans (pow_le_pow_left₀ hsum hsched 4)
  refine (mul_le_mul_of_nonneg_left hp' (by positivity)).trans_eq ?_
  rw [← mul_pow]
  congr 1
  field_simp

/-- An actual overflow-selected tail pays all second noise without a rarity discount.
The selecting compression may be correlated with every preparation walk. -/
theorem initialSecondSignal_overflowNoise
    (S : Environment P 3 → ZMod P → Finset (ZMod P)) (n K : ℕ → ℕ) (floor : ℕ → ℝ)
    (increments : Environment P 3 → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (a : Environment P 3 → ZMod P → State (ZMod P)) :
    let m := Nat.log2 M + 1
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let γ := fun i => actualNoiseMax R.source R.terminal (side P ks) (side P ka)
      (side P ku) B.padding ss st ka G Δ (fun _ _ _ _ => 0) 1 i
    vertexNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
      (fun σ x => firstOverflowNoiseTail (S σ x) n K floor (increments σ x) (a σ x) m
        (fun i => 28 ^ (m - i)) (fun i => γ i σ x)) ≤
      (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) * (7 / 9)) ^ 4 := by
  extract_lets m Δ γ
  have he : 0 ≤ |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) := by positivity
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have h := vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget S n K floor increments a m
    (by decide : 4 ≠ 0) hNu (retainedMask R.source (side P ks) B.padding ss)
    (C := 28) (q := 1 / 64) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    he γ (fun _ _ _ _ _ => kthLargest_nonneg)
    (fun i hi => B.initialSecondSignal_noise M bin haux r R ks ku ss st hs hu F W hW
      ka G hG ζ i hi)
  norm_num only [show (28 : ℝ) * (1 / 64) / (1 - 28 * (1 / 64)) = 7 / 9 by norm_num] at h
  exact h

omit hG in
/-- Second-noise raw false-overflow charges use the already-added prefix j+1 on usage.
No bound for either deterministic mean discrepancy is assumed. -/
theorem initialSecondSignal_falseNoise {floor : ℝ} (hf : 0 < floor) (radius : ℝ) :
    let m := Nat.log2 M + 1
    let n := compatibleCapacity HP.K m
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let e := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    ∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
        ((n j : ℝ) * dyadicFloor floor m j ^ 4)) *
      rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ku) B.padding st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G Δ (fun _ _ _ _ => 0) 1 j) ≤
      64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4 * e ^ 4 / 63 := by
  extract_lets m n Δ e
  have he : 0 ≤ e := by dsimp only [e]; positivity
  refine (sum_le_sum fun j hj => ?_).trans
    (false_schedule_sum_capacity hf (Nat.cast_nonneg HP.K) m n
      (fun j _ => (compatibleCapacity_bounds HP.K m j).2))
  have hn := B.initialSecondSignal_noise_moment M bin haux r R ks ku ss st hs hu F W hW
    ka G ζ j (mem_range.mp hj)
  have hbudget := hn.trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he) 4)
  exact mul_le_mul_of_nonneg_left hbudget (by positivity)

end Scheduled

/-- Both centered noises pay the false-overflow raw-prefix charge on their own masks.
The deterministic envelopes still need their separate integrated payments. -/
theorem initialSignals_falseNoise (hM : 0 < M) (hbins : B.bins.Nonempty)
    (ka : ℕ) (ht : r.terminal = gridChannel R.terminal ka st)
    (hF : B.initialPrefixes M r = some F)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (ζ : ℝ) {floor : ℝ} (hf : 0 < floor) (radius : ℝ) :
    let m := Nat.log2 M + 1
    let Δ := firstSignalIncrement F ka
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ)
    let e₀ := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let e₁ := |ζ| * (2 : ℝ) ^ (-B.requestPrecision M r)
    let c := 64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4
    ∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) *
      (rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G Δ (fun _ _ _ _ => 0) 0 j) +
       rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ku) B.padding st)
        (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G Δ (fun _ _ _ _ => 0) 1 j)) ≤
      c * e₀ ^ 4 / 63 + c * e₁ ^ 4 / 63 := by
  dsimp only
  simp_rw [mul_add, sum_add_distrib]
  apply add_le_add
  · exact B.initialFirstSignal_falseNoise M hM hbins r R.source R.terminal
      R.source_terminal ks ka ss st hs ht F hF G hG (side P ku)
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ) hf radius
  · exact B.initialSecondSignal_falseNoise M bin haux r R ks ku ss st hs hu F W hW
      ka G ζ hf radius

end Walks
/-- Successful compressed-bin execution supplies its actual histories and the paid
second-noise statistics. This is a noise contract, not compressed-output accuracy. -/
theorem compressedBin_secondNoise (B : BudgetData HP P) (M bin ka : ℕ)
    (haux : ∀ d, B.auxiliary bin d ∈ Set.Icc 0 1) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ku : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (hu : r.usage = gridChannel R.terminal ku st)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.compressedBin M bin ka ζ floor r = some A) :
    ∃ F W,
      B.initialPrefixes M r = some F ∧
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.complete M r (B.binPreparation bin r (F (i + 1)))
          (dyadicSlack (Nat.log2 M + 1) i)) = some W ∧
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka B.base (firstSignalIncrement F ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
            (fun _ _ _ _ => 0) 1 j) ≤
          (|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
            (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  unfold compressedBin at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp only [hF, bind, Option.bind_none] at hA; contradiction
    | some F =>
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
          B.complete M r (B.binPreparation bin r (F (i + 1)))
            (dyadicSlack (Nat.log2 M + 1) i)) with
      | none => simp only [hF, hW, bind, Option.bind_some, Option.bind_none] at hA; contradiction
      | some W =>
        refine ⟨F, W, rfl, hW, ?_⟩
        intro j hj
        exact B.initialSecondSignal_noise_moment M bin haux r R ks ku ss st hs hu F W hW
          ka B.base ζ j hj

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
