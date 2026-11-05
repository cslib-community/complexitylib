/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialSecondNoise
public import Complexity.Foundations.Probability.HierarchyTransportedPreparation
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduleAllocation

/-!
# Allocating the literal selected-preparation noise

The actual usage-walk length has twice the logarithmic decay needed by its old range
payment. Its spare decay pays the sparse selected input, with its full-terminal rank
support, on an explicitly covered field family. No first-history accuracy or second-mean
stability is used. Every preparation is allowed to depend on the same environment.

The new scalar is a minimum with the existing payment. The execution theorem consumes
literal successful preparation lists; it does not construct successful recursive children.
Field coverage is essential to this particular structural-charge argument. A uniform
second-mean salary, the full recursive IH and native space bounds remain separate.
These are original bounds on the existing finite fourth-moment model.
-/

public section
noncomputable section
namespace Cslib.Probability

/-- Retain the spare half of the logarithmic walk allocation. This bound uses the
same length as `spectralWalkLength_payment`, without increasing the computed walk. -/
theorem spectralWalkLength_squared_payment {r C ε : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC : 0 ≤ C) (hε : 0 < ε) (d t : ℕ)
    (ht : spectralWalkLength r C ε d ≤ t) :
    r ^ (2 * t) ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 8 / (C + 1) ^ 2 := by
  have hb : 0 < (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 := by positivity
  have hlog := (Nat.le_ceil (Real.logb r
    ((ε * (64 : ℝ)⁻¹ ^ d) ^ 4 / (C + 1)))).trans
      (show (spectralWalkLength r C ε d : ℝ) ≤ t by exact_mod_cast ht)
  have hp : r ^ t ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 / (C + 1) := by
    have h := (Real.logb_le_iff_le_rpow_of_base_lt_one hr hr1
      (div_pos hb (by positivity))).mp hlog
    rwa [Real.rpow_natCast] at h
  have hsq := pow_le_pow_left₀ (pow_nonneg hr.le t) hp 2
  simpa only [← pow_mul, mul_comm t 2, div_pow, ← pow_mul] using hsq

end Cslib.Probability

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Actual sparse-input spectral payment, intersected with the original range payment.
This scalar retains zeta, the original source normalization and computed step count. -/
@[expose] def initialSecondNoiseMoment (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ζ : ℝ) (j : ℕ) : ℝ :=
  min ((|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
    (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4)
    (ζ ^ 4 * (32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^
      (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) j)) * (16 * HP.K)))

/-- Exact integration seam for the existing computed four-statistic consumer.
Replacing only its second-noise branch by the minimum with this scalar preserves the
old bound. The literal preparation-list theorem below supplies the new branch. -/
theorem initialSecondNoiseMoment_min_precision (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ : ℝ) (j : ℕ) :
    min (B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j true 1)
      (B.initialSecondNoiseMoment M r ζ j) = B.initialSecondNoiseMoment M r ζ j := by
  change min _ (min _ _) = min _ _
  exact min_eq_right (min_le_left _ _)

/-- Both branches are nonnegative; no independence or mean-error hypothesis enters. -/
lemma initialSecondNoiseMoment_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ζ : ℝ) (j : ℕ) :
    0 ≤ B.initialSecondNoiseMoment M r ζ j := by
  unfold initialSecondNoiseMoment
  apply le_min (by positivity)
  have hr : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4) := by norm_num
  positivity

/-- The actual completed preparation list consumes the sparse spectral scalar.
The rank mask is terminal, the noise mask is usage, and the first history is arbitrary. -/
theorem initialSecondSignal_noise_allocated (B : BudgetData HP P) (M bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (H : Horizon P) (ks ka ku : ℕ) (hks : ks ≤ H.maxExponent) (husage : ka ≤ ku)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j) ≤ B.initialSecondNoiseMoment M r ζ j := by
  apply le_min
  · apply B.initialSecondSignal_noise_moment M bin _ r R ks ku ss st hs hu F W hW ka G ζ j hj
    intro d
    rw [haux]
    exact ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩
  · let input := fun i => selectedPreparation HP B.padding R st ka (F i)
    let walks := fun i => conditionalWalk
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
        (CopyPadding.identifier B.padding st))
      (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) (i - 1))) (input i)
    have he (σ : Environment P 3) (x y : ZMod P) :
        actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G (firstSignalIncrement F ka
            (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
          (fun _ _ _ _ => 0) 1 j σ x y =
        actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G (firstSignalIncrement F ka (secondSignalIncrement walks ζ))
          (fun _ _ _ _ => 0) 1 j σ x y := by
      simp only [actualNoiseEntry, twoMaskMean, Fin.isValue, one_ne_zero, ↓reduceIte,
        div_one, actualPrefix_twoSignal_second, Nat.add_sub_cancel]
      have hw := B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj
      rw [B.binPreparation_eq_selected bin r R ka st ht haux] at hw
      have hw' : W[j]?.getD 0 = walks (j + 1) := by
        dsimp only [walks, input, Nat.add_sub_cancel]
        convert hw using 1; congr 8
      rw [hw']
    have heq := funext fun σ => funext fun x => funext fun y => he σ x y
    rw [heq]
    have hb := actualSelectedSecondSignal_noise_le HP
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) B.padding R H ks ka ku husage
      hks ss st F F (fun i => B.steps M r (dyadicSlack (Nat.log2 M + 1) (i - 1))) ζ G j
    simpa only [walks, input, hs, gridChannel, Nat.add_sub_cancel, Nat.cast_ofNat] using hb

/-- A covered field pays a scalar structural salary from spare spectral decay.
The numerical coverage is on the field, not on a desired noise moment or child IH.
The original precision and usage-walk step allocation are unchanged. -/
theorem initialSecondNoiseMoment_le (B : BudgetData HP P) (M ks : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (hp : 0 ≤ B.requestPrecision M r)
    (ζ q : ℝ)
    (hfield : 512 * (HP.K : ℝ) ≤ q ^ 4 * (32 * P + 1) ^ 2) (j : ℕ) :
    B.initialSecondNoiseMoment M r ζ j ≤
      (|ζ| * q * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  let C := 32 * ((P : ℝ) ^ 2 / (P * r.source.rate) * B.magnitude r ^ 4)
  let ε := (2 : ℝ) ^ (-B.requestPrecision M r)
  let d := dyadicSlack (Nat.log2 M + 1) j
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)
  have hr : 0 < ρ := by norm_num [ρ]
  have hr1 : ρ < 1 := by norm_num [ρ]
  have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have hsource1 : r.source.rate ≤ 1 := by
    rw [hs]
    simpa only [rate, pow_zero, inv_one, one_pow] using rate_antitone (Nat.zero_le ks)
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hNu := mul_pos hP hsource
  have hwidth : (P : ℝ) ≤ (P : ℝ) ^ 2 / (P * r.source.rate) := by
    apply (le_div_iff₀ hNu).mpr
    nlinarith
  have hm := one_le_pow₀ (B.one_le_magnitude r) (n := 4)
  have hC : 32 * P ≤ C := by
    dsimp only [C]
    have hh := mul_le_mul hwidth hm (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    nlinarith only [hh]
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ 32 * P).trans hC
  have ht := spectralWalkLength_squared_payment hr hr1 hC0
    (show 0 < ε by dsimp only [ε]; positivity) d (B.steps M r d) (Nat.le_max_right _ _)
  have ht' : ρ ^ (2 * B.steps M r d) * (C + 1) ^ 2 ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 8 :=
    (le_div_iff₀ (by positivity)).mp ht
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hx0 : 0 ≤ ε * (64 : ℝ)⁻¹ ^ d := by positivity
  have hx1 : ε * (64 : ℝ)⁻¹ ^ d ≤ 1 :=
    (mul_le_mul_of_nonneg_right hε1 (by positivity)).trans
      (by simpa only [one_mul] using
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 64⁻¹) (by norm_num : (64 : ℝ)⁻¹ ≤ 1) :
          (64 : ℝ)⁻¹ ^ d ≤ 1))
  have hx8 : (ε * (64 : ℝ)⁻¹ ^ d) ^ 8 ≤ (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 :=
    pow_le_pow_of_le_one hx0 hx1 (by decide : 4 ≤ 8)
  have hc2 : (32 * (P : ℝ) + 1) ^ 2 ≤ (C + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hsparse : 512 * (HP.K : ℝ) * ρ ^ (2 * B.steps M r d) ≤
      q ^ 4 * (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 := by
    calc
      _ ≤ (q ^ 4 * (32 * P + 1) ^ 2) * ρ ^ (2 * B.steps M r d) :=
        mul_le_mul_of_nonneg_right hfield (by positivity)
      _ ≤ q ^ 4 * (ρ ^ (2 * B.steps M r d) * (C + 1) ^ 2) := by
        nlinarith only [mul_le_mul_of_nonneg_left hc2
          (show 0 ≤ q ^ 4 * ρ ^ (2 * B.steps M r d) by positivity)]
      _ ≤ q ^ 4 * (ε * (64 : ℝ)⁻¹ ^ d) ^ 4 :=
        mul_le_mul_of_nonneg_left (ht'.trans hx8) (by positivity)
  apply (min_le_right _ _).trans
  have hh := mul_le_mul_of_nonneg_left hsparse (pow_nonneg (abs_nonneg ζ) 4)
  convert hh using 1 <;> simp only [mul_pow, (by decide : Even (4 : ℕ)).pow_abs ζ] <;> ring

/-- A natural field-size condition supplies the preceding scalar coverage. The
charge is fixed before the field and all request, usage, horizon and precision data. -/
theorem initialSecondNoiseMoment_charge (A : ℕ) (B : BudgetData HP P)
    (hfield : (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P) (M ks : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (hp : 0 ≤ B.requestPrecision M r) (ζ : ℝ) (j : ℕ) :
    B.initialSecondNoiseMoment M r ζ j ≤
      (|ζ| * (1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  apply B.initialSecondNoiseMoment_le M ks r hs hp ζ ((1 / 2 : ℝ) ^ A)
  have hf : (512 * (HP.K : ℝ) + 1) * (2 : ℝ) ^ (2 * A) ≤ P := by exact_mod_cast hfield
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 * A) := by positivity
  have hk : 0 ≤ (512 * (HP.K : ℝ) + 1) := by positivity
  have hsquare := pow_le_pow_left₀ (mul_nonneg hk hpow.le) hf 2
  have hid : ((1 / 2 : ℝ) ^ A) ^ 4 * ((2 : ℝ) ^ (2 * A)) ^ 2 = 1 := by
    simp only [div_pow, one_pow, ← pow_mul]
    rw [show 2 * A * 2 = A * 4 by omega]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ ((1 / 2 : ℝ) ^ A) ^ 4 by positivity)
  have hsq : 512 * (HP.K : ℝ) ≤ (512 * (HP.K : ℝ) + 1) ^ 2 := by
    have hk0 : (0 : ℝ) ≤ HP.K := Nat.cast_nonneg HP.K
    nlinarith
  have hid' : ((1 / 2 : ℝ) ^ A) ^ 4 *
      ((512 * (HP.K : ℝ) + 1) * (2 : ℝ) ^ (2 * A)) ^ 2 =
        (512 * (HP.K : ℝ) + 1) ^ 2 := by
    rw [mul_pow]
    nlinarith only [hid]
  rw [hid'] at hh
  exact (hsq.trans hh).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ P)
      (by have hp0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P; linarith) 2)
    (by positivity))

/-- Stationary, final, unconditional factor-28 tail and literal raw false-event
allocations of the same scalar consumed by the actual preparation-list theorem.
All weights retain their original floor/capacity/postincrement conventions. -/
theorem initialSecondNoiseMoment_schedule (A : ℕ) (B : BudgetData HP P)
    (hfield : (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P) (M ks : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (hp : 0 ≤ B.requestPrecision M r)
    (ζ floor radius : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let E := |ζ| * (1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r)
    let a := fun j => B.initialSecondNoiseMoment M r ζ j
    (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ)) ≤ floor * E / 511 ∧
    a (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ E / 4 ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ)) ≤ E * (458752 / 57) ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63 := by
  extract_lets m E a
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have han (j : ℕ) : 0 ≤ a j := B.initialSecondNoiseMoment_nonneg M r ζ j
  have he (j : ℕ) (_hj : j < m) :
      0 ≤ a j ^ (4⁻¹ : ℝ) ∧ a j ^ (4⁻¹ : ℝ) ≤ E * (1 / 4 : ℝ) ^ dyadicSlack m j := by
    refine ⟨Real.rpow_nonneg (han j) _, ?_⟩
    have hb := B.initialSecondNoiseMoment_charge A hfield M ks r hs hp ζ j
    have hroot := Real.rpow_le_rpow (han j) hb (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have hid : ((E * (1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4) ^ (4⁻¹ : ℝ) =
        E * (1 / 64 : ℝ) ^ dyadicSlack m j := by
      convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ E * (1 / 64 : ℝ) ^
        dyadicSlack m j) (by decide : (4 : ℕ) ≠ 0) using 1
    exact (hroot.trans_eq hid).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 1 / 4) _) hE)
  obtain ⟨hpre, hfinal, htail, hraw⟩ := compatible_quarter_noise_schedule hf hE HP.K m
    radius (fun j => a j ^ (4⁻¹ : ℝ)) he
  refine ⟨hpre, hfinal _ (by dsimp only [m]; omega), htail, ?_⟩
  have hpow (j : ℕ) : (a j ^ (4⁻¹ : ℝ)) ^ 4 = a j := by
    convert Real.rpow_inv_natCast_pow (han j) (by decide : (4 : ℕ) ≠ 0) using 1
  simpa only [hpow] using hraw

/-- Choose the structural charge before fields, horizons, source/terminal/usage data,
budgets and precision. The remaining family restriction is explicit field coverage;
no second-mean salary or recursive accuracy is assumed. -/
theorem initialSecondNoiseMoment_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ tolerance : ℝ) (ht : 0 < tolerance) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P →
      ∀ (M ks : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.source.rate = rate ks → 0 ≤ B.requestPrecision M r → ∀ j,
      B.initialSecondNoiseMoment M r ζ j ≤
        (tolerance * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
  obtain ⟨A, hA⟩ := exists_nat_gt (|ζ| / tolerance)
  have hpow : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast (show A ≤ 2 ^ A from Nat.lt_two_pow_self.le)
  have hs : |ζ| * (1 / 2 : ℝ) ^ A ≤ tolerance := by
    rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity)]
    have ha := (div_lt_iff₀ ht).mp hA
    nlinarith only [ha, mul_le_mul_of_nonneg_left hpow ht.le]
  refine ⟨A, ?_⟩
  intro P _ B hfield M ks r hsource hp j
  apply (B.initialSecondNoiseMoment_charge A hfield M ks r hsource hp ζ j).trans
  apply pow_le_pow_left₀ (by positivity) _ 4
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (by positivity)) (by positivity)

/-- Successful computed compression supplies literal histories consumed by the new
scalar. This is conditional execution; no joint lower-budget availability is claimed.
In particular it demands no second-mean stability premise. -/
theorem compressedBin_secondNoise_allocated (B : BudgetData HP P) (M bin ka : ℕ)
    (ζ floor : ℝ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (H : Horizon P) (ks ku : ℕ) (hks : ks ≤ H.maxExponent) (husage : ka ≤ ku)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (result : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hresult : B.compressedBin M bin ka ζ floor r = some result) :
    ∃ F W, B.initialPrefixes M r = some F ∧
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.complete M r (B.binPreparation bin r (F (i + 1)))
          (dyadicSlack (Nat.log2 M + 1) i)) = some W ∧
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka B.base (firstSignalIncrement F ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
            (fun _ _ _ _ => 0) 1 j) ≤ B.initialSecondNoiseMoment M r ζ j := by
  have haux' (d : ℝ) : B.auxiliary bin d ∈ Set.Icc 0 1 := by
    rw [haux]
    exact ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩
  obtain ⟨F, W, hF, hW, _⟩ := B.compressedBin_secondNoise M bin ka haux' ζ floor
    r R ks ku ss st hs hu result hresult
  exact ⟨F, W, hF, hW, fun j hj => B.initialSecondSignal_noise_allocated M bin r R H
    ks ka ku hks husage ss st hs ht hu haux F W hW B.base ζ j hj⟩

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
