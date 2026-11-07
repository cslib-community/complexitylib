/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialGeometric
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform decay of the complete initial geometric payment

All constants are chosen before the retained depth and field. The estimates apply uniformly
to the literal computed payment, including its exceptional first group and both unconditional
noises. Successful outputs at arbitrary accuracy are constructed at linear statistical budget.
They do not establish the general lower-budget invariant or a native implementation.

## Main results

* `initialGeometricRHS_uniform`: one complete majorant before depth and prime.
* `initialGeometricRHS_uniform_small`: uniform arbitrary accuracy of the computed payment.
* `fixed_charge_linear_guards`: eventual actual guards from fixed structural constants.
* `exists_compressedBin_uniform_accuracy`: successful actual output at arbitrary accuracy.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {HP : FourthRootHierarchyParams 16 1 16 32 8}

private lemma fourth_root_pow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 4) ^ (4⁻¹ : ℝ) = x := by
  convert Real.pow_rpow_inv_natCast hx (by decide : (4 : ℕ) ≠ 0) using 1

private lemma weighted_root_bound {x w A s : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ w) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (h : w ^ 4 * x ≤ A * s) :
    w * x ^ (4⁻¹ : ℝ) ≤ A ^ (4⁻¹ : ℝ) * s ^ (4⁻¹ : ℝ) := by
  have hr := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hw 4) hx) h
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rwa [Real.mul_rpow (pow_nonneg hw 4) hx, fourth_root_pow hw,
    Real.mul_rpow hA hs] at hr

private lemma root_bound {x A s : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (h : x ≤ A * s) :
    x ^ (4⁻¹ : ℝ) ≤ A ^ (4⁻¹ : ℝ) * s ^ (4⁻¹ : ℝ) := by
  simpa only [one_pow, one_mul] using
    weighted_root_bound hx (by norm_num : (0 : ℝ) ≤ 1) hA hs (by simpa using h)

private lemma bin_rate_sum_le (n : ℕ) :
    ∑ i ∈ range (n + 1), rate i ≤ (16 / 15 : ℝ) := by
  simp_rw [rate_eq_source_grid]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1)
    (by norm_num : (0 : ℝ) ≤ 16⁻¹) (by norm_num : (16⁻¹ : ℝ) < 1)
  norm_num only [Nat.Ico_zero_eq_range, pow_zero] at h
  convert h using 1; norm_num

private lemma width_sq_le (P n : ℕ) (hP : P ≤ 2 ^ (n + 1)) :
    (P : ℝ) ^ 2 ≤ 4 * (4 : ℝ) ^ n := by
  have hp : (P : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hP
  apply (pow_le_pow_left₀ (Nat.cast_nonneg P) hp 2).trans_eq
  rw [← pow_mul, Nat.add_mul, Nat.one_mul, pow_add, Nat.mul_comm n 2, pow_mul]
  norm_num
  ring

private lemma decay_width {q : ℝ} (hq : 0 ≤ q) (hq64 : q * 4 ≤ 1 / 64)
    (P n d : ℕ) (hP : P ≤ 2 ^ (n + 1)) (hd : n ≤ d) :
    q ^ d * (P : ℝ) ^ 2 ≤ 4 * (1 / 64 : ℝ) ^ n := by
  have hq1 : q ≤ 1 := by linarith
  calc
    _ ≤ q ^ n * (4 * (4 : ℝ) ^ n) := mul_le_mul
      (pow_le_pow_of_le_one hq hq1 hd) (width_sq_le P n hP) (by positivity)
      (pow_nonneg hq _)
    _ = 4 * (q * 4) ^ n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq64 n)
      (by norm_num)

private lemma precision_le {p : ℝ} {n : ℕ} (hp : 2 * (n : ℝ) ≤ p) :
    (2 : ℝ) ^ (-p) ≤ (1 / 4 : ℝ) ^ n := by
  calc
    _ ≤ (2 : ℝ) ^ ((-2) * (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by rw [Real.rpow_mul_natCast (by norm_num)]; norm_num

private lemma tail_root_payment {x y z v F E s w W Q p : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hF : 0 ≤ F) (hE : 0 ≤ E) (hs : 0 ≤ s) (hw : 0 ≤ w) (hQ : 0 ≤ Q)
    (hlx : x ≤ F * s) (hly : y ≤ F * s) (hez : z ≤ E * p) (hev : v ≤ E * p)
    (hwp : w ^ 4 * p ≤ 4 * s) (hW : W ≤ Q * w) :
    Q * (x ^ (4⁻¹ : ℝ) + y ^ (4⁻¹ : ℝ)) / 63 +
      W * (z ^ (4⁻¹ : ℝ) + v ^ (4⁻¹ : ℝ)) ≤
      (Q * (2 * F ^ (4⁻¹ : ℝ)) / 63 + Q * (2 * (4 * E) ^ (4⁻¹ : ℝ))) *
        s ^ (4⁻¹ : ℝ) := by
  have hl1 := root_bound hx hF hs hlx
  have hl2 := root_bound hy hF hs hly
  have hb1 := mul_le_mul_of_nonneg_left hez (pow_nonneg hw 4)
  have hb2 := mul_le_mul_of_nonneg_left hev (pow_nonneg hw 4)
  have hb3 := mul_le_mul_of_nonneg_left hwp hE
  have hr1 := weighted_root_bound hz hw (by positivity : 0 ≤ 4 * E) hs
    (by linarith only [hb1, hb3])
  have hr2 := weighted_root_bound hv hw (by positivity : 0 ≤ 4 * E) hs
    (by linarith only [hb2, hb3])
  have hg := mul_le_mul_of_nonneg_right hW
    (add_nonneg (Real.rpow_nonneg hz (4⁻¹ : ℝ)) (Real.rpow_nonneg hv (4⁻¹ : ℝ)))
  have hl := mul_le_mul_of_nonneg_left (add_le_add hl1 hl2) hQ
  have he := mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hQ
  linarith only [hg, hl, he]

private lemma stationary_root_payment {floor f e t : ℝ} (hf : 0 < floor)
    (hfs : 0 ≤ f) (ht : 0 ≤ t) (m : ℕ) (hm : 0 < m) (a : ℕ → ℝ)
    (hlate : ∀ i ≠ 0, a i ≤ 2 * f * t)
    (hearly : (1 / 1024 : ℝ) ^ dyadicSlack m 0 * a 0 ≤ 2 * e * t) :
    (∑ i ∈ range m, dyadicFloor floor m i * a i) ≤ floor * (2 * f + 2 * e) * t := by
  have hterm (i : ℕ) : dyadicFloor floor m i * a i ≤
      dyadicFloor floor m i * (2 * f * t) +
        if i = 0 then floor * (2 * e * t) else 0 := by
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceIte]
      have hh := mul_le_mul_of_nonneg_left hearly hf.le
      change floor * ((1 / 1024 : ℝ) ^ dyadicSlack m 0) * a 0 ≤ _
      linarith only [hh, mul_nonneg (dyadicFloor_nonneg hf.le m 0)
        (show 0 ≤ 2 * f * t by positivity)]
    · simp only [hi, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_left (hlate i hi) (dyadicFloor_nonneg hf.le _ _)
  calc
    _ ≤ ∑ i ∈ range m, (dyadicFloor floor m i * (2 * f * t) +
        if i = 0 then floor * (2 * e * t) else 0) := sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ range m, dyadicFloor floor m i) * (2 * f * t) + floor * (2 * e * t) := by
      simp only [sum_add_distrib, ← sum_mul, sum_ite_eq', mem_range, hm, ↓reduceIte]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right
        (sum_range_dyadicFloor_le_scale hf.le m) (by positivity : (0 : ℝ) ≤ 2 * f * t)
      linarith only [hh, mul_nonneg (by positivity : (0 : ℝ) ≤ floor * (1022 / 1023))
        (show 0 ≤ 2 * f * t by positivity)]

/-- A single majorant for EVERY term of the literal geometric payment. Source and terminal
exponents, both sensitivities, zeta, positive floor, decoder constants and primitive bin-cap
bound are fixed before depth, prime, base, suffixes and request. The precision premises concern
the actual requests; no output-error budget is supplied. A budget `128*c*n` may be substituted
once its guards hold. No transport between different fields is required. -/
theorem initialGeometricRHS_uniform (ks ka : ℕ) (ζ floor Lh Lρ C Cpre cap : ℝ)
    (hf : 0 < floor) (hcap : 0 ≤ cap) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P n M : ℕ) [Fact P.Prime] (B : BudgetData HP P),
      1 < M → n ≤ dyadicSlack (Nat.log2 M + 1) 0 →
      P ≤ 2 ^ (n + 1) → B.bins = range (n + 1) → B.binRate = rate → B.binCap ≤ cap →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      (∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale { r with usage := r.terminal } (some bin)) < M) →
      2 * (n : ℝ) ≤ B.requestPrecision M { r with usage := r.terminal } →
      2 * (n : ℝ) ≤ B.requestPrecision M r →
      ∀ (H : Horizon P), ks ≤ H.maxExponent →
      ∀ (R : RoleProfile 3) (ss st : List (ZMod P)),
      B.initialGeometricRHS M n r R ks ka ss st ζ floor Lh Lρ C Cpre ≤
        D * (1 / 64 : ℝ) ^ n := by
  have hr := rate_pos ka
  let A := (|ζ| * (Lh + Lρ) / rate ka) ^ 4
  let b := 1 + cap * (16 / 15)
  let F := 64 / rate ka ^ 4 + 544 * A
  let E := 16 * b ^ 4 / rate ka ^ 4 + 8 * A * (1 + 16 * b ^ 4)
  let f := F ^ (4⁻¹ : ℝ)
  let e := (4 * E) ^ (4⁻¹ : ℝ)
  let Q := (2 + 256 / floor) ^ (4⁻¹ : ℝ)
  let noise := (64 / 63) / rate ka + |ζ|
  let S := floor * (2 * f + 2 * e) + floor * noise / 511
  let T := Q * (2 * f) / 63 + Q * (2 * e) + noise * (7 / 9)
  let radius := (2 * max (1 : ℝ) 16) ^ (4⁻¹ : ℝ)
  let c := 64 * (HP.K : ℝ) * radius ^ 4 / floor ^ 4
  let D := 128 * (HP.K : ℝ) *
    (Cpre ^ 4 * S ^ 4 + C ^ 4 * (2 * f + noise / 64) ^ 4 + C ^ 4 * T ^ 4) +
    64 * (c * (2 * F) / 63 + c * (8 * E) + c * noise ^ 4 * 2 / 63)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hf0 : 0 ≤ f := Real.rpow_nonneg hF _
  have he0 : 0 ≤ e := Real.rpow_nonneg (by positivity) _
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by positivity) _
  have hnoise : 0 ≤ noise := by dsimp only [noise]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro P n M _ B hM hd hP hbins hrate hBC r hcut hp0 hp1 H hks R ss st
  have hsr := rate_pos ks
  let m := Nat.log2 M + 1
  let s := (1 / 64 : ℝ) ^ n
  let t := s ^ (4⁻¹ : ℝ)
  let u := rate n
  let p := (2 : ℝ) ^ (-B.requestPrecision M { r with usage := r.terminal })
  let p' := (2 : ℝ) ^ (-B.requestPrecision M r)
  let X := retainedMask R.source (side P ks) B.padding ss
  let Y := retainedMask R.terminal (side P ka) B.padding st
  let row := fun v => rowNormPow 4 P (rate ks) X Y (fun _ _ _ => v)
  let vertex := fun v => vertexNormPow 4 P (rate ks) X (fun _ _ => v)
  let q := fun i => B.initialMeanCharge M n i ka r
  let inactive := B.binCap * ∑ bin ∈ B.bins, B.binRate bin
  let prep := fun i => (P : ℝ) * A *
    (8 * (((p * (64 / 63) / rate ka) * rate ka * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 +
      row (u + B.initialInactiveCharge M i r)))
  have hprep_eq (i : ℕ) : prep i = (P : ℝ) * A *
      (8 * ((p * (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 +
        row (u + B.initialInactiveCharge M i r))) := by
    dsimp only [prep]
    rw [div_mul_cancel₀ _ hr.ne']
  let latePrep := (P : ℝ) * A * 8 * ((p / 63) ^ 4 + row u)
  let earlyPrep := (P : ℝ) * A * 8 * ((p / 63) ^ 4 + row (u + inactive))
  let a := fun i => (vertex (q i)) ^ (4⁻¹ : ℝ) + (prep i) ^ (4⁻¹ : ℝ)
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have ht : 0 ≤ t := Real.rpow_nonneg hs _
  have ht4 : t ^ 4 = s := by
    convert Real.rpow_inv_natCast_pow hs (by decide : (4 : ℕ) ≠ 0) using 1
  have hu : 0 ≤ u := (rate_pos n).le
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hp' : 0 ≤ p' := by dsimp only [p']; positivity
  have hp_le := precision_le hp0
  have hp'_le := precision_le hp1
  have hv1 : (1 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp1 : p ≤ 1 := hp_le.trans hv1
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).one_lt.le
  have hPP : (P : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith only [hP1]
  have hPs : (P : ℝ) ^ 2 * u ^ 4 ≤ 4 * s :=
    (bounded_width_omission P n hP).trans (by
      dsimp only [s]; gcongr; norm_num)
  have hps : (P : ℝ) ^ 2 * p ^ 4 ≤ 4 * s := bounded_width_precision_sq P n hP hp0
  have hus : u ^ 4 ≤ 4 * s := (le_mul_of_one_le_left (pow_nonneg hu 4)
    (one_le_pow₀ hP1)).trans hPs
  have hpp : (P : ℝ) * p ^ 4 ≤ 4 * s :=
    (mul_le_mul_of_nonneg_right hPP (pow_nonneg hp 4)).trans hps
  have hPu : (P : ℝ) * u ^ 4 ≤ 4 * s :=
    (mul_le_mul_of_nonneg_right hPP (pow_nonneg hu 4)).trans hPs
  have hrow0 (v : ℝ) : 0 ≤ row v := rowNormPow_nonneg (by positivity) _
  have hvertex0 (v : ℝ) : 0 ≤ vertex v := vertexNormPow_nonneg (by positivity) _
  have hrow (v : ℝ) (hv : 0 ≤ v) : row v ≤ 16 * P * v ^ 4 :=
    grid_row_moment_le B.padding R.source ks ss H hks Y _ hv
      (by intro σ x y; rw [abs_of_nonneg hv])
  have hvertex (v : ℝ) (hv : 0 ≤ v) : vertex v ≤ 16 * v ^ 4 :=
    grid_vertex_moment_le B.padding R.source ks ss H hks _ hv
      (by intro σ x; rw [abs_of_nonneg hv])
  have hbr (i : ℕ) : 0 ≤ B.binRate i := by rw [hrate]; exact (rate_pos i).le
  have hinactive0 : 0 ≤ inactive := mul_nonneg B.binCap_nonneg (sum_nonneg fun i _ => hbr i)
  have hinactive : inactive ≤ cap * (16 / 15) := by
    dsimp only [inactive]
    rw [hbins, hrate]
    exact mul_le_mul hBC (bin_rate_sum_le n) (sum_nonneg fun i _ => (rate_pos i).le) hcap
  have hub : u + inactive ≤ b := by
    have hu1 : u ≤ 1 := by
      dsimp only [u]
      rw [rate_eq_source_grid]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [b]
    linarith only [hu1, hinactive]
  have hz (i : ℕ) (hi : i ≠ 0) : B.initialInactiveCharge M i r = 0 :=
    B.initialInactiveCharge_eq_zero_of_pos M i hM (by omega) r hcut
  have hcharge0 (i : ℕ) : 0 ≤ B.initialInactiveCharge M i r := by
    unfold initialInactiveCharge
    apply mul_nonneg B.binCap_nonneg
    apply sum_nonneg
    intro j _
    split_ifs
    · exact hbr j
    · exact le_rfl
  have hcharge (i : ℕ) : B.initialInactiveCharge M i r ≤ inactive :=
    B.initialInactiveCharge_le M i r hbr
  have hq0 (i : ℕ) : 0 ≤ q i := by
    dsimp only [q, initialMeanCharge]
    exact div_nonneg (add_nonneg hu (hcharge0 i)) (rate_pos ka).le
  have hqbound (i : ℕ) : q i ≤ b / rate ka := by
    dsimp only [q, initialMeanCharge]
    exact div_le_div_of_nonneg_right ((add_le_add le_rfl (hcharge i)).trans hub) (rate_pos ka).le
  have hlateRow : row (u / rate ka) ≤ F * s := by
    calc
      _ ≤ 16 * P * (u / rate ka) ^ 4 := hrow _ (by positivity)
      _ ≤ (64 / rate ka ^ 4) * s := by
        rw [div_pow]
        have hh := mul_le_mul_of_nonneg_left hPu (div_nonneg (by norm_num : (0 : ℝ) ≤ 16)
          (pow_nonneg hr.le 4))
        convert hh using 1 <;> ring
      _ ≤ _ := by dsimp only [F]; linarith only [mul_nonneg hA hs]
  have hlateVertex : vertex (u / rate ka) ≤ F * s := by
    calc
      _ ≤ 16 * (u / rate ka) ^ 4 := hvertex _ (by positivity)
      _ ≤ (64 / rate ka ^ 4) * s := by
        rw [div_pow]
        have hh := mul_le_mul_of_nonneg_left hus (div_nonneg (by norm_num : (0 : ℝ) ≤ 16)
          (pow_nonneg hr.le 4))
        convert hh using 1 <;> ring
      _ ≤ _ := by dsimp only [F]; linarith only [mul_nonneg hA hs]
  have hlatePrep : latePrep ≤ F * s := by
    have hr := hrow u hu
    have hpr : (p / 63) ^ 4 ≤ p ^ 4 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith only [hp]
    have h1 : (P : ℝ) * (p / 63) ^ 4 ≤ 4 * s :=
      (mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg P)).trans hpp
    have h2 : (P : ℝ) * row u ≤ 64 * s := by
      have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg P)
      linarith only [hh, hPs]
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (mul_nonneg hA (by norm_num : (0 :
      ℝ) ≤ 8))
    dsimp only [latePrep, F]
    linarith only [hh, mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 64) (pow_nonneg
      (rate_pos ka).le 4)) hs]
  have hearly (v : ℝ) (hv : 0 ≤ v) (hvb : v ≤ b / rate ka) :
      row v ≤ E * (P : ℝ) ^ 2 ∧ vertex v ≤ E * (P : ℝ) ^ 2 := by
    have hbc : 0 ≤ 16 * b ^ 4 / rate ka ^ 4 := by positivity
    have hE' : 16 * b ^ 4 / rate ka ^ 4 ≤ E := by
      dsimp only [E]
      exact le_add_of_nonneg_right (by positivity)
    have hpow := pow_le_pow_left₀ hv hvb 4
    have hpow16 : 16 * v ^ 4 ≤ 16 * b ^ 4 / rate ka ^ 4 := by
      rw [div_pow] at hpow
      convert mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 16) using 1; ring
    constructor
    · calc
        _ ≤ 16 * P * v ^ 4 := hrow v hv
        _ ≤ (16 * b ^ 4 / rate ka ^ 4) * (P : ℝ) := by
          convert mul_le_mul_of_nonneg_right hpow16 (Nat.cast_nonneg P) using 1; ring
        _ ≤ (16 * b ^ 4 / rate ka ^ 4) * (P : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hPP hbc
        _ ≤ _ := mul_le_mul_of_nonneg_right hE' (by positivity)
    · exact (hvertex v hv).trans (hpow16.trans
        ((le_mul_of_one_le_right hbc (one_le_pow₀ hP1)).trans
          (mul_le_mul_of_nonneg_right hE' (by positivity))))
  have hearlyPrep : earlyPrep ≤ E * (P : ℝ) ^ 2 := by
    have hpr : (p / 63) ^ 4 ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      linarith only [hp1]
    have h1 : (P : ℝ) * (p / 63) ^ 4 ≤ (P : ℝ) ^ 2 := by
      linarith only [mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg P), hPP]
    have h2 : (P : ℝ) * row (u + inactive) ≤ 16 * b ^ 4 * (P : ℝ) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left (hrow _ (add_nonneg hu hinactive0)) (Nat.cast_nonneg P)
      have hpow := pow_le_pow_left₀ (add_nonneg hu hinactive0) hub 4
      linarith only [hh, mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 16 * (P : ℝ)
        ^ 2)]
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (mul_nonneg hA (by norm_num : (0 :
      ℝ) ≤ 8))
    dsimp only [earlyPrep, E]
    linarith only [hh, mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * b ^ 4 / rate ka ^ 4)
      (pow_nonneg (Nat.cast_nonneg P) 2)]
  have hprep0 (i : ℕ) : 0 ≤ prep i := by
    have hh := hrow0 (u + B.initialInactiveCharge M i r)
    dsimp only [prep]; positivity
  have hprep (i : ℕ) : prep i ≤ earlyPrep := by
    have hd1 := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by norm_num : (1 / 64 : ℝ) ≤ 1) (dyadicSlack_pos m i)
    simp only [pow_one] at hd1
    have hpn : p * (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack m i ≤ p / 63 := by
      linarith only [mul_le_mul_of_nonneg_left hd1 (mul_nonneg hp (by norm_num : (0 : ℝ) ≤ 64 /
        63))]
    have hmono : row (u + B.initialInactiveCharge M i r) ≤ row (u + inactive) := by
      apply (rowNormPow_le_mul (by positivity) (c := 1) ?_).trans_eq (one_mul _)
      intro σ x y _ _
      rw [one_mul, abs_of_nonneg (add_nonneg hu (hcharge0 i)), abs_of_nonneg (add_nonneg hu
        hinactive0)]
      exact pow_le_pow_left₀ (add_nonneg hu (hcharge0 i)) (add_le_add le_rfl (hcharge i)) 4
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (pow_le_pow_left₀ (by positivity) hpn 4) hmono)
      (by positivity : (0 : ℝ) ≤ (P : ℝ) * A * 8)
    rw [hprep_eq]
    dsimp only [earlyPrep]
    linarith only [hh]
  have hprepLate (i : ℕ) (hi : i ≠ 0) : prep i ≤ latePrep := by
    have hd1 := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by norm_num : (1 / 64 : ℝ) ≤ 1) (dyadicSlack_pos m i)
    simp only [pow_one] at hd1
    have hpn : p * (64 / 63) * (1 / 64 : ℝ) ^ dyadicSlack m i ≤ p / 63 := by
      linarith only [mul_le_mul_of_nonneg_left hd1 (mul_nonneg hp (by norm_num : (0 : ℝ) ≤ 64 /
        63))]
    rw [hprep_eq]
    dsimp only [latePrep]
    rw [hz i hi, add_zero]
    linarith only [mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hpn 4)
      (by positivity : (0 : ℝ) ≤ (P : ℝ) * A * 8)]
  have haLate (i : ℕ) (hi : i ≠ 0) : a i ≤ 2 * f * t := by
    have hq : q i = u / rate ka := by dsimp only [q, initialMeanCharge]; rw [hz i hi, add_zero]
    have hv := root_bound (hvertex0 _) hF hs hlateVertex
    have hp := root_bound (hprep0 i) hF hs ((hprepLate i hi).trans hlatePrep)
    dsimp only [a]
    rw [hq]
    change _ ≤ f * t at hv hp
    linarith only [hv, hp]
  have haEarly (w : ℝ) (hw : 0 ≤ w) (hwP : w ^ 4 * (P : ℝ) ^ 2 ≤ 4 * s) :
      w * a 0 ≤ 2 * e * t := by
    have hb1 := mul_le_mul_of_nonneg_left (hearly _ (hq0 0) (hqbound 0)).2 (pow_nonneg hw 4)
    have hb2 := mul_le_mul_of_nonneg_left ((hprep 0).trans hearlyPrep) (pow_nonneg hw 4)
    have hb3 := mul_le_mul_of_nonneg_left hwP hE
    have h1 : w ^ 4 * vertex (q 0) ≤ (4 * E) * s := by linarith only [hb1, hb3]
    have h2 : w ^ 4 * prep 0 ≤ (4 * E) * s := by linarith only [hb2, hb3]
    have hr1 := weighted_root_bound (hvertex0 _) hw (by positivity : 0 ≤ 4 * E) hs h1
    have hr2 := weighted_root_bound (hprep0 0) hw (by positivity : 0 ≤ 4 * E) hs h2
    dsimp only [a]
    change _ ≤ e * t at hr1 hr2
    linarith only [hr1, hr2]
  have hstationary : (∑ i ∈ range m, dyadicFloor floor m i * a i) ≤
      floor * (2 * f + 2 * e) * t := by
    let w := (1 / 1024 : ℝ) ^ dyadicSlack m 0
    have hw : 0 ≤ w := by dsimp only [w]; positivity
    have hwP : w ^ 4 * (P : ℝ) ^ 2 ≤ 4 * s := by
      dsimp only [w]
      rw [← pow_mul, Nat.mul_comm _ 4, pow_mul]
      exact decay_width (by norm_num) (by norm_num) P n _ hP hd
    exact stationary_root_payment hf hf0 ht m (by dsimp only [m]; omega) a haLate
      (haEarly w hw hwP)
  have hlog : Nat.log2 M ≠ 0 := by
    have hh : 1 ≤ Nat.log2 M := by
      exact (Nat.le_log2 (by omega : M ≠ 0)).mpr (by simpa using (show 2 ≤ M by omega))
    omega
  have hfinal := haLate (Nat.log2 M) hlog
  have hnoiseT : p * (64 / 63) / rate ka + |ζ| * p' ≤ noise * t := by
    have hv4 : ((1 / 4 : ℝ) ^ n) ^ 4 ≤ s := by
      rw [← pow_mul, Nat.mul_comm n 4, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hv := Real.rpow_le_rpow (pow_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n) 4)
      hv4 (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rw [fourth_root_pow (by positivity)] at hv
    have h0 := mul_le_mul_of_nonneg_right (hp_le.trans hv)
      (by positivity : (0 : ℝ) ≤ (64 / 63) / rate ka)
    have h1 := mul_le_mul_of_nonneg_left (hp'_le.trans hv) (abs_nonneg ζ)
    change p * ((64 / 63) / rate ka) ≤ t * ((64 / 63) / rate ka) at h0
    change |ζ| * p' ≤ |ζ| * t at h1
    dsimp only [noise]
    simpa only [mul_div_assoc, add_mul, mul_comm t] using add_le_add h0 h1
  have htail : Q * ((row (u / rate ka)) ^ (4⁻¹ : ℝ) + latePrep ^ (4⁻¹ : ℝ)) / 63 +
      (((2 + 256 / dyadicFloor floor m 0) / (compatibleCapacity HP.K m 0 : ℝ)) ^
        (4⁻¹ : ℝ)) * 28 ^ m *
        ((row ((u + inactive) / rate ka)) ^ (4⁻¹ : ℝ) + earlyPrep ^ (4⁻¹ : ℝ)) ≤
      (Q * (2 * f) / 63 + Q * (2 * e)) * t := by
    let w := (1 / 64 : ℝ) ^ dyadicSlack m 0
    have hw : 0 ≤ w := by dsimp only [w]; positivity
    have hwP : w ^ 4 * (P : ℝ) ^ 2 ≤ 4 * s := by
      dsimp only [w]
      rw [← pow_mul, Nat.mul_comm _ 4, pow_mul]
      exact decay_width (by norm_num) (by norm_num) P n _ hP hd
    exact tail_root_payment (hrow0 _) (mul_nonneg (by positivity)
      (add_nonneg (by positivity) (hrow0 _))) (hrow0 _)
      (mul_nonneg (by positivity) (add_nonneg (by positivity) (hrow0 _)))
      hF hE hs hw hQ hlateRow hlatePrep
      (hearly _ (by positivity) (div_le_div_of_nonneg_right hub hr.le)).1 hearlyPrep hwP
      (compatible_first_rarity_decay hf HP.K m (by dsimp only [m]; omega))
  have hfalse :
      (64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m 0 : ℝ) * dyadicFloor floor m 0 ^ 4)) *
        (row ((u + inactive) / rate ka) + earlyPrep) ≤ c * (8 * E) * s := by
    let w := 64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m 0 : ℝ) * dyadicFloor floor m 0 ^ 4)
    have hw : 0 ≤ w := by dsimp only [w]; positivity
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add (hearly _ (by positivity)
        (div_le_div_of_nonneg_right hub (rate_pos ka).le)).1 hearlyPrep) hw
    have hh := compatible_first_false_width hf HP.K m P n radius hP hd
    have hh' : w * (P : ℝ) ^ 2 ≤ c * 4 * s := hh.trans (by
      dsimp only [c, s]; gcongr; norm_num)
    have he := mul_le_mul_of_nonneg_left hh' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE)
    linarith only [hb, he]
  have hp40 : (p * (64 / 63) / rate ka) ^ 4 ≤ noise ^ 4 * s := by
    apply (pow_le_pow_left₀ (by positivity)
      ((le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ |ζ| * p')).trans hnoiseT) 4).trans_eq
    rw [mul_pow, ht4]
  have hp41 : (|ζ| * p') ^ 4 ≤ noise ^ 4 * s := by
    apply (pow_le_pow_left₀ (by positivity)
      ((le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ p * (64 / 63) / rate ka)).trans
        hnoiseT) 4).trans_eq
    rw [mul_pow, ht4]
  unfold initialGeometricRHS
  have hcancel : (p * (64 / 63) / rate ka) * rate ka / 64 = p / 63 := by
    field_simp
  change 128 * (HP.K : ℝ) *
    (Cpre ^ 4 * ((∑ i ∈ range m, dyadicFloor floor m i * a i) +
      floor * (p * (64 / 63) / rate ka + |ζ| * p') / 511) ^ 4 +
    C ^ 4 * (a (Nat.log2 M) + (p * (64 / 63) / rate ka + |ζ| * p') / 64) ^ 4 +
    C ^ 4 * ((Q * ((row (u / rate ka)) ^ (4⁻¹ : ℝ) +
      ((P : ℝ) * A * 8 * (((p * (64 / 63) / rate ka) * rate ka / 64) ^ 4 + row u)) ^ (4⁻¹ : ℝ))
        / 63 +
      (((2 + 256 / dyadicFloor floor m 0) / (compatibleCapacity HP.K m 0 : ℝ)) ^ (4⁻¹ : ℝ)) *
        28 ^ m * ((row ((u + inactive) / rate ka)) ^ (4⁻¹ : ℝ) +
        ((P : ℝ) * A * 8 * (((p * (64 / 63) / rate ka) * rate ka / 64) ^ 4 + row (u +
          inactive))) ^ (4⁻¹ : ℝ))) +
        (p * (64 / 63) / rate ka + |ζ| * p') * (7 / 9)) ^ 4) +
    64 * (c * (row (u / rate ka) +
      (P : ℝ) * A * 8 * (((p * (64 / 63) / rate ka) * rate ka / 64) ^ 4 + row u)) / 63 +
      (64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m 0 : ℝ) * dyadicFloor floor m 0 ^ 4)) *
        (row ((u + inactive) / rate ka) +
        (P : ℝ) * A * 8 * (((p * (64 / 63) / rate ka) * rate ka / 64) ^ 4 + row (u + inactive))) +
      (c * (p * (64 / 63) / rate ka) ^ 4 / 63 + c * (|ζ| * p') ^ 4 / 63)) ≤ D * s
  rw [hcancel]
  have hS : (∑ i ∈ range m, dyadicFloor floor m i * a i) +
      floor * (p * (64 / 63) / rate ka + |ζ| * p') / 511 ≤ S * t := by
    have hh := mul_le_mul_of_nonneg_left hnoiseT hf.le
    dsimp only [S]
    linarith only [hstationary, hh]
  have hFinal : a (Nat.log2 M) + (p * (64 / 63) / rate ka + |ζ| * p') / 64 ≤
      (2 * f + noise / 64) * t := by linarith only [hfinal, hnoiseT]
  have hTail := add_le_add htail (mul_le_mul_of_nonneg_right hnoiseT (by norm_num : (0 : ℝ) ≤ 7
    / 9))
  have hTailEq : (Q * (2 * f) / 63 + Q * (2 * e)) * t + noise * t * (7 / 9) = T * t := by
    dsimp only [T]; ring
  rw [hTailEq] at hTail
  have ha0 (i : ℕ) : 0 ≤ a i := add_nonneg
    (Real.rpow_nonneg (hvertex0 _) _) (Real.rpow_nonneg (hprep0 _) _)
  have hS4 := pow_le_pow_left₀ (by
    exact add_nonneg (sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf.le _ _) (ha0 i))
      (by positivity)) hS 4
  have hFinal4 := pow_le_pow_left₀ (by
    exact add_nonneg (ha0 _) (by positivity) : 0 ≤ a (Nat.log2 M) +
    (p * (64 / 63) / rate ka + |ζ| * p') / 64) hFinal 4
  have hTail0 : 0 ≤ Q * ((row (u / rate ka)) ^ (4⁻¹ : ℝ) + latePrep ^ (4⁻¹ : ℝ)) / 63 +
      (((2 + 256 / dyadicFloor floor m 0) / (compatibleCapacity HP.K m 0 : ℝ)) ^ (4⁻¹ : ℝ)) *
      28 ^ m * ((row ((u + inactive) / rate ka)) ^ (4⁻¹ : ℝ) + earlyPrep ^ (4⁻¹ : ℝ)) +
      (p * (64 / 63) / rate ka + |ζ| * p') * (7 / 9) := by
    have hdf := dyadicFloor_pos hf m 0
    have hr0 := hrow0 (u / rate ka)
    have hr1 := hrow0 ((u + inactive) / rate ka)
    have hp0 : 0 ≤ latePrep := mul_nonneg (by positivity) (add_nonneg (by positivity) (hrow0 _))
    have hp1 : 0 ≤ earlyPrep := mul_nonneg (by positivity) (add_nonneg (by positivity) (hrow0 _))
    positivity
  have hTail4 := pow_le_pow_left₀ hTail0 hTail 4
  have hraw := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hlateRow hlatePrep) hc)
      (mul_le_mul_of_nonneg_left hp40 hc)) (mul_le_mul_of_nonneg_left hp41 hc)
  rw [mul_pow, ht4] at hS4 hFinal4 hTail4
  have h1 := mul_le_mul_of_nonneg_left hS4 (by positivity : 0 ≤ Cpre ^ 4)
  have h2 := mul_le_mul_of_nonneg_left hFinal4 (by positivity : 0 ≤ C ^ 4)
  have h3 := mul_le_mul_of_nonneg_left hTail4 (by positivity : 0 ≤ C ^ 4)
  have h4 := mul_le_mul_of_nonneg_left hlateRow hc
  have h5 := mul_le_mul_of_nonneg_left hlatePrep hc
  have h6 := mul_le_mul_of_nonneg_left hp40 hc
  have h7 := mul_le_mul_of_nonneg_left hp41 hc
  have h123 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3)
    (by positivity : (0 : ℝ) ≤ 128 * (HP.K : ℝ))
  let sa := (∑ i ∈ range m, dyadicFloor floor m i * a i) +
    floor * (p * (64 / 63) / rate ka + |ζ| * p') / 511
  let fa := a (Nat.log2 M) + (p * (64 / 63) / rate ka + |ζ| * p') / 64
  let ta := Q * ((row (u / rate ka)) ^ (4⁻¹ : ℝ) + latePrep ^ (4⁻¹ : ℝ)) / 63 +
    (((2 + 256 / dyadicFloor floor m 0) / (compatibleCapacity HP.K m 0 : ℝ)) ^ (4⁻¹ : ℝ)) *
      28 ^ m * ((row ((u + inactive) / rate ka)) ^ (4⁻¹ : ℝ) + earlyPrep ^ (4⁻¹ : ℝ)) +
      (p * (64 / 63) / rate ka + |ζ| * p') * (7 / 9)
  let w := 64 * (HP.K : ℝ) * radius ^ 4 /
    ((compatibleCapacity HP.K m 0 : ℝ) * dyadicFloor floor m 0 ^ 4)
  change 128 * (HP.K : ℝ) * (Cpre ^ 4 * sa ^ 4 + C ^ 4 * fa ^ 4 + C ^ 4 * ta ^ 4) +
    64 * (c * (row (u / rate ka) + latePrep) / 63 +
      w * (row ((u + inactive) / rate ka) + earlyPrep) +
      (c * (p * (64 / 63) / rate ka) ^ 4 / 63 + c * (|ζ| * p') ^ 4 / 63)) ≤ D * s
  change 128 * (HP.K : ℝ) * (Cpre ^ 4 * sa ^ 4 + C ^ 4 * fa ^ 4 + C ^ 4 * ta ^ 4) ≤ _ at h123
  change w * (row ((u + inactive) / rate ka) + earlyPrep) ≤ _ at hfalse
  dsimp only [D]
  linarith only [h123, h4, h5, hfalse, h6, h7]

/-- Uniform arbitrary accuracy for the complete computed RHS, with all fixed constants
chosen first. Every admissible prime and input at every sufficiently large depth is covered. -/
theorem initialGeometricRHS_uniform_small (ks ka : ℕ) (ζ floor Lh Lρ C Cpre cap : ℝ)
    (hf : 0 < floor) (hcap : 0 ≤ cap) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (P n M : ℕ) [Fact P.Prime] (B : BudgetData HP P),
      N ≤ n →
      1 < M → n ≤ dyadicSlack (Nat.log2 M + 1) 0 →
      P ≤ 2 ^ (n + 1) → B.bins = range (n + 1) → B.binRate = rate → B.binCap ≤ cap →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      (∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale { r with usage := r.terminal } (some bin)) < M) →
      2 * (n : ℝ) ≤ B.requestPrecision M { r with usage := r.terminal } →
      2 * (n : ℝ) ≤ B.requestPrecision M r →
      ∀ (H : Horizon P), ks ≤ H.maxExponent →
      ∀ (R : RoleProfile 3) (ss st : List (ZMod P)),
      B.initialGeometricRHS M n r R ks ka ss st ζ floor Lh Lρ C Cpre ≤
        ε := by
  obtain ⟨D, hD, hbound⟩ := initialGeometricRHS_uniform (HP := HP) ks ka ζ floor Lh Lρ C Cpre
    cap hf hcap
  intro ε hε
  have hlim : Filter.Tendsto (fun n : ℕ => D * (1 / 64 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨N, ?_⟩
  intro P n M _ B hn hM hd hP hbins hrate hBC r hcut hp0 hp1 H hks R ss st
  exact (hbound P n M B hM hd hP hbins hrate hBC r hcut hp0 hp1 H hks R ss st).trans
    (hN n hn).le

private lemma linear_firstSlack (c n : ℕ) (hc : 0 < c) :
    n ≤ dyadicSlack (Nat.log2 (128 * c * n) + 1) 0 := by
  have hh : 128 * c * n < 2 * 2 ^ Nat.log2 (128 * c * n) := by
    simpa only [Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) (128 * c * n)
  have hn := Nat.mul_le_mul_right n (show 2 ≤ 128 * c by omega)
  simp only [dyadicSlack, Nat.add_sub_cancel]
  omega

/-- Fix the slack and an upper bound on the structural charge before choosing depth.
Both literal request precisions and every retained scale cutoff are then admissible uniformly
in the prime and base matrix. Usage exponents do not enter either precision. -/
theorem fixed_charge_linear_guards (ks ka c : ℕ) (rankCost : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ (P n : ℕ) (B : BudgetData HP P), N ≤ n → B.slack = c →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.source.rate = rate ks → r.terminal.rate = rate ka →
      B.rankCharge * r.task.rank ≤ rankCost →
      let M := 128 * c * n
      1 < M ∧ B.slack * (1 + 4 * (n + ka)) < M ∧
      2 * (n : ℝ) ≤ B.requestPrecision M r ∧
      2 * (n : ℝ) ≤ B.requestPrecision M { r with usage := r.terminal } := by
  obtain ⟨b, hb⟩ := exists_nat_gt (2 * ((ka : ℝ) + ks) + rankCost)
  refine ⟨max (max 1 ka) b, ?_⟩
  intro P n B hn hslack r hs ht hcharge
  have hn1 : 1 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hka : ka ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hbn : b ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcost : 2 * ((ka : ℝ) + ks) + rankCost ≤ n := hb.le.trans (by exact_mod_cast hbn)
  have hM : 1 < 128 * c * n := by nlinarith only [hc, hn1]
  have hbudget : B.slack * (1 + 4 * (n + ka)) < 128 * c * n := by
    rw [hslack]
    nlinarith only [hc, hn1, hka]
  have hprec : 2 * (n : ℝ) ≤ B.requestPrecision (128 * c * n) r := by
    rw [B.requestPrecision_grid _ ks ka r hs ht, hslack]
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have he : ((128 * c * n : ℕ) : ℝ) / (16 * c) = 8 * n := by
      push_cast
      field_simp
      ring
    rw [he]
    linarith only [hcost, hcharge, hn0]
  exact ⟨hM, hbudget, hprec, hprec⟩

/-- Arbitrary accuracy of every successful actual compressed-bin output at sufficiently
large linear budget. C is fixed before the floor, Cpre after the floor, and both before depth
or prime. Fixed slack and structural charge pay the actual precision and scale guards.
The output and both actual histories are constructed, and its dense target is the actual
positive-budget dense constructor of `evaluate`; the recursive lower-budget invariant
and general/noninitial evaluator dispatch remain separate. -/
theorem exists_compressedBin_uniform_accuracy (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hscl : 0 < scale)
    (hmargin : scale ≤ HP.η) (hcapscale : scale ≤ max (1 : ℝ) 16 / 10000)
    (hsmall : ζ ≤ scale / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor : ℝ, 0 < floor → floor ≤ scale → floor ≤ 1 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ (ks ka c : ℕ) (rankCost cap Lh Lρ : ℝ), 0 < c → 0 ≤ cap →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
      (n : ℕ), N ≤ n → P ≤ 2 ^ (n + 1) →
      B.bins = range (n + 1) → B.binRate = rate → B.binCap ≤ cap → B.slack = c →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      B.auxiliary = (fun _ => polynomialPrepCutoff4 HP.θ) → B.padding ≠ 0 →
      ∀ (H : Horizon P), n ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), Admissible r →
      B.rankCharge * r.task.rank ≤ rankCost →
      ∀ (R : RoleProfile 3) (ku : ℕ) (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      r.usage = gridChannel R.terminal ku st → ks ≤ H.maxExponent → ka ≤ H.maxExponent → ka ≤ ku →
      let M := 128 * c * n
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      ∀ (bin : ℕ), 0 ≤ Lh → 0 ≤ Lρ →
      (∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|) →
      (∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|) →
      ∃ A, B.compressedBin M bin ka ζ floor r = some A ∧
      rootDistPow 4 P (rate ks)
        (retainedMask R.source (side P ks) B.padding ss)
        (retainedMask R.terminal (side P ka) B.padding st) A
        (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K
          B.base) ≤ ε ∧
        B.evaluate M {r with task := .baseNormalized 0 bin} = some (.row
          (denseChild B.padding id r (B.cutoff bin) (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K
            B.base)) := by
  obtain ⟨C, hC, hfloor⟩ := exists_compressedBin_geometric HP hζ hscl hmargin hcapscale hsmall
  refine ⟨C, hC, ?_⟩
  intro floor hf hfs hf1
  obtain ⟨Cp, hCp, houtput⟩ := hfloor floor hf hfs hf1
  refine ⟨Cp, hCp, ?_⟩
  intro ks ka c rankCost cap Lh Lρ hc hcap ε hε
  obtain ⟨N, hN⟩ := initialGeometricRHS_uniform_small (HP := HP) ks ka ζ floor Lh Lρ C Cp cap
    hf hcap ε hε
  obtain ⟨Ng, hguard⟩ := fixed_charge_linear_guards (HP := HP) ks ka c rankCost hc
  refine ⟨max N Ng, ?_⟩
  intro P _ B n hn hP hbins hrate hBC hslack hcutoff haux hD H hdepth r hr hcharge R ku ss st
    hsource hterminal husage hks hka hku
  dsimp only
  intro hbase hbase1 bin hLh hLρ hh hρ
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnG : Ng ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hM, hbudget, hp1, hp0⟩ := hguard P n B hnG hslack r
    (by simp only [hsource, gridChannel]) (by simp only [hterminal, gridChannel]) hcharge
  have hsc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < 128 * c * n := by
    intro bin hi
    have hb : bin ≤ n := by rw [hbins, mem_range] at hi; omega
    exact B.retained_scaleCutoff_lt { r with usage := r.terminal } _ n ka hrate
      (by simp only [hterminal, gridChannel]) hbudget bin hb
  have hroles : R.source ≠ R.terminal := by
    simpa only [hsource, hterminal, gridChannel] using hr.1
  obtain ⟨F, hF⟩ : ∃ F, B.initialPrefixes (128 * c * n) r = some F :=
    ⟨_, (B.initialPrefixes_grid _ (by omega) (by rw [hbins]; exact nonempty_range_iff.mpr (by
      omega))
      r R.source R.terminal hroles ks ka ss st hsource hterminal).1⟩
  have hw (i : ℕ) : ∃ A, B.complete (128 * c * n) r
      (B.binPreparation bin r (F (i + 1))) (dyadicSlack (Nat.log2 (128 * c * n) + 1) i) = some A :=
    ⟨_, B.complete_grid _ r R.source R.terminal hroles ks ku ss st hsource husage _ _⟩
  choose walks hwalk using hw
  have hW : (List.range (Nat.log2 (128 * c * n) + 1)).mapM (fun i =>
      B.complete (128 * c * n) r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 (128 * c * n) + 1) i)) =
      some ((List.range (Nat.log2 (128 * c * n) + 1)).map walks) := by
    simp_rw [hwalk]
    exact List.mapM_pure
  have hp : 0 < B.requestPrecision (128 * c * n) r := by
    have hn0 : (0 : ℝ) < n := by
      have hnpos : 0 < n := by
        by_contra hz
        have hnzero : n = 0 := by omega
        simp [hnzero] at hM
      exact_mod_cast hnpos
    linarith only [hp1, hn0]
  obtain ⟨A, hA⟩ : ∃ A, B.compressedBin (128 * c * n) bin ka ζ floor r = some A := by
    unfold compressedBin
    rw [ite_eq_right (by simp only [show 128 * c * n ≠ 0 by omega, hp, not_true_eq_false,
      false_or, hterminal, gridChannel, ne_eq, not_false_eq_true])]
    simp only [hF, bind, Option.bind_some]
    rw [hW]
    exact ⟨_, rfl⟩
  refine ⟨A, hA, ?_, ?_⟩
  · exact (houtput B _ n hM hbins hrate hcutoff haux hD H hdepth r hr R ks ka ku ss st
      hsource hterminal husage hks hka hku hbudget hbase hbase1 bin F hF _ hW A hA
      Lh Lρ hLh hLρ hh hρ).trans
        (hN P n _ B hnN hM (linear_firstSlack c n hc) hP hbins hrate hBC
          r hsc hp0 hp1 H hks R ss st)
  · simpa only [haux, denseChild_congr_task] using B.evaluate_dense _ bin (by omega)
      {r with task := .baseNormalized 0 bin} rfl

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
