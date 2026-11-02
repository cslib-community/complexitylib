/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.TimeBound
public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicCost.Asymptotics
public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Exec
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A content-independent natural allowance for callable dyadic solving

The natural function depends only on original dimension n and original weight bound F. A
selected-prime logarithmic estimate and the actual wrapper charges bound the real parameter,
selector and callable ledger, including header/halt reserve. This is a mathematical time bound;
the program does not compute it or receive a time certificate. Small-branch execution and
actual program assembly remain separate.

## Main definitions

* `dyadicTime`: natural allowance for the complete fast ledger, independent of input contents,
  reference memory, layout and physical width.

## Main results

* `timeBound_le_dyadicTime`: the actual charged fast ledger is bounded at every selected prime.
* `exists_dyadicTime_subcubic_bound`: uniform strict-subcubic growth for polynomial original F.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Filter Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open ParameterChoice

private noncomputable def weightExponent (n F : ℕ) : ℝ :=
  1 + Real.logb n (F + 1)

private def setupLog (n F : ℕ) : ℕ :=
  Nat.clog 2 (4 * n + 3 * (n * n) * (2 * F + 1) + 4)

private noncomputable def upperTime (n F : ℕ) : ℝ :=
  3 * DyadicCost.costCoefficient (weightExponent n F) n * ((n : ℝ) ^ 3 / groups n) +
    24 * (n : ℝ) ^ 2 + 24669 * (setupLog n F : ℝ) + 497

/-- Natural fast-ledger allowance from original n and F only. The ceiling is descriptive
metadata, not an executed instruction or an oracle supplied to the native solver. The final
sixteen reserve the assembled initialized header and halt. -/
noncomputable def dyadicTime (n F : ℕ) : ℕ := ⌈upperTime n F⌉₊ + 16

private theorem one_le_weightExponent {n : ℕ} (hn : 2 ≤ n) (F : ℕ) :
    1 ≤ weightExponent n F := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hF : 0 ≤ Real.log (F + 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ F + 1))
  have hdiv := div_nonneg hF hlog.le
  unfold weightExponent Real.logb
  linarith only [hdiv]

private theorem bound_le_rpow_weightExponent {n : ℕ} (hn : 2 ≤ n) (F : ℕ) :
    (F : ℝ) ≤ (n : ℝ) ^ weightExponent n F := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (n : ℝ) ≠ 1 := by exact_mod_cast (by omega : n ≠ 1)
  rw [weightExponent, Real.rpow_add hn0, Real.rpow_one,
    Real.rpow_logb hn0 hn1 (by positivity)]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  nlinarith

private theorem original_weights {n F : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F) :
    WeightsBoundedBy
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (F : ℝ) := by
  have hlookup (q : ℕ) : (values.getD q 0).natAbs ≤ F := by
    by_cases hq : q < 3 * (n * n)
    · exact RecordWitness.original_magnitude values hlen hv hq
    · rw [List.getD_eq_default values 0 (by omega : values.length ≤ q), Int.natAbs_zero]
      exact Nat.zero_le F
  have hw (q : ℕ) : ((|values.getD q 0| : ℤ) : ℝ) ≤ F := by
    rw [← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast hlookup q
  exact ⟨fun _ _ => hw _, fun _ _ => hw _, fun _ _ => hw _⟩

private theorem scalar_bounds {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ Nat.sqrtPrimeWindow (window n)) :
    window n ≤ n ∧ groups n ≤ n ∧ p ≤ n := by
  have hd := window_le hn
  have hsq := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).2.2
  exact ⟨hd, (groups_le_window n).trans hd,
    (Nat.le_self_pow (by decide : 2 ≠ 0) p).trans (hsq.le.trans hd)⟩

/-- Bound the actual fast initialized ledger, including all copies, setup, dispatch/restore,
header and halt. All original matrices bounded by F share this same natural function. The
prime is actually selected; no layout, execution or time law is a premise. -/
theorem timeBound_le_dyadicTime {n F p : ℕ} (hf : 0 < blocks n) (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hp : IsSelectedPrime
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p)
    (mem : ℕ → ℕ) :
    DyadicParameters.timeBound n + PrimeSelection.timeBound n (window n) +
        timeBound (m := level n) (pos_of_blocks_pos hf) (groups n) p values mem + 42 ≤
      dyadicTime n F := by
  have hn := pos_of_blocks_pos hf
  obtain ⟨hd, hg, hpN⟩ := scalar_bounds hn hp.1
  have hn2 : 2 ≤ n := by have h := (window_ge_sixteen hf).trans hd; omega
  have hexp := bound_le_rpow_weightExponent hn2 F
  obtain ⟨hab, hbc, hac⟩ := original_weights values hlen hv
  have hv' : WeightsBoundedBy
      (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
      (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
      (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0)
      ((n : ℝ) ^ weightExponent n F) :=
    ⟨fun _ _ => (hab _ _).trans hexp, fun _ _ => (hbc _ _).trans hexp,
      fun _ _ => (hac _ _).trans hexp⟩
  have hc := DyadicCost.components_timeBound_le hf (one_le_weightExponent hn2 F) values mem hv' hp
  change (_ : ℝ) ≤ DyadicCost.costCoefficient (weightExponent n F) n *
    ((n : ℝ) ^ 3 / groups n) at hc
  have hraw := rawTotal_le values hlen hv
  have hlog : Nat.clog 2 (n + window n + groups n + p + rawTotal n values + 4) ≤ setupLog n F :=
    Nat.clog_mono_right 2 (by omega)
  have hparam := DyadicParameters.timeBound_le n
  have hnat : DyadicParameters.timeBound n + PrimeSelection.timeBound n (window n) +
      timeBound (m := level n) hn (groups n) p values mem + 42 ≤
    3 * (12 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
      FixedPrime.timeBound (m := level n) hn (groups n) p values mem) +
        24 * (n * n) + 24669 * setupLog n F + 497 + 16 := by
    unfold timeBound
    dsimp only [D, window] at *
    nlinarith only [hlog, hparam]
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  have hceil : upperTime n F ≤ (⌈upperTime n F⌉₊ : ℝ) := Nat.le_ceil _
  apply (Nat.cast_le (α := ℝ)).mp
  unfold dyadicTime
  push_cast at hreal hc ⊢
  unfold upperTime at hceil ⊢
  nlinarith only [hreal, hc, hceil]

private theorem setupLog_le_log {n F κ : ℕ} (hF : F ≤ (n + 2) ^ κ) :
    setupLog n F ≤ (κ + 7) * Nat.clog 2 (n + 2) := by
  let B := n + 2
  have hb : 2 ≤ B := by dsimp only [B]; omega
  have hb1 : 1 ≤ B := by omega
  have hnB : n ≤ B := by dsimp only [B]; omega
  have hn2 : n * n ≤ B ^ 2 := (Nat.mul_le_mul hnB hnB).trans_eq (by ring)
  have hunit : 1 ≤ B ^ κ := Nat.one_le_pow _ _ hb1
  have hcoef : 2 * F + 1 ≤ 3 * B ^ κ := by
    have : F ≤ B ^ κ := hF
    omega
  have hterm : 3 * (n * n) * (2 * F + 1) ≤ 9 * B ^ (κ + 2) := by
    calc
      _ ≤ (3 * B ^ 2) * (3 * B ^ κ) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 hn2) hcoef
      _ = _ := by rw [pow_add]; ring
  have hB : B ≤ B ^ (κ + 2) := Nat.le_self_pow (by omega) _
  have hlinear : 4 * n + 4 ≤ 8 * B ^ (κ + 2) := by nlinarith only [hnB, hb1, hB]
  have hsum : 4 * n + 3 * (n * n) * (2 * F + 1) + 4 ≤ 17 * B ^ (κ + 2) := by
    omega
  have h17 : 17 ≤ B ^ 5 := (by decide : 17 ≤ (2 : ℕ) ^ 5).trans
    (Nat.pow_le_pow_left hb 5)
  have hpoly : 4 * n + 3 * (n * n) * (2 * F + 1) + 4 ≤ B ^ (κ + 7) := by
    calc
      _ ≤ 17 * B ^ (κ + 2) := hsum
      _ ≤ B ^ 5 * B ^ (κ + 2) := Nat.mul_le_mul_right _ h17
      _ = _ := by rw [← pow_add]; congr 1; omega
  have h := hpoly.trans (Nat.pow_le_pow_left
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) B) (κ + 7))
  rw [← pow_mul, Nat.mul_comm (Nat.clog 2 B) (κ + 7)] at h
  exact Nat.clog_le_of_le_pow h

private theorem weightExponent_le {n F κ : ℕ} (hn : 2 ≤ n) (hF : F ≤ (n + 2) ^ κ) :
    weightExponent n F ≤ (2 * κ + 2 : ℕ) := by
  have hpow : F ≤ n ^ (2 * κ) :=
    hF.trans ((Nat.pow_le_pow_left (by nlinarith : n + 2 ≤ n ^ 2) κ).trans_eq
      (by rw [← pow_mul]))
  have hunit : 1 ≤ n ^ (2 * κ) := Nat.one_le_pow _ _ (by omega)
  have hF1 : F + 1 ≤ n ^ (2 * κ + 1) := by
    rw [pow_succ]
    nlinarith only [hpow, hunit, hn]
  have hF1R : (F + 1 : ℝ) ≤ (n : ℝ) ^ ((2 * κ + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hF1
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := (Real.logb_le_iff_le_rpow hnR (by positivity : (0 : ℝ) < F + 1)).mpr hF1R
  unfold weightExponent
  push_cast at hlog ⊢
  linarith only [hlog]

private theorem upperTime_nonneg {n : ℕ} (hn : 2 ≤ n) (F : ℕ) : 0 ≤ upperTime n F := by
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hexp : 0 ≤ weightExponent n F := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_weightExponent hn F)
  unfold upperTime DyadicCost.costCoefficient
  positivity

-- Only the original fixed fast-threshold numeral is normalized during filter transport.
set_option exponentiation.threshold 1296 in
/-- One positive coefficient and threshold per weight exponent control the natural time
function uniformly over all original bounds F≤(n+2)^κ. This is an estimate of the bound
function itself, usable by the actual Callee contract. No contents/layout/width occurs in it. -/
theorem exists_dyadicTime_subcubic_bound {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ^ 1296 ≤ N ∧
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (dyadicTime n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
  let C : ℝ := (49338 * (κ + 7) + 550 : ℕ)
  have hcκ : (1 : ℝ) ≤ (2 * κ + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * κ + 2)
  have hevent := DyadicCost.costCoefficient_eventually_le_rpow hcκ
    (by norm_num : (0 : ℝ) < 1 / 1296)
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ F ≤ (n + 2) ^ κ,
      (dyadicTime n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
    filter_upwards [hevent, eventually_ge_atTop (16 : ℕ)] with n hc hn
    intro F hF
    have hn2 : 2 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hcoeff := (DyadicCost.costCoefficient_mono hn1 (weightExponent_le hn2 hF)).trans hc
    have hmain : 3 * DyadicCost.costCoefficient (weightExponent n F) n *
        ((n : ℝ) ^ 3 / groups n) ≤ 12 * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
      calc
        _ ≤ 3 * (n : ℝ) ^ (1 / 1296 : ℝ) * ((n : ℝ) ^ 3 / groups n) := by gcongr
        _ ≤ 3 * (n : ℝ) ^ (1 / 1296 : ℝ) *
            (4 * (n : ℝ) ^ (3 - 1 / 648 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (cubic_div_groups_le (by omega)) (by positivity)
        _ = _ := by
          rw [mul_assoc, mul_left_comm ((n : ℝ) ^ (1 / 1296 : ℝ)) 4,
            ← mul_assoc, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < n))]
          norm_num
    have hlog := setupLog_le_log hF
    have hclog : Nat.clog 2 (n + 2) ≤ n + 2 :=
      Nat.clog_le_of_le_pow (show n + 2 ≤ 2 ^ (n + 2) from Nat.lt_two_pow_self.le)
    have hn2' : n + 2 ≤ 2 * (n * n) := by nlinarith
    have hsetup := hlog.trans (Nat.mul_le_mul_left (κ + 7) (hclog.trans hn2'))
    have hsmallNat : 24 * (n * n) + 24669 * setupLog n F + 514 ≤
        (49338 * (κ + 7) + 538) * (n * n) := by
      have hunit : 1 ≤ n * n := by nlinarith
      nlinarith only [hsetup, hunit]
    have hsmallR := (Nat.cast_le (α := ℝ)).mpr hsmallNat
    have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
    have hscaled := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ (49338 * (κ + 7) + 538 : ℕ) by positivity)
    have hceil := (Nat.ceil_lt_add_one (upperTime_nonneg hn2 F)).le
    unfold dyadicTime C
    push_cast at hsmallR hscaled ⊢
    unfold upperTime at hceil ⊢
    nlinarith only [hmain, hsmallR, hscaled, hceil]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfinal
  refine ⟨C, by dsimp only [C]; positivity, max N (2 ^ 1296), le_max_right _ _, ?_⟩
  intro n hn
  exact hN n ((le_max_left _ _).trans hn)

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
