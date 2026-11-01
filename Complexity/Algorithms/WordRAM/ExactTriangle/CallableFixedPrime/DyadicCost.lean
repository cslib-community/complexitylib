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

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
