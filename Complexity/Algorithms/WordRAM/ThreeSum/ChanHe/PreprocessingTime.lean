/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingInput
public import Complexity.Algorithms.ThreeSum.ChanHe.ShiftedSizes

/-!
# Subquadratic charged native preprocessing cost

The bound counts complete initialized-input execution, trial division, all descriptor loads,
every recursion transition, native collision/heavy computation, array writes and the final halt.
Its polynomial factor is `(n+2)(sqrt(n+2)+1)` and its logarithm has fixed degree thirteen.

## Main definitions

* `rootCoefficient`, `costCoefficient`: explicit constants depending only on the fixed exponent.

## Main results

* `cost_bound`: the actual native instruction count is at most square-root times linear times
  a fixed logarithmic power, uniformly over physical width.

These charged estimates are original. The existing mathematical prime/instance bounds are reused.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Uniform complete-root coefficient after substituting the actual candidate bound. -/
def rootCoefficient (κ : ℕ) : ℕ :=
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  70 + 196608 * (C + 4 * C ^ 3)

/-- Explicit whole-program coefficient, independent of input length, data and physical width. -/
def costCoefficient (κ : ℕ) : ℕ :=
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  Frontend.costCoefficient κ + 60 * C ^ 2 + 77 +
    4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)

private theorem parameter_scale_bounds (κ n : ℕ) :
    let B := n + 2
    let L := Nat.log 2 B + 1
    let S := Nat.sqrt B + 1
    let C := (5 * κ + 16) * (10 * κ + 40) + 1
    Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ) + 1 ≤ C * S * L ^ 2 ∧
      S ^ 2 ≤ 4 * B := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  constructor
  · have hm := Cslib.Algorithms.ThreeSum.ChanHe.mPar_shifted_pow_le n κ
    have hu : 1 ≤ S * L ^ 2 := by
      have hp : 0 < S * L ^ 2 := by positivity
      omega
    calc _ ≤ ((5 * κ + 16) * (10 * κ + 40)) * S * L ^ 2 + S * L ^ 2 :=
        Nat.add_le_add hm hu
      _ = C * S * L ^ 2 := by dsimp only [C]; ring
  · have hs := Nat.sqrt_le B
    have ht := Nat.sqrt_le_self B
    change S ^ 2 ≤ 4 * B
    dsimp only [S]
    nlinarith only [hs, ht, hB]

/-- The complete root cost at the actual magnitude-derived candidate window. -/
theorem root_cost_bound (κ n : ℕ) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    Traversal.rootTime (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) (n + 1) m (2 * m ^ 2) ≤
      rootCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
        (Nat.log 2 (n + 2) + 1) ^ 11 := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hlog : Nat.log 2 n ≤ Nat.log 2 B := Nat.log_mono_right (by dsimp only [B]; omega)
  obtain ⟨hmb, hsquare⟩ := parameter_scale_bounds κ n
  change m + 1 ≤ C * S * L ^ 2 at hmb
  change S ^ 2 ≤ 4 * B at hsquare
  have hcube : S ^ 3 ≤ 4 * B * S := by
    have hh := Nat.mul_le_mul_right S hsquare
    nlinarith
  have lp {i j : ℕ} (hij : i ≤ j) : L ^ i ≤ L ^ j := Nat.pow_le_pow_right hL hij
  have hroot : Traversal.rootTime F (n + 1) m (2 * m ^ 2) ≤
      rootCoefficient κ * B * S * L ^ 11 := by
    have hr := Traversal.rootTime_fuel_square_le n (n + 1) m
    have hlogs : 2 * Nat.log 2 n + 2 ≤ 2 * L := by dsimp only [L]; omega
    calc Traversal.rootTime F (n + 1) m (2 * m ^ 2)
        ≤ 70 + 6144 * (2 * L) ^ 5 *
          (B * (C * S * L ^ 2) + (C * S * L ^ 2) ^ 3) := by
            apply hr.trans
            change 70 + 6144 * (2 * Nat.log 2 n + 2) ^ 5 *
              (B * (m + 1) + (m + 1) ^ 3) ≤ _
            gcongr
      _ = 70 + 196608 * (C * B * S * L ^ 7 + C ^ 3 * S ^ 3 * L ^ 11) := by ring
      _ ≤ 70 + 196608 * (C * B * S * L ^ 11 + C ^ 3 * (4 * B * S) * L ^ 11) := by
        have hl : C * B * S * L ^ 7 ≤ C * B * S * L ^ 11 :=
          Nat.mul_le_mul_left _ (lp (show 7 ≤ 11 by decide))
        have hr : C ^ 3 * S ^ 3 * L ^ 11 ≤ C ^ 3 * (4 * B * S) * L ^ 11 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcube)
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add hl hr)) _
      _ ≤ rootCoefficient κ * B * S * L ^ 11 := by
        have hu : 1 ≤ B * S * L ^ 11 := by
          have hp : 0 < B * S * L ^ 11 := by positivity
          omega
        change _ ≤ (70 + 196608 * (C + 4 * C ^ 3)) * B * S * L ^ 11
        nlinarith only [hu]
  exact hroot

private theorem forest_time_bound (κ n : ℕ) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
    (Frontend.layout κ n).count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤
      (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) *
        ((n + 2) * (Nat.sqrt (n + 2) + 1) * (Nat.log 2 (n + 2) + 1) ^ 13) := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let V := B * S * L ^ 13
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hroot := root_cost_bound κ n
  change Traversal.rootTime F (n + 1) m (2 * m ^ 2) ≤
    rootCoefficient κ * B * S * L ^ 11 at hroot
  have hD : (Frontend.layout κ n).count ≤ 4 * (κ + 3) ^ 2 * L ^ 2 := by
    have hb := Cslib.Algorithms.ThreeSum.ChanHe.labelBits_pow_le B κ
    have hb' : (Frontend.layout κ n).digits ≤ (κ + 3) * L := by
      exact hb.trans (by change κ * L + 3 ≤ (κ + 3) * L; nlinarith only [hL])
    have hh := Nat.pow_le_pow_left hb' 2
    have hu : 1 ≤ ((κ + 3) * L) ^ 2 := by
      have hp : 0 < ((κ + 3) * L) ^ 2 := by positivity
      omega
    dsimp only [Frontend.Layout.count, Frontend.Layout.splits]
    nlinarith only [hh, hu]
  have hforest : (Frontend.layout κ n).count *
      (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤
      (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V := by
    have hu : 1 ≤ B * S * L ^ 11 := by
      have hp : 0 < B * S * L ^ 11 := by positivity
      omega
    have hr : Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17 ≤
        (rootCoefficient κ + 17) * B * S * L ^ 11 := by nlinarith only [hroot, hu]
    calc _ ≤ (4 * (κ + 3) ^ 2 * L ^ 2) *
          ((rootCoefficient κ + 17) * B * S * L ^ 11) := Nat.mul_le_mul hD hr
      _ = _ := by dsimp only [V]; ring
  exact hforest

private theorem prime_time_bound (B S C L m : ℕ)
    (hB : 1 ≤ B) (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hmb : m + 1 ≤ C * S * L ^ 2) (hsquare : S ^ 2 ≤ 4 * B) :
    (m + 1) * (7 * m + 15) + 8 ≤
      (60 * C ^ 2 + 8) * (B * S * L ^ 13) := by
  let V := B * S * L ^ 13
  have hV : 1 ≤ V := by
    have hp : 0 < V := by dsimp only [V]; positivity
    omega
  have lp {i j : ℕ} (hij : i ≤ j) : L ^ i ≤ L ^ j := Nat.pow_le_pow_right hL hij
  have hprime : (m + 1) * (7 * m + 15) + 8 ≤ (60 * C ^ 2 + 8) * V := by
    have hm2 := Nat.pow_le_pow_left hmb 2
    have hs := Nat.mul_le_mul_right (C ^ 2 * L ^ 4) hsquare
    have hsmall : B * L ^ 4 ≤ V := by
      have hh := Nat.mul_le_mul_left B (lp (show 4 ≤ 13 by decide))
      calc B * L ^ 4 ≤ B * L ^ 13 := hh
        _ ≤ B * S * L ^ 13 := Nat.mul_le_mul_right _ (by nlinarith only [hS])
    have hms : (m + 1) ^ 2 ≤ 4 * C ^ 2 * B * L ^ 4 := by nlinarith only [hm2, hs]
    have hh := Nat.mul_le_mul_left (60 * C ^ 2) hsmall
    nlinarith only [hms, hh, hV]
  exact hprime

private theorem frontend_time_bound (κ n : ℕ) :
    Frontend.cost κ n ≤ Frontend.costCoefficient κ *
      ((n + 2) * (Nat.sqrt (n + 2) + 1) * (Nat.log 2 (n + 2) + 1) ^ 13) := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let V := B * S * L ^ 13
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have lp {i j : ℕ} (hij : i ≤ j) : L ^ i ≤ L ^ j := Nat.pow_le_pow_right hL hij
  have hclog : Nat.clog 2 B ≤ L :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) B).le
  have hfront : Frontend.cost κ n ≤ Frontend.costCoefficient κ * V := by
    have hh := Frontend.cost_bound κ n
    have hlogs := Nat.pow_le_pow_left hclog 2
    have hp := lp (show 2 ≤ 13 by decide)
    have hnb : n + 1 ≤ B := by dsimp only [B]; omega
    have hsmall : (n + 1) * Nat.clog 2 B ^ 2 ≤ V := by
      calc (n + 1) * Nat.clog 2 B ^ 2 ≤ B * L ^ 13 :=
          Nat.mul_le_mul hnb (hlogs.trans hp)
        _ ≤ B * S * L ^ 13 := Nat.mul_le_mul_right _ (by nlinarith only [hS])
    rw [Nat.mul_assoc] at hh
    exact hh.trans (Nat.mul_le_mul_left (Frontend.costCoefficient κ) hsmall)
  exact hfront

/-- The actual native program has a genuinely subquadratic polynomial factor and fixed polylog. -/
theorem cost_bound (κ n : ℕ) :
    cost κ n ≤ costCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
      (Nat.log 2 (n + 2) + 1) ^ 13 := by
  let B := n + 2
  let L := Nat.log 2 B + 1
  let S := Nat.sqrt B + 1
  let C := (5 * κ + 16) * (10 * κ + 40) + 1
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * B ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let V := B * S * L ^ 13
  have hB : 2 ≤ B := by dsimp only [B]; omega
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hlog : Nat.log 2 n ≤ Nat.log 2 B := Nat.log_mono_right (by dsimp only [B]; omega)
  obtain ⟨hmb, hsquare⟩ := parameter_scale_bounds κ n
  change m + 1 ≤ C * S * L ^ 2 at hmb
  change S ^ 2 ≤ 4 * B at hsquare
  have lp {i j : ℕ} (hij : i ≤ j) : L ^ i ≤ L ^ j := Nat.pow_le_pow_right hL hij
  have hV : 1 ≤ V := by
    have hp : 0 < V := by dsimp only [V]; positivity
    omega
  have hforest := forest_time_bound κ n
  change (Frontend.layout κ n).count *
    (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤
      (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V at hforest
  have hprime : (m + 1) * (7 * m + 15) + 8 ≤ (60 * C ^ 2 + 8) * V :=
    prime_time_bound B S C L m (by omega) hS hL hmb hsquare
  have hfront : Frontend.cost κ n ≤ Frontend.costCoefficient κ * V := frontend_time_bound κ n
  have hheight : Cslib.Algorithms.ThreeSum.ChanHe.height n ≤ Nat.log 2 n + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hF : 4 * F + 45 ≤ 69 * V := by
    have hLV : L ≤ V := by
      have hh := lp (show 1 ≤ 13 by decide)
      simp only [pow_one] at hh
      calc L ≤ L ^ 13 := hh
        _ ≤ B * S * L ^ 13 := Nat.le_mul_of_pos_left _ (by positivity)
    have hsmall : F ≤ 6 * L := by
      change 3 * Cslib.Algorithms.ThreeSum.ChanHe.height n - 2 ≤ _
      dsimp only [L]
      omega
    have hh : 4 * F + 45 ≤ 69 * L := by nlinarith only [hsmall, hL]
    exact hh.trans (Nat.mul_le_mul_left 69 hLV)
  change Frontend.cost κ n + (m + 1) * (7 * m + 15) + 8 + 4 * F + 45 +
    (Frontend.layout κ n).count * (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) ≤ _
  rw [show costCoefficient κ * (n + 2) * (Nat.sqrt (n + 2) + 1) *
      (Nat.log 2 (n + 2) + 1) ^ 13 = costCoefficient κ * V by dsimp only [V, B, S, L]; ring]
  change _ ≤ (Frontend.costCoefficient κ + 60 * C ^ 2 + 77 +
    4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V
  calc _ = Frontend.cost κ n + ((m + 1) * (7 * m + 15) + 8) +
        (4 * F + 45) + (Frontend.layout κ n).count *
          (Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) := by omega
    _ ≤ Frontend.costCoefficient κ * V + (60 * C ^ 2 + 8) * V + 69 * V +
        (4 * (κ + 3) ^ 2 * (rootCoefficient κ + 17)) * V :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfront hprime) hF) hforest
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
