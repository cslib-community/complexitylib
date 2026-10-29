/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLayout

/-!
# Polynomial global preprocessing reservations

Every frontend allocation, explicit-stack reservation and root allocation is bounded by a fixed
power of the existing parameter budget. This derives local kernel fits from logarithmic width.

## Main results

* `arena_envelope_le`: the complete global signed envelope has polynomial magnitude.

These coarse resource estimates are original. Charged subquadratic time is a separate bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- The complete global envelope is a fixed power of the already bounded native parameter budget. -/
theorem arena_envelope_le (κ n : ℕ) (retained : ℕ → ℕ) :
    let a := arena κ n retained
    Traversal.envelope a.ceiling a.n a.m a.Λ a.U a.N ≤
      Parameters.Math.budget n ((n + 2) ^ κ) ^ 52 := by
  let U := (n + 2) ^ κ
  let P := Parameters.Math.budget n U
  let l := Frontend.layout κ n
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let N := 2 * m ^ 2
  have hP : 64 ≤ P := by dsimp only [P, Parameters.Math.budget]; omega
  have hP1 : 1 ≤ P := by omega
  have hsmall : 8 * U + 4 * n + 64 ≤ P := by
    dsimp only [P, Parameters.Math.budget]
    omega
  have hms : 8 * (m + 1) ^ 2 ≤ P := by
    dsimp only [P, Parameters.Math.budget, m]
    omega
  have hm : m ≤ P := by nlinarith
  have hmp : m + 1 ≤ P := by nlinarith
  have hm2 : m ^ 2 ≤ P := by nlinarith
  have hN : N ≤ P := by dsimp only [N]; nlinarith
  have hn : n + 1 ≤ P := by omega
  have hU : 2 * U ≤ P := by omega
  have hΛ : l.digits ≤ P := by
    have hl := Nat.log_le_self 2 (4 * U)
    change Cslib.Algorithms.ThreeSum.labelBits (2 * U) ≤ P
    dsimp only [Cslib.Algorithms.ThreeSum.labelBits]
    rw [show 2 * (2 * U) = 4 * U by omega]
    omega
  have hheight : Cslib.Algorithms.ThreeSum.ChanHe.height n ≤ Nat.log 2 n + 2 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hlog := Nat.log_le_self 2 n
  have hF : F ≤ P := by
    dsimp only [F, Cslib.Algorithms.ThreeSum.ChanHe.fuel]
    omega
  have hwork : Traversal.Math.work F ≤ P ^ 6 := by
    have hw := Traversal.work_fuel_le n
    change Traversal.Math.work F ≤ 3 * (2 * Nat.log 2 n + 2) ^ 5 at hw
    calc Traversal.Math.work F ≤ 3 * P ^ 5 :=
        hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5))
      _ ≤ P * P ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 6 := by ring
  have hpower : 3 ^ (F + 1) ≤ P ^ 7 := by
    have he := Traversal.Math.work_eq F
    have hpow : 1 ≤ P ^ 6 := Nat.one_le_pow _ _ hP1
    calc 3 ^ (F + 1) ≤ 3 * P ^ 6 := by omega
      _ ≤ P * P ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 7 := by ring
  have hD : l.count ≤ P ^ 3 := by
    have hsq := Nat.pow_le_pow_left hΛ 2
    have hpos : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ hP1
    calc
      l.count ≤ 4 * P ^ 2 := by
        dsimp only [Frontend.Layout.count, Frontend.Layout.splits]
        omega
      _ ≤ P * P ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 3 := by ring
  have hfront : l.endpoint ≤ P ^ 4 := by
    have hb := Frontend.array_budget_le n U
    change Frontend.Arrays.budget l U ≤ P ^ 4 at hb
    apply le_trans ?_ hb
    dsimp only [Frontend.Arrays.budget]
    omega
  have hdelta : Traversal.allocationSize (n + 1) m N ≤ P ^ 2 := by
    dsimp only [Traversal.allocationSize]
    nlinarith
  have powmono {i j : ℕ} (hij : i ≤ j) : P ^ i ≤ P ^ j :=
    Nat.pow_le_pow_right hP1 hij
  have hstack : l.endpoint + m + 1 ≤ P ^ 5 := by
    have hp := powmono (show 1 ≤ 4 by decide)
    simp only [pow_one] at hp
    calc l.endpoint + m + 1 ≤ 2 * P ^ 4 := by omega
      _ ≤ P * P ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 5 := by ring
  have hcap : 7 * (2 * F + 1) ≤ P ^ 2 := by nlinarith
  have htable : l.endpoint + m + 1 + 7 * (2 * F + 1) ≤ P ^ 6 := by
    have hp := powmono (show 2 ≤ 5 by decide)
    calc _ ≤ 2 * P ^ 5 := by omega
      _ ≤ P * P ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 6 := by ring
  have houtcap : l.count * 3 ^ (F + 1) ≤ P ^ 10 := by
    calc _ ≤ P ^ 3 * P ^ 7 := Nat.mul_le_mul hD hpower
      _ = P ^ 10 := by ring
  have hfloor : (arena κ n retained).floor ≤ P ^ 11 := by
    have hp := powmono (show 6 ≤ 10 by decide)
    change l.endpoint + m + 1 + 7 * (2 * F + 1) + l.count * 3 ^ (F + 1) ≤ _
    calc _ ≤ 2 * P ^ 10 := by omega
      _ ≤ P * P ^ 10 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 11 := by ring
  have halloc : l.count * (Traversal.Math.work F *
      Traversal.allocationSize (n + 1) m N) ≤ P ^ 11 := by
    calc _ ≤ P ^ 3 * (P ^ 6 * P ^ 2) :=
        Nat.mul_le_mul hD (Nat.mul_le_mul hwork hdelta)
      _ = P ^ 11 := by ring
  have hceil : (arena κ n retained).ceiling ≤ P ^ 12 := by
    change (arena κ n retained).floor + l.count *
      (Traversal.Math.work F * Traversal.allocationSize (n + 1) m N) ≤ _
    calc _ ≤ 2 * P ^ 11 := by omega
      _ ≤ P * P ^ 11 := Nat.mul_le_mul_right _ (by omega)
      _ = P ^ 12 := by ring
  have hsum : (arena κ n retained).ceiling + (n + 1) + m ^ 2 + l.digits + m +
      2 * U + N + 100 ≤ 2 * P ^ 12 := by
    have hpow : P ^ 2 ≤ P ^ 12 := powmono (by decide)
    have hsmall' : (n + 1) + m ^ 2 + l.digits + m + 2 * U + N + 100 ≤ P ^ 2 := by
      nlinarith
    omega
  change 65536 * ((arena κ n retained).ceiling + (n + 1) + m ^ 2 + l.digits + m +
      2 * U + N + 100) ^ 4 ≤ P ^ 52
  calc _ ≤ 65536 * (2 * P ^ 12) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 4)
    _ = 1048576 * P ^ 48 := by ring
    _ ≤ P ^ 4 * P ^ 48 := Nat.mul_le_mul_right _ (by
      have := Nat.pow_le_pow_left hP 4
      norm_num at this
      omega)
    _ = P ^ 52 := by ring

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
