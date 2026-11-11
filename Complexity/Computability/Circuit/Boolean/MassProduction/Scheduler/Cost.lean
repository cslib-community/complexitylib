/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler.PhaseCircuit
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Gate budgets of the scheduler

A phase with `2 ^ p ≤ 2 ^ D` pending requests and a menu of `r` entries, where
`2 ^ p * r ≤ 2 ^ D * (2 + 3 L) + 2 ^ (p + 1)`, costs at most
`16384 * 2 ^ D * (s + 1) * (D + L + b + 2) ^ 4` gates when `s < 2 ^ b` (`phaseCost_le`). A sort
of `2 ^ p` records of width `R` by `k` key bits costs at most
`(p + 1) ^ 2 * 2 ^ p * (2 k + 2 R + 1)` gates (`size_bitonicSortCircuit_le`). These count every
gate, including constants; the factors are crude.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Scheduler.size_bitonicSortCircuit_le`: sorting.
* `Cslib.Circuits.Boolean.MassProduction.Scheduler.phaseCost_le`: the phase budget.

## References

* Adapted from MassProduction/Nonuniform/BufferIterationCost.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using the sorting network of
  [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Scheduler

open BitonicSort

/-- A sort of `2 ^ p` records of width `R` by `k` key bits uses at most
`(p + 1) ^ 2 * 2 ^ p * (2 * k + 2 * R + 1)` gates. -/
theorem size_bitonicSortCircuit_le {k R : ℕ} (key : Fin k → Fin R) (p : ℕ) (ascending : Bool) :
    (bitonicSortCircuit key p ascending).size ≤ (p + 1) ^ 2 * 2 ^ p * (2 * k + 2 * R + 1) := by
  have h := four_mul_size_bitonicSortCircuit key p ascending
  have hite : (if R = 0 then 0 else 6 * k + 6 * R + 2) ≤ 3 * (2 * k + 2 * R + 1) := by
    split_ifs <;> lia
  have hp : p * (p + 1) ≤ (p + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (Nat.le_succ p)
  have := Nat.mul_le_mul (Nat.mul_le_mul_right (2 ^ p) hp) hite
  have e : (p + 1) ^ 2 * 2 ^ p * (3 * (2 * k + 2 * R + 1)) =
      3 * ((p + 1) ^ 2 * 2 ^ p * (2 * k + 2 * R + 1)) := by ring
  lia

section Bounds

variable {n W S r k s L : ℕ}

private theorem pow_le_four (hW : 1 ≤ W) {i : ℕ} (hi : i ≤ 4) : W ^ i ≤ W ^ 4 :=
  Nat.pow_le_pow_right hW hi

private theorem stage1_le (hrk : r * k ≤ 4 * n * W) (hsS : s ≤ S) (hLW : L ≤ W) (hW : 1 ≤ W) :
    r * k * s * L ≤ 4 * n * S * W ^ 4 :=
  calc r * k * s * L ≤ (4 * n * W) * S * W := Nat.mul_le_mul (Nat.mul_le_mul hrk hsS) hLW
    _ = 4 * n * S * W ^ 2 := by ring
    _ ≤ 4 * n * S * W ^ 4 := Nat.mul_le_mul_left _ (pow_le_four hW (by decide))

private theorem stage2_le {X Y : ℕ} (hX : X ≤ 6 * n * S * W) (hY : Y ≤ 7 * W) (hLW : L + 2 ≤ W) :
    48 * X * Y ^ 2 * (L + 1 + 1) ≤ 14112 * n * S * W ^ 4 :=
  calc 48 * X * Y ^ 2 * (L + 1 + 1) ≤ 48 * (6 * n * S * W) * (7 * W) ^ 2 * W := by gcongr
    _ = 14112 * n * S * W ^ 4 := by ring

private theorem stage4_le (hrk : r * k ≤ 4 * n * W) (hS : S = s + 1) (hW : 1 ≤ W) :
    r * k * (2 * s + 2) ≤ 8 * n * S * W ^ 4 :=
  calc r * k * (2 * s + 2) = 2 * (r * k) * S := by rw [hS]; ring
    _ ≤ 2 * (4 * n * W) * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrk)
    _ = 8 * n * S * W ^ 1 := by ring
    _ ≤ 8 * n * S * W ^ 4 := Nat.mul_le_mul_left _ (pow_le_four hW (by decide))

private theorem stage5_le {p z : ℕ} (hz : z ≤ (p + 1) ^ 2 * k * 5) (hrk : r * k ≤ 4 * n * W)
    (hp : p + 1 ≤ W) (hS : 1 ≤ S) (hW : 1 ≤ W) : r * z ≤ 20 * n * S * W ^ 4 :=
  calc r * z ≤ r * ((p + 1) ^ 2 * k * 5) := Nat.mul_le_mul_left r hz
    _ = 5 * (p + 1) ^ 2 * (r * k) := by ring
    _ ≤ 5 * W ^ 2 * (4 * n * W) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 2)) hrk
    _ = 20 * n * 1 * W ^ 3 := by ring
    _ ≤ 20 * n * S * W ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) (pow_le_four hW (by decide))

private theorem stage6_le (hr : r ≤ 4 * n * W) (hS : 1 ≤ S) (hW : 1 ≤ W) :
    3 * r ≤ 12 * n * S * W ^ 4 :=
  calc 3 * r ≤ 3 * (4 * n * W) := Nat.mul_le_mul_left _ hr
    _ = 12 * n * 1 * W ^ 1 := by ring
    _ ≤ 12 * n * S * W ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) (pow_le_four hW (by decide))

private theorem stage7_le (hrk : r * k ≤ 4 * n * W) (hkn : k ≤ n) (hS : 1 ≤ S) (hW : 1 ≤ W) :
    k * (2 * r + 1) ≤ 9 * n * S * W ^ 4 := by
  have h : n ≤ n * W := Nat.le_mul_of_pos_right _ hW
  calc k * (2 * r + 1) ≤ 9 * n * W := by
        have : k * (2 * r + 1) = 2 * (r * k) + k := by ring
        lia
    _ = 9 * n * 1 * W ^ 1 := by ring
    _ ≤ 9 * n * S * W ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) (pow_le_four hW (by decide))

private theorem stage8_le (hrk : r * k ≤ 4 * n * W) (hkn : k ≤ n) (hsS : s ≤ S) (hLW : L ≤ W)
    (hW : 1 ≤ W) : k * s * L * (2 * r + 1) ≤ 9 * n * S * W ^ 4 := by
  have h : n ≤ n * W := Nat.le_mul_of_pos_right _ hW
  have h9 : k * (2 * r + 1) ≤ 9 * n * W := by
    have : k * (2 * r + 1) = 2 * (r * k) + k := by ring
    lia
  calc k * s * L * (2 * r + 1) = k * (2 * r + 1) * s * L := by ring
    _ ≤ 9 * n * W * S * W := Nat.mul_le_mul (Nat.mul_le_mul h9 hsS) hLW
    _ = 9 * n * S * W ^ 2 := by ring
    _ ≤ 9 * n * S * W ^ 4 := Nat.mul_le_mul_left _ (pow_le_four hW (by decide))

private theorem stage9_le {p z D : ℕ}
    (hz : z ≤ (p + 1) ^ 2 * k * (2 * 1 + 2 * (1 + (D + (L + s * L))) + 1))
    (hkn : k ≤ n) (hp : p + 1 ≤ W) (hDL : D + L ≤ W) (hLW : L ≤ W) (hS : S = s + 1)
    (hW : 1 ≤ W) : z ≤ 7 * n * S * W ^ 4 := by
  have hR : 2 * 1 + 2 * (1 + (D + (L + s * L))) + 1 ≤ 7 * (S * W) := by
    have : s * L ≤ s * W := Nat.mul_le_mul_left _ hLW
    have : S * W = s * W + W := by rw [hS]; ring
    lia
  calc z ≤ (p + 1) ^ 2 * k * (2 * 1 + 2 * (1 + (D + (L + s * L))) + 1) := hz
    _ ≤ W ^ 2 * n * (7 * (S * W)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hp 2) hkn) hR
    _ = 7 * n * S * W ^ 3 := by ring
    _ ≤ 7 * n * S * W ^ 4 := Nat.mul_le_mul_left _ (pow_le_four hW (by decide))

end Bounds

private theorem stage3_le {D L b s p r : ℕ} (hk : arity p ≤ 2 ^ D)
    (hrk : r * arity p ≤ 4 * 2 ^ D * (D + L + b + 2)) (hs : s < 2 ^ b) :
    r * ((duplicateFlagsCircuit (id : Fin (L + 1) → Fin (L + 1))
      (Nat.clog 2 (arity p * s))).size + 2) ≤ 264 * 2 ^ D * (s + 1) * (D + L + b + 2) ^ 4 := by
  set W := D + L + b + 2 with hW
  set d := Nat.clog 2 (arity p * s) with hd
  have hW1 : 1 ≤ W := by lia
  have hk1 : 1 ≤ arity p := by rw [arity_eq_two_pow]; exact Nat.one_le_two_pow
  have hA : arity d ≤ 2 * (arity p * s) + 1 := by
    rw [arity_eq_two_pow]
    by_cases h0 : arity p * s = 0
    · rw [hd, h0]
      simp
    · have := Nat.pow_clog_le_mul Nat.one_lt_two h0
      lia
  have hA1 : 1 ≤ arity d := by rw [arity_eq_two_pow]; exact Nat.one_le_two_pow
  have hd1 : d + 1 ≤ W := by
    have : arity p * s ≤ 2 ^ (D + b) := by
      rw [pow_add]
      exact Nat.mul_le_mul hk hs.le
    have := Nat.clog_le_of_le_pow this
    lia
  have hsts : 4 * sortTraceSize d ≤ 4 * (W ^ 2 * arity d) := by
    rw [four_mul_sortTraceSize, ← arity_eq_two_pow]
    have h1 : d * (d + 1) ≤ W ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by lia) hd1
    calc d * (d + 1) * arity d ≤ W ^ 2 * arity d := Nat.mul_le_mul_right _ h1
      _ ≤ 4 * (W ^ 2 * arity d) := by lia
  have hsts' : sortTraceSize d ≤ W ^ 2 * arity d := by lia
  have hW3 : W ≤ W ^ 3 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by decide)
  have e1 : sortTraceSize d * (6 * (L + 1) + 6 * (L + 1) + 8) ≤ 12 * W ^ 3 * arity d :=
    calc sortTraceSize d * (6 * (L + 1) + 6 * (L + 1) + 8) ≤ (W ^ 2 * arity d) * (12 * W) :=
          Nat.mul_le_mul hsts' (by lia)
      _ = 12 * W ^ 3 * arity d := by ring
  have e2 : (arity d - 1) * (6 * (L + 1) + 1) ≤ 6 * W ^ 3 * arity d :=
    calc (arity d - 1) * (6 * (L + 1) + 1) ≤ arity d * (6 * W ^ 3) := by gcongr <;> omega
      _ = 6 * W ^ 3 * arity d := by ring
  have e3 : 4 * arity d ≤ 4 * W ^ 3 * arity d := by
    have : 1 ≤ W ^ 3 := Nat.one_le_pow _ _ (by lia)
    calc 4 * arity d = 4 * 1 * arity d := by ring
      _ ≤ 4 * W ^ 3 * arity d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
  have hsize : (duplicateFlagsCircuit (id : Fin (L + 1) → Fin (L + 1)) d).size + 2 ≤
      22 * W ^ 3 * arity d := by
    rw [size_duplicateFlagsCircuit]
    lia
  have hrA : r * arity d ≤ 12 * 2 ^ D * W * (s + 1) := by
    have h1 := Nat.mul_le_mul_left r hA
    have h2 : r * (2 * (arity p * s) + 1) = 2 * ((r * arity p) * s) + r := by ring
    have h3 := Nat.mul_le_mul_right s hrk
    have hr : r ≤ r * arity p := Nat.le_mul_of_pos_right r hk1
    have h4 : 4 * 2 ^ D * W * (s + 1) = 4 * 2 ^ D * W * s + 4 * 2 ^ D * W := by ring
    have h5 : 12 * 2 ^ D * W * (s + 1) = 12 * 2 ^ D * W * s + 12 * 2 ^ D * W := by ring
    lia
  calc r * ((duplicateFlagsCircuit (id : Fin (L + 1) → Fin (L + 1)) d).size + 2)
      ≤ r * (22 * W ^ 3 * arity d) := Nat.mul_le_mul_left r hsize
    _ = 22 * W ^ 3 * (r * arity d) := by ring
    _ ≤ 22 * W ^ 3 * (12 * 2 ^ D * W * (s + 1)) := Nat.mul_le_mul_left _ hrA
    _ = 264 * 2 ^ D * (s + 1) * W ^ 4 := by ring

/-- **The phase budget.** Under the menu-size bound and `s < 2 ^ b`, one phase costs at most
`16384 * 2 ^ D * (s + 1) * (D + L + b + 2) ^ 4` gates, counting every gate. -/
theorem phaseCost_le {D L b s p a r : ℕ} (hk : a + arity p = 2 ^ D)
    (hr : arity p * r ≤ 2 ^ D * (2 + 3 * L) + 2 * arity p) (hs : s < 2 ^ b) :
    phaseCost D L s p a r ≤ 16384 * 2 ^ D * (s + 1) * (D + L + b + 2) ^ 4 := by
  have hkn : arity p ≤ 2 ^ D := by lia
  have hpD : p ≤ D := by
    by_contra h
    have := Nat.pow_lt_pow_right Nat.one_lt_two (not_le.mp h)
    have := arity_eq_two_pow p
    lia
  have hk1 : 1 ≤ arity p := by rw [arity_eq_two_pow]; exact Nat.one_le_two_pow
  have hW1 : 1 ≤ D + L + b + 2 := by lia
  have hrk : r * arity p ≤ 4 * 2 ^ D * (D + L + b + 2) := by
    have h1 : 2 ^ D * (2 + 3 * L) + 2 * arity p ≤ 2 ^ D * (4 + 3 * L) := by
      have : 2 ^ D * (4 + 3 * L) = 2 ^ D * (2 + 3 * L) + 2 * 2 ^ D := by ring
      lia
    have h2 : 2 ^ D * (4 + 3 * L) ≤ 2 ^ D * (4 * (D + L + b + 2)) :=
      Nat.mul_le_mul_left _ (by lia)
    have h3 : 2 ^ D * (4 * (D + L + b + 2)) = 4 * 2 ^ D * (D + L + b + 2) := by ring
    have h4 : r * arity p = arity p * r := Nat.mul_comm _ _
    lia
  have hr' : r ≤ 4 * 2 ^ D * (D + L + b + 2) := le_trans (Nat.le_mul_of_pos_right r hk1) hrk
  have hS1 : 1 ≤ s + 1 := by lia
  -- Stage 2 operands.
  have hrks : r * arity p * s ≤ 4 * 2 ^ D * (D + L + b + 2) * (s + 1) :=
    Nat.mul_le_mul hrk (by lia)
  have has : a * s ≤ 2 ^ D * (s + 1) := Nat.mul_le_mul (by lia) (by lia)
  have hX : r * arity p * s + a * s + 1 ≤ 6 * 2 ^ D * (s + 1) * (D + L + b + 2) := by
    have h1 : 2 ^ D * (s + 1) ≤ 2 ^ D * (s + 1) * (D + L + b + 2) :=
      Nat.le_mul_of_pos_right _ hW1
    have h2 : 1 ≤ 2 ^ D * (s + 1) := Nat.mul_le_mul Nat.one_le_two_pow hS1
    have h3 : 4 * 2 ^ D * (D + L + b + 2) * (s + 1) = 4 * (2 ^ D * (s + 1) * (D + L + b + 2)) :=
      by ring
    have h4 : 6 * 2 ^ D * (s + 1) * (D + L + b + 2) = 6 * (2 ^ D * (s + 1) * (D + L + b + 2)) :=
      by ring
    lia
  have hY : Nat.clog 2 (r * arity p * s + a * s) + 1 ≤ 7 * (D + L + b + 2) := by
    have hfour : 4 * (D + L + b + 2) < 2 ^ (4 * (D + L + b + 2)) := Nat.lt_two_pow_self
    have hle : r * arity p * s + a * s ≤ 2 ^ (D + b + 4 * (D + L + b + 2)) := by
      have h1 : r * arity p * s + a * s ≤ 2 ^ D * s * (4 * (D + L + b + 2) + 1) := by
        have h5 := Nat.mul_le_mul_right s hrk
        have h6 := Nat.mul_le_mul_right s (show a ≤ 2 ^ D by lia)
        have h7 : 2 ^ D * s * (4 * (D + L + b + 2) + 1) =
            4 * 2 ^ D * (D + L + b + 2) * s + 2 ^ D * s := by ring
        lia
      calc r * arity p * s + a * s ≤ 2 ^ D * s * (4 * (D + L + b + 2) + 1) := h1
        _ ≤ 2 ^ D * 2 ^ b * 2 ^ (4 * (D + L + b + 2)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hs.le) hfour
        _ = 2 ^ (D + b + 4 * (D + L + b + 2)) := by rw [pow_add, pow_add]
    have := Nat.clog_le_of_le_pow hle
    lia
  have t1 := stage1_le hrk (by lia : s ≤ s + 1) (by lia : L ≤ D + L + b + 2) hW1
  have t2 := stage2_le hX hY (by lia : L + 2 ≤ D + L + b + 2)
  have t3 := stage3_le (L := L) hkn hrk hs
  have t4 := stage4_le (s := s) hrk rfl hW1
  have hz5 := size_bitonicSortCircuit_le (id : Fin 1 → Fin 1) p false
  rw [← arity_eq_two_pow] at hz5
  have t5 := stage5_le (z := (bitonicSortCircuit (id : Fin 1 → Fin 1) p false).size)
    (by simpa using hz5) hrk (by lia : p + 1 ≤ D + L + b + 2) hS1 hW1
  have t6 := stage6_le hr' hS1 hW1
  have t7 := stage7_le hrk hkn hS1 hW1
  have t8 := stage8_le (L := L) (s := s) hrk hkn (by lia : s ≤ s + 1)
    (by lia : L ≤ D + L + b + 2) hW1
  have hz9 := size_bitonicSortCircuit_le
    (Fin.castAdd (width D L s) : Fin 1 → Fin (1 + width D L s)) p false
  rw [← arity_eq_two_pow] at hz9
  have t9 := stage9_le hz9 hkn (by lia : p + 1 ≤ D + L + b + 2)
    (by lia : D + L ≤ D + L + b + 2) (by lia : L ≤ D + L + b + 2) rfl hW1
  unfold phaseCost
  lia

end Cslib.Circuits.Boolean.MassProduction.Scheduler
