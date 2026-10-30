/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.Assembly
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.Nat.Size

/-! Checks for the conditional assembly of the counting simulation (#1833): the streamed modular
sum on concrete terms, the blocking parameters, and toy instances of both interfaces, which show
that the hypotheses of `Cslib.Complexity.CountingSimulation.exists_computableInO_count` can be met.

The toy instances are deliberately trivial: a "network" is a natural number that is its own value,
the contraction reduces it modulo `2 ^ P`, every network is admissible, and the counted quantity
is `2 ^ τ`, the number of all choice strings of length `τ`, carried by the first of
`scheduleCount 1 t` schedules. They exercise the algorithm and its bounds, not the tensor
networks of the intended instance. -/

namespace ComplexityTests.CountingSimulation

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity.CountingSimulation

/-! ### The streamed sum -/

/-- `0 + 1 + 2 + 3 = 6` below the modulus `7`. -/
example : modSum (fun p : Unit × ℕ => p.2) (fun _ => 7) (fun _ => 4) () = 6 := by
  rw [modSum_eq_sum_mod]
  decide

/-- The residue wraps around: `(0 + 1 + 2 + 3 + 4) % 4 = 2`. -/
example : modSum (fun p : Unit × ℕ => p.2) (fun _ => 4) (fun _ => 5) () = 2 := by
  rw [modSum_eq_sum_mod]
  decide

/-- With no terms the sum is zero, whatever the modulus. -/
example : modSum (fun p : Unit × ℕ => p.2 + 1) (fun _ => 5) (fun _ => 0) () = 0 := by
  rw [modSum_eq_sum_mod]
  rfl

/-! ### Blocking parameters -/

/-- With clock `6`, intervals of `⌈log₂ 8⌉ = 3` steps, two of them, and no padding. -/
example : blockLength 6 = 3 ∧ numBlocks 6 = 2 ∧ paddedTime 6 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- With clock `7`, intervals of `⌈log₂ 9⌉ = 4` steps, and one step of padding. -/
example : blockLength 7 = 4 ∧ numBlocks 7 = 2 ∧ paddedTime 7 = 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Two blocked heads over two intervals have `3 ^ 4` movement schedules. -/
example : scheduleCount 2 6 = 81 := by decide

example : paddedTime 7 + 1 ≤ 2 * 7 := paddedTime_add_one_le (by norm_num)

/-! ### A toy contraction algorithm -/

/-- Reducing modulo `2 ^ P` only needs the low `min (size n) P` bits. -/
theorem mod_two_pow_min_size (n P : ℕ) : n % 2 ^ min (Nat.size n) P = n % 2 ^ P := by
  rcases le_total (Nat.size n) P with h | h
  · rw [min_eq_left h, Nat.mod_eq_of_lt (Nat.lt_size_self n),
      Nat.mod_eq_of_lt ((Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right two_pos h))]
  · rw [min_eq_right h]

theorem computableInPolyTime_mod_two_pow :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.2 % 2 ^ p.1) (encPair encNat encNat) encNat := by
  have h : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 % 2 ^ min (Nat.size p.2) p.1)
      (encPair encNat encNat) encNat := by fun_prop
  simpa only [mod_two_pow_min_size] using h

/-- The contraction interface for networks that are their own values, all admissible: a
polynomial-time reduction modulo `2 ^ P` meets every bound. -/
noncomputable def toyContraction :
    ContractionAlgorithm encNat (fun n : ℕ => n) (fun _ _ _ => True) where
  certificate := NativeCertificate.ofPolyTime computableInPolyTime_mod_two_pow
  bound C D := by
    obtain ⟨p, hp, -, hb⟩ := exists_mono_poly_cert computableInPolyTime_mod_two_pow
    obtain ⟨a, d, hpa⟩ := Cslib.polynomiallyBounded_iff_le.mp hp
    refine ⟨a + d, fun s P G _ _ _ _ => ?_⟩
    have hpow : a * ((encPair encNat encNat (P, G)).length + 1) ^ d ≤
        (a + d) * ((encPair encNat encNat (P, G)).length + 1) ^ (a + d) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    have hE : 1 ≤ 2 ^ ((a + d) * s / Nat.sqrt (Nat.log 2 s)) := Nat.one_le_two_pow
    have hT := (hb (P, G)).1.trans (hpa _)
    have hS := (hb (P, G)).2.trans (hpa _)
    exact ⟨hT.trans (hpow.trans (Nat.le_mul_of_pos_right _ hE)), hS.trans hpow⟩

/-! ### A toy network family -/

theorem computableInPolyTime_toyNet :
    ComputableInPolyTime (fun p : List Bool × ℕ × ℕ => 2 ^ paddedTime p.2.1 * (1 - p.2.2))
      (encPair encBits (encPair encUnary encNat)) encNat := by
  simp only [paddedTime, numBlocks, blockLength, Nat.ceilDiv_eq_add_pred_div]
  fun_prop

/-- The count `2 ^ τ` of all choice strings of length `τ`, carried by the network of the first of
`scheduleCount 1 t` schedules; the others have value zero. -/
noncomputable def toyFamily :
    NetworkFamily encNat (fun n : ℕ => n) (fun _ _ _ => True) (fun _ τ => 2 ^ τ) where
  heads := 1
  constant := 0
  net p := 2 ^ paddedTime p.2.1 * (1 - p.2.2)
  polyTime := computableInPolyTime_toyNet
  sum_value x t _ _ := by
    have h0 : 0 ∈ Finset.range (scheduleCount 1 t) :=
      Finset.mem_range.mpr (Nat.one_le_pow _ _ (by norm_num))
    rw [Finset.sum_eq_single_of_mem 0 h0 fun σ _ hσ => by
      rw [Nat.sub_eq_zero_of_le (Nat.one_le_iff_ne_zero.mpr hσ), Nat.mul_zero]]
    rw [Nat.sub_zero, Nat.mul_one]
  admissible _ _ _ _ _ _ := trivial

/-- The simulation computes the count on a concrete input and clock. -/
example : simulate toyFamily ([true, false], 5) = 2 ^ paddedTime 5 :=
  simulate_eq toyFamily (by decide) (by norm_num) le_rfl

/-- On an input that is too long for its clock the simulation outputs `0`. -/
example : simulate toyFamily ([true, false, true], 2) = 0 := by
  simp [simulate]

/-! ### The conditional endpoint on the toy instances -/

/-- `T n = 2 ^ 2 ^ n` meets the bound `max n 2 ≤ T n` of the endpoint. -/
theorem max_le_two_pow_two_pow (n : ℕ) : max n 2 ≤ 2 ^ 2 ^ n :=
  max_le (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num)
    Nat.lt_two_pow_self.le))
    (calc 2 = 2 ^ 2 ^ 0 := by norm_num
      _ ≤ 2 ^ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.zero_le n)))

/-- With the toy interfaces and the time-constructible `T n = 2 ^ 2 ^ n ≥ max n 2`, the count at
the padded clock is computable within time `2 ^ O(T / √(log T))` and space `T ^ O(1)`. -/
example : ∃ C d : ℕ, ComputableInO
    (fun x : List Bool => 2 ^ paddedTime (1 * 2 ^ 2 ^ x.length)) encBits encNat
    (fun x => 2 ^ (C * 2 ^ 2 ^ x.length / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ x.length))))
    (fun x => (2 ^ 2 ^ x.length) ^ d) :=
  exists_computableInO_count toyFamily toyContraction (fun _ _ => le_rfl)
    Cslib.Complexity.timeConstructible_two_pow_two_pow
    max_le_two_pow_two_pow
    le_rfl (rule := Prod.snd) (by fun_prop)

/-- The strict-majority comparison `2 ^ τ < 2 * count` used for `BPTIME` and `PPTIME` is a
polynomial-time rule because the padded time is passed in unary. On the toy family every string
is accepted, so the rule accepts every input. -/
example : ∃ C d : ℕ, ComputableInO
    (fun x : List Bool => decide (2 ^ paddedTime (1 * 2 ^ 2 ^ x.length) <
      2 * 2 ^ paddedTime (1 * 2 ^ 2 ^ x.length))) encBits encBool
    (fun x => 2 ^ (C * 2 ^ 2 ^ x.length / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ x.length))))
    (fun x => (2 ^ 2 ^ x.length) ^ d) :=
  exists_computableInO_count toyFamily toyContraction (fun _ _ => le_rfl)
    Cslib.Complexity.timeConstructible_two_pow_two_pow
    max_le_two_pow_two_pow
    le_rfl (rule := fun p => decide (2 ^ p.1 < 2 * p.2)) (by fun_prop)

end ComplexityTests.CountingSimulation
