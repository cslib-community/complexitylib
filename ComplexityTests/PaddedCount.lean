/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SharpP.PaddedCount
import Complexity.Computability.Complexity.Classes.Constructible.UnaryClock
import Complexity.Computability.Machines.Turing.MultiTape.Counting.PaddedClock
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay
import Complexity.Foundations.Data.Nat.Doubling
import ComplexityTests.CountingSeparation

/-! # Padded coin counts as `SharpTIME` functions: checked instances

The unary clock of `Cslib.Complexity.TimeConstructible.exists_prepare_unaryClock`, the padded
count bridge and the class-level count tests, at the clock `T n = (n + 1) ^ 2 + 1`. The
always-accepting table gives a nonvacuous instance: its padded count is positive. -/

namespace ComplexityTests.PaddedCount

open Cslib.Complexity Turing ComplexityTests.CountingSeparation

/-! ### The clock -/

/-- The rounded clock is between `c * (m + 1)` and `c * (2 * m + 1)`. -/
example (c m : ℕ) : c * (m + 1) ≤ c * 2 ^ Nat.size m ∧ c * 2 ^ Nat.size m ≤ c * (2 * m + 1) :=
  ⟨Nat.mul_le_mul_left c (Nat.lt_size_self m), Nat.mul_le_mul_left c (Nat.two_pow_size_le m)⟩

example : ∃ (r : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM (r + 1) Bool State)
    (C : ℕ), ∀ input,
      machine.runFrom (machine.initCfg input) (C * ((input.length + 1) ^ 2 + 1) + C) =
        wordsCfg input none (Function.update (fun _ => []) (Fin.last r)
          (List.replicate (3 * 2 ^ Nat.size ((input.length + 1) ^ 2 + 1)) true)) [] :=
  timeConstructible_succ_sq_add_one.exists_prepare_unaryClock 3

/-! ### The always-accepting table -/

example : MultiTapePTM.acceptAll.acceptCount [true, false] 3 = 8 :=
  MultiTapePTM.acceptCount_acceptAll _ 2

example : MultiTapePTM.acceptAll.acceptCount [] 0 = 0 := by
  rw [MultiTapePTM.acceptCount, acceptCount_zero]
  rfl

/-! ### The bridge -/

/-- A padded count at a linear clock is a positive `SharpTIME` function. -/
example {α : Type} {enc : α ↪ List Bool} :
    ∃ f ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1), ∀ a, 0 < f a := by
  obtain ⟨τ, hτ, -, hmem⟩ := exists_clock_acceptCount_mem_SharpTIME (enc := enc)
    timeConstructible_succ_sq_add_one 0 1
  refine ⟨_, hmem MultiTapePTM.acceptAll, fun a => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, τ (enc a).length = m + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.lt_of_lt_of_le (by norm_num) (hτ (enc a).length))
  simp only [hm, MultiTapePTM.acceptCount_acceptAll]
  positivity

/-- The counting phase alone: a clock of `n` cells and the coin strings of length `n`. -/
example {k : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (input : List Bool) (n : ℕ) :
    (MultiTapeCTM.PaddedClock.machine M 0).acceptCount (n + 1)
        (MultiTapeCTM.PaddedClock.config 0 (Cfg.init M.initial input)
          (tapeOfList (List.replicate n true)) 0) =
      M.acceptCount input n := by
  rw [(MultiTapeCTM.PaddedClock.haltsWithin_acceptCount_machine M 0 n _ _ 0
    (fun i hi => by simp [hi]) (by simp)).2, MultiTapePTM.acceptCount]
  simp only [Cslib.Complexity.acceptCount, MultiTapePTM.runClosedCoins_eq_output_stepCoins]

/-! ### Count tests for nondeterministic, majority and bounded-error time -/

example {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ NTIME enc fun n => (n + 1) ^ 2 + 1) :
    ∃ f ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1), ∀ a, a ∈ A ↔ 0 < f a :=
  exists_mem_SharpTIME_of_mem_NTIME timeConstructible_succ_sq_add_one hA

example {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PPTIME enc fun n => (n + 1) ^ 2 + 1) :
    ∃ f ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1),
      ∃ g ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1), ∀ a, a ∈ A ↔ g a < 2 * f a :=
  exists_mem_SharpTIME_of_mem_PPTIME timeConstructible_succ_sq_add_one hA

example {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ BPTIME enc fun n => (n + 1) ^ 2 + 1) :
    ∃ f ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1),
      ∃ g ∈ SharpTIME enc (fun n => (n + 1) ^ 2 + 1), ∀ a, a ∈ A ↔ g a < 2 * f a :=
  exists_mem_SharpTIME_of_mem_BPTIME timeConstructible_succ_sq_add_one hA

end ComplexityTests.PaddedCount
