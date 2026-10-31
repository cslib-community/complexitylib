/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.CountingClasses
import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Complexity.Classes.FunctionTime.Bounds

/-! # Counting classes and strict containments in `DTIME[2 ^ T]`: checked instances

The containments and strict containments at the clock `T n = (n + 1) ^ 2 + 1`, which is
time-constructible and at least `max n 2`, and nonvacuity of the new time-bounded counting
classes through their polynomial-time unions. -/

namespace ComplexityTests.CountingSeparation

open Cslib.Complexity Cslib.Complexity.CountingSimulation Turing.MultiTapeTM

/-- The clock `(n + 1) ^ 2 + 1` is time-constructible. -/
theorem timeConstructible_succ_sq_add_one : TimeConstructible fun n => (n + 1) ^ 2 + 1 :=
  timeConstructible_succ_sq.comp_of_computableInPolyTime (g := fun m => m + 1)
    (ComputableInPolyTime.binary_add.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1)))
    fun _ => Nat.le_succ _

/-- The clock `(n + 1) ^ 2 + 1` is at least `max n 2`. -/
theorem max_le_succ_sq_add_one (n : ℕ) : max n 2 ≤ (n + 1) ^ 2 + 1 :=
  max_le (by nlinarith) (by have := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n); omega)

/-! ### The separating clock -/

example : TimeConstructible fun n => 2 ^ (((n + 1) ^ 2 + 1) / 4) :=
  timeConstructible_succ_sq_add_one.two_pow_div (by norm_num)

example : ¬DTIME encBits (fun n => 2 ^ ((n + 1) ^ 2 + 1)) ⊆ ⋃ C, DTIME encBits fun n =>
    2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two
    timeConstructible_succ_sq_add_one fun n => (le_max_left _ _).trans (max_le_succ_sq_add_one n)

/-! ### Nondeterministic and probabilistic time -/

example : NTIME encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  NTIME_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

example : BPTIME encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  BPTIME_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

example : PPTIME encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  PPTIME_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

/-! ### Parity, modular and exact counting -/

example {α : Type} {enc : α ↪ List Bool} :
    ParityTIME enc (fun n => (n + 1) ^ 2 + 1) ⊆ ⋃ C, DTIME enc fun n =>
      2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  ParityTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

example {α : Type} {enc : α ↪ List Bool} :
    ModTIME 3 enc (fun n => (n + 1) ^ 2 + 1) ⊆ ⋃ C, DTIME enc fun n =>
      2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  ModTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two 3 timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

example {α : Type} {enc : α ↪ List Bool} :
    CeqTIME enc (fun n => (n + 1) ^ 2 + 1) ⊆ ⋃ C, DTIME enc fun n =>
      2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  CeqTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

example : ParityTIME encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ParityTIME_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

example : ModTIME 3 encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ModTIME_ssubset_DTIME_two_pow 3 timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

example : CeqTIME encBits (fun n => (n + 1) ^ 2 + 1) ⊂
    DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  CeqTIME_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one

/-! ### Supporting API -/

example {α : Type} {enc : α ↪ List Bool} : SharpTIME enc (· ^ 1) ⊆ SharpTIME enc (· ^ 2) :=
  SharpTIME_pow_mono (by norm_num)

example {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : f ∈ FTIME enc encOut fun n => (n + 1) ^ 2 + 1) :
    ∃ c, ∀ a, (encOut (f a)).length ≤ c * (((enc a).length + 1) ^ 2 + 1 + 1) := by
  obtain ⟨c, -, -, hl⟩ := FTIME.exists_computableInO hf
  exact ⟨c, hl⟩

/-! ### Nonvacuity through the polynomial-time unions -/

example {α : Type} {enc : α ↪ List Bool} : ∃ d, (∅ : Set α) ∈ ModTIME 3 enc (· ^ d) :=
  mem_ModP_iff_exists_mem_ModTIME.mp (P_subset_ModP (by norm_num) empty_mem_P)

example {α : Type} {enc : α ↪ List Bool} : ∃ d, (∅ : Set α) ∈ ParityTIME enc (· ^ d) := by
  rw [← mem_ParityP_iff_exists_mem_ParityTIME, ← ModP_two]
  exact P_subset_ModP le_rfl empty_mem_P

example {α : Type} {enc : α ↪ List Bool} : ∃ d, (Set.univ : Set α) ∈ CeqTIME enc (· ^ d) := by
  refine mem_CeqP_iff_exists_mem_CeqTIME.mp (coNP_subset_CeqP ?_)
  rw [mem_coNP, Set.compl_univ]
  exact P_subset_NP empty_mem_P

end ComplexityTests.CountingSeparation
