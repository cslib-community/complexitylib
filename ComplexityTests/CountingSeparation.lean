/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.CountingClasses
import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Complexity.Classes.FunctionTime.Bounds
import Complexity.Foundations.Data.Nat.SqrtLog.Factor

/-! # Counting classes and strict containments in `DTIME[2 ^ T]`: checked instances

The containments and strict containments at the clock `T n = (n + 1) ^ 2 + 1`, which is
time-constructible and at least `max n 2`, the sharper strict containments at time
`T n * ⌊√⌊√⌊log₂ (T n)⌋⌋⌋`, and nonvacuity of the new time-bounded counting classes through their
polynomial-time unions. -/

namespace ComplexityTests.CountingSeparation

open Cslib.Complexity Cslib.Complexity.CountingSimulation Filter Turing.MultiTapeTM

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

/-- The clock `(n + 1) ^ 2 + 1` tends to infinity. -/
theorem tendsto_succ_sq_add_one : Tendsto (fun n : ℕ => (n + 1) ^ 2 + 1) atTop atTop :=
  tendsto_atTop_mono (fun n => (le_max_left _ _).trans (max_le_succ_sq_add_one n)) tendsto_id

example : ¬DTIME encBits (fun n => 2 ^ ((n + 1) ^ 2 + 1)) ⊆ ⋃ C, DTIME encBits fun n =>
    2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two
    timeConstructible_succ_sq_add_one (fun n => (le_max_left _ _).trans (max_le_succ_sq_add_one n))
    fun C => tendsto_succ_sq_add_one.eventually (Nat.eventually_mul_le_mul_sqrt_log_two C)

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

/-! ### Sharper separations at time `T * ⌊√⌊√⌊log₂ T⌋⌋⌋` -/

/-- The clock `(n + 1) ^ 2 + 1` times the fourth root of its logarithm is time-constructible. -/
theorem timeConstructible_succ_sq_add_one_mul_sqrt_sqrt_log_two :
    TimeConstructible fun n =>
      ((n + 1) ^ 2 + 1) * Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  timeConstructible_succ_sq_add_one.mul_sqrt_sqrt_log_two fun n =>
    (le_max_right _ _).trans (max_le_succ_sq_add_one n)

/-- The fourth-root factor is unbounded, so these separations are strictly sharper than those at
time `T`. -/
example : Tendsto (fun n : ℕ => Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) atTop atTop :=
  (tendsto_atTop_atTop.2 fun b => ⟨b * b, fun _ hm => Nat.le_sqrt.2 hm⟩).comp
    (Nat.tendsto_sqrt_log_two_atTop.comp tendsto_succ_sq_add_one)

example : NTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  NTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

/-- The noncontainment `DTIME[2 ^ T] ⊄ NTIME[T ⌊√⌊√⌊log₂ T⌋⌋⌋]`. -/
example : ¬DTIME encBits (fun n => 2 ^ ((n + 1) ^ 2 + 1)) ⊆ NTIME encBits fun n =>
    ((n + 1) ^ 2 + 1) * Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  not_subset_of_ssubset (NTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow
    timeConstructible_succ_sq_add_one max_le_succ_sq_add_one)

example : BPTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  BPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

example : PPTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  PPTIME_mul_sqrt_sqrt_log_two_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

/-- The fourth-root factor of `(n + 1) ^ 2 + 1` is positive. -/
theorem one_le_sqrt_sqrt_log_two_succ_sq_add_one (n : ℕ) :
    1 ≤ Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  Nat.one_le_sqrt_sqrt_log_two ((le_max_right _ _).trans (max_le_succ_sq_add_one n))

/-- The fourth-root factor of `(n + 1) ^ 2 + 1` is `o(√⌊log₂ ((n + 1) ^ 2 + 1)⌋)`. -/
theorem eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le (C : ℕ) :
    ∀ᶠ n in atTop, C * Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) ≤
      Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)) :=
  tendsto_succ_sq_add_one.eventually (Nat.eventually_mul_sqrt_sqrt_log_two_le C)

example : ParityTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ParityTIME_mul_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one
    timeConstructible_succ_sq_add_one_mul_sqrt_sqrt_log_two
    one_le_sqrt_sqrt_log_two_succ_sq_add_one eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le

example : ModTIME 3 encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ModTIME_mul_ssubset_DTIME_two_pow 3 timeConstructible_succ_sq_add_one max_le_succ_sq_add_one
    timeConstructible_succ_sq_add_one_mul_sqrt_sqrt_log_two
    one_le_sqrt_sqrt_log_two_succ_sq_add_one eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le

example : CeqTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  CeqTIME_mul_ssubset_DTIME_two_pow timeConstructible_succ_sq_add_one max_le_succ_sq_add_one
    timeConstructible_succ_sq_add_one_mul_sqrt_sqrt_log_two
    one_le_sqrt_sqrt_log_two_succ_sq_add_one eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le

/-- The count-test separation at time `T * h`, applied to the class of problems defined by equal
counts (the definition of `C₌TIME`, unfolded). -/
example : {A : Set (List Bool) | ∃ f ∈ SharpTIME encBits (fun n => ((n + 1) ^ 2 + 1) *
    Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))), ∃ g ∈ SharpTIME encBits (fun n =>
      ((n + 1) ^ 2 + 1) * Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))),
        ∀ x, x ∈ A ↔ f x = g x} ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_mul timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one timeConstructible_succ_sq_add_one_mul_sqrt_sqrt_log_two
    one_le_sqrt_sqrt_log_two_succ_sq_add_one eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le
    fun _ ⟨f, hf, g, hg, hA⟩ => ⟨f, hf, g, hg, fun p => decide (p.1 = p.2),
      ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
        (ComputableInPolyTime.snd encNat encNat), fun x => by simp [hA x]⟩

/-- The same count-test separation at time `T`. -/
example : {A : Set (List Bool) | ∃ f ∈ SharpTIME encBits (fun n => (n + 1) ^ 2 + 1),
    ∃ g ∈ SharpTIME encBits (fun n => (n + 1) ^ 2 + 1), ∀ x, x ∈ A ↔ f x = g x} ⊂
      DTIME encBits fun n => 2 ^ ((n + 1) ^ 2 + 1) :=
  ssubset_DTIME_two_pow_of_forall_mem_SharpTIME_self timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one fun _ ⟨f, hf, g, hg, hA⟩ => ⟨f, hf, g, hg, fun p => decide (p.1 = p.2),
      ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encNat encNat)
        (ComputableInPolyTime.snd encNat encNat), fun x => by simp [hA x]⟩

/-- A factor `g (T n)` with `g = o(√log)` on `ℕ` satisfies the hypothesis `h = o(√⌊log₂ T⌋)`,
since `T` tends to infinity. -/
example {g : ℕ → ℕ} (hg : ∀ C, ∀ᶠ m in atTop, C * g m ≤ Nat.sqrt (Nat.log 2 m)) (C : ℕ) :
    ∀ᶠ n in atTop, C * g ((n + 1) ^ 2 + 1) ≤ Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)) :=
  tendsto_succ_sq_add_one.eventually (hg C)

/-- The general hypothesis `t / √⌊log₂ t⌋ = o(T)` at `t = T * h`. -/
example (C : ℕ) : ∀ᶠ n in atTop,
    C * (((n + 1) ^ 2 + 1) * Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1)))) ≤
      ((n + 1) ^ 2 + 1) * Nat.sqrt (Nat.log 2 (((n + 1) ^ 2 + 1) *
        Nat.sqrt (Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))))) :=
  (eventually_mul_sqrt_sqrt_log_two_succ_sq_add_one_le C).mono fun n hn =>
    Nat.mul_mul_le_mul_sqrt_log_two_mul (one_le_sqrt_sqrt_log_two_succ_sq_add_one n) hn

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
