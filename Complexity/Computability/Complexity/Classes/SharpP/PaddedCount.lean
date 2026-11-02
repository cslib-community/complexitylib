/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Complexity.Classes.PP.Time
public import Complexity.Computability.Complexity.Classes.SharpP.Time
public import Complexity.Computability.Complexity.Classes.Time.AcceptCount
import Complexity.Computability.Complexity.Classes.Constructible.UnaryClock
import Complexity.Computability.Machines.Turing.MultiTape.Counting.PaddedClock
import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PolynomialClock
import Complexity.Foundations.Data.Nat.Doubling

/-!
# Padded coin counts in time-bounded counting

The library reduces nondeterministic, bounded-error and majority time to the padded accepting
count of a fair-coin machine (`Turing.MultiTapePTM.acceptCount`): the number of coin strings of a
length `τ` whose replay outputs `[true]`, where a run that halts early ignores its remaining coins
(`Cslib.Complexity.exists_acceptCount_of_mem_NTIME`,
`Cslib.Complexity.exists_acceptCount_of_mem_BPTIME`,
`Turing.MultiTapePTM.decidesByMajorityInTime_iff`). `Cslib.Complexity.SharpTIME` counts accepting
terminal branches of native counting machines instead, without padding.

For a time-constructible `T`, padded counts at a linear clock are `SharpTIME enc T` functions
(`Cslib.Complexity.exists_clock_acceptCount_mem_SharpTIME`). The clock is
`τ n = c * 2 ^ Nat.size (T n)`, which lies between `c * (T n + 1)` and `c * (2 * T n + 1)`. A
deterministic phase writes it in unary within `O(T n)` steps
(`Cslib.Complexity.TimeConstructible.exists_prepare_unaryClock`). The counting machine
`Turing.MultiTapeCTM.PaddedClock.machine` then branches once per coin, continuing after the source
halts, until the clock is exhausted. The clock is chosen before the machine, so several counts
can share it. A clock exactly `c₁ * T n + c₂` would need an exact binary-to-unary conversion in
linear time; the rounded clock suffices below, because each characterization holds at every
clock of at least `c₁ * T n + c₂`.

Hence:

* `NTIME[T]` problems are positivity tests of one `SharpTIME[T]` count
  (`Cslib.Complexity.exists_mem_SharpTIME_of_mem_NTIME`).
* `PPTIME[T]` and `BPTIME[T]` problems are comparisons `g a < 2 * f a` of two `SharpTIME[T]`
  counts, where `g a = 2 ^ τ` is the count of a machine accepting every coin string
  (`Cslib.Complexity.exists_mem_SharpTIME_of_mem_PPTIME`,
  `Cslib.Complexity.exists_mem_SharpTIME_of_mem_BPTIME`).

The converse direction, from terminal counts to padded counts, is
`Turing.MultiTapeCTM.CountingChoice.acceptCount_table_of_halts`.

## Main results

* `Cslib.Complexity.exists_clock_acceptCount_mem_SharpTIME`: padded counts at a linear clock.
* `Cslib.Complexity.exists_mem_SharpTIME_of_mem_NTIME`,
  `Cslib.Complexity.exists_mem_SharpTIME_of_mem_PPTIME`,
  `Cslib.Complexity.exists_mem_SharpTIME_of_mem_BPTIME`: the class-level count tests.
-/

public section

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ} {A : Set α}

/-- **Padded counts at a linear clock are time-bounded terminal counts.** For a time-constructible
`T` and constants `c₁` and `c₂`, there is a clock `τ` with `c₁ * T n + c₂ ≤ τ n ≤ C * T n + C`
such that, for every fair-coin machine `M` with a binary alphabet and finitely many states, the
padded accepting count of `M` with `τ` coins lies in `SharpTIME enc T`. The clock does not depend
on `M`. -/
theorem exists_clock_acceptCount_mem_SharpTIME (hT : TimeConstructible T) (c₁ c₂ : ℕ) :
    ∃ τ : ℕ → ℕ, (∀ n, c₁ * T n + c₂ ≤ τ n) ∧ (∃ C, ∀ n, τ n ≤ C * T n + C) ∧
      ∀ {k : ℕ} {State : Type} [Finite State] (M : MultiTapePTM k Bool State),
        (fun a => M.acceptCount (enc a) (τ (enc a).length)) ∈ SharpTIME enc T := by
  obtain ⟨r, P, hP, prepare, C, hprepare⟩ := hT.exists_prepare_unaryClock (c₁ + c₂)
  have hupper (n : ℕ) : (c₁ + c₂) * 2 ^ Nat.size (T n) ≤
      2 * (c₁ + c₂) * T n + 2 * (c₁ + c₂) := by
    have := Nat.mul_le_mul_left (c₁ + c₂) (Nat.two_pow_size_le (T n))
    have e : 2 * (c₁ + c₂) * T n + 2 * (c₁ + c₂) =
        (c₁ + c₂) * (2 * T n + 1) + (c₁ + c₂) := by ring
    omega
  refine ⟨fun n => (c₁ + c₂) * 2 ^ Nat.size (T n), fun n => ?_, ⟨2 * (c₁ + c₂), hupper⟩,
    fun {k State} _ M => ?_⟩
  · have h : (c₁ + c₂) * (T n + 1) ≤ (c₁ + c₂) * 2 ^ Nat.size (T n) :=
      Nat.mul_le_mul_left _ (Nat.lt_size_self _)
    have e : (c₁ + c₂) * (T n + 1) = c₁ * T n + c₂ + (c₂ * T n + c₁) := by ring
    rw [e] at h
    change c₁ * T n + c₂ ≤ (c₁ + c₂) * 2 ^ Nat.size (T n)
    omega
  · let compiled := MultiTapeCTM.PaddedClock.compile M (prepare.extendTapes (Fin.natAddEmb k))
    refine ⟨C + 2 * (c₁ + c₂), C + 2 * (c₁ + c₂) + 1, k + r + 1, P ⊕ Option State,
      inferInstance, compiled, MultiTapeCTM.PaddedClock.nonblocking_compile _ _, fun a => ?_⟩
    have hready := MultiTapePTM.PolynomialClock.prepare_runFrom (k := k) prepare (enc a)
      (List.replicate ((c₁ + c₂) * 2 ^ Nat.size (T (enc a).length)) true)
      (C * T (enc a).length + C) (hprepare (enc a))
    obtain ⟨hhalt, hcount⟩ := MultiTapeCTM.PaddedClock.haltsWithin_acceptCount_compile M
      (prepare.extendTapes (Fin.natAddEmb k)) (enc a) _ _ hready
    have hle : C * T (enc a).length + C + ((c₁ + c₂) * 2 ^ Nat.size (T (enc a).length) + 1) ≤
        (C + 2 * (c₁ + c₂)) * T (enc a).length + (C + 2 * (c₁ + c₂) + 1) := by
      have := hupper (enc a).length
      have e : (C + 2 * (c₁ + c₂)) * T (enc a).length + (C + 2 * (c₁ + c₂) + 1) =
          C * T (enc a).length + C + (2 * (c₁ + c₂) * T (enc a).length + 2 * (c₁ + c₂)) + 1 := by
        ring
      omega
    refine ⟨hhalt.mono hle, ?_⟩
    change compiled.branchCount (· == [true]) _ _ = _
    rw [hhalt.branchCount_eq hle]
    exact hcount

/-- **`NTIME[T]` as a positive count.** For a time-constructible `T`, every problem in
`NTIME enc T` consists of the instances with a positive count `f a`, for some `f` in
`SharpTIME enc T`. -/
theorem exists_mem_SharpTIME_of_mem_NTIME (hT : TimeConstructible T) (hA : A ∈ NTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∀ a, a ∈ A ↔ 0 < f a := by
  obtain ⟨k, State, _, M, c₁, c₂, hM⟩ := exists_acceptCount_of_mem_NTIME hA
  obtain ⟨τ, hτ, -, hmem⟩ := exists_clock_acceptCount_mem_SharpTIME (enc := enc) hT c₁ c₂
  exact ⟨_, hmem M, fun a => hM a _ (hτ _)⟩

/-- **`PPTIME[T]` as a comparison of two counts.** For a time-constructible `T`, every problem in
`PPTIME enc T` consists of the instances with `g a < 2 * f a`, for some `f` and `g` in
`SharpTIME enc T`. Here `f` counts accepting coin strings at a common linear clock `τ` and
`g a = 2 ^ τ` counts all of them. -/
theorem exists_mem_SharpTIME_of_mem_PPTIME (hT : TimeConstructible T) (hA : A ∈ PPTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∀ a, a ∈ A ↔ g a < 2 * f a := by
  obtain ⟨c₁, c₂, k, State, _, M, hM⟩ := hA
  obtain ⟨τ, hτ, -, hmem⟩ := exists_clock_acceptCount_mem_SharpTIME (enc := enc) hT c₁ (c₂ + 1)
  refine ⟨_, hmem M, _, hmem MultiTapePTM.acceptAll, fun a => ?_⟩
  have hdecide := MultiTapePTM.decidesByMajorityInTime_iff.mp
    (hM.mono (t' := fun a => τ (enc a).length) fun a => (Nat.le_succ _).trans (hτ _)) a
  obtain ⟨m, hm⟩ : ∃ m, τ (enc a).length = m + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.lt_of_lt_of_le (Nat.succ_pos _) (hτ _))
  rw [hdecide.2]
  change _ ↔ MultiTapePTM.acceptAll.acceptCount (enc a) (τ (enc a).length) < _
  rw [hm, MultiTapePTM.acceptCount_acceptAll]

/-- **`BPTIME[T]` as a comparison of two counts**, through `Cslib.Complexity.BPTIME_subset_PPTIME`.
-/
theorem exists_mem_SharpTIME_of_mem_BPTIME (hT : TimeConstructible T) (hA : A ∈ BPTIME enc T) :
    ∃ f ∈ SharpTIME enc T, ∃ g ∈ SharpTIME enc T, ∀ a, a ∈ A ↔ g a < 2 * f a :=
  exists_mem_SharpTIME_of_mem_PPTIME hT (BPTIME_subset_PPTIME hA)

end Cslib.Complexity
