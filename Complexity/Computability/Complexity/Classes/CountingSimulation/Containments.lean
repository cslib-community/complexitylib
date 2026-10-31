/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.Assembly
public import Complexity.Computability.Complexity.Classes.Time.AcceptCount
public import Complexity.Computability.Complexity.Classes.PP.Time
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Nondeterministic and probabilistic time in deterministic time `2 ^ O(T / √(log T))`

**Conditional** on the interfaces of the counting simulation (#1833): network families for the
accept counts of all finite-state fair-coin machines
(`Cslib.Complexity.CountingSimulation.NetworkFamilies`) and a contraction algorithm
(`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`). Under these hypotheses, for every
time-constructible `T` with `max n 2 ≤ T n`, every problem in `NTIME[T]`, `BPTIME[T]` or
`PPTIME[T]` is decided within time `2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d`.

Each class is reduced to the accept count `A_M(x)` of a fair-coin machine `M` at every padded time
`τ` past a linear clock: `x ∈ L ↔ 0 < A_M(x)` for `NTIME`, and `x ∈ L ↔ 2 ^ τ < 2 * A_M(x)` for
`BPTIME` and `PPTIME` (`Cslib.Complexity.exists_acceptCount_of_mem_NTIME`,
`Cslib.Complexity.exists_acceptCount_of_mem_BPTIME`,
`Turing.MultiTapePTM.decidesByMajorityInTime_iff`). The count is computed by the simulation of
`Cslib.Complexity.CountingSimulation.exists_computableInO_count`, and the comparison is a
polynomial-time function of the padded time and the count.

## Main definitions

* `Cslib.Complexity.CountingSimulation.NetworkFamilies`: network families for all machines.

## Main results

* `Cslib.Complexity.CountingSimulation.exists_decidableInTimeAndSpace_of_mem_NTIME`,
  `exists_decidableInTimeAndSpace_of_mem_BPTIME`, `exists_decidableInTimeAndSpace_of_mem_PPTIME`:
  time `2 ^ O(T / √(log T))` and space polynomial in `T`.
* `Cslib.Complexity.CountingSimulation.NTIME_subset_iUnion_DTIME`, `BPTIME_subset_iUnion_DTIME`,
  `PPTIME_subset_iUnion_DTIME`: the containments in `⋃ C, DTIME (2 ^ (C * T / √⌊log₂ T⌋))`.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing Turing.MultiTapeTM

variable {N : Type} {encN : N ↪ List Bool} {value : N → ℕ} {Admissible : ℕ → ℕ → N → Prop}
  {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- **Network families for all machines**: for every finite-state fair-coin machine, a network
family (`Cslib.Complexity.CountingSimulation.NetworkFamily`) for its accept count
`Turing.MultiTapePTM.acceptCount`. This is the hypothesis supplied by the block-counting step of
#1833. -/
def NetworkFamilies (encN : N ↪ List Bool) (value : N → ℕ) (Admissible : ℕ → ℕ → N → Prop) :
    Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] (M : MultiTapePTM k Bool State),
    Nonempty (NetworkFamily encN value Admissible fun x τ => M.acceptCount x τ)

/-- A problem decided by a polynomial-time comparison of the padded time with the accept count of
a finite-state fair-coin machine, at every padded time past a linear clock, is decided within time
`2 ^ O(T / √(log T))` and space polynomial in `T`. -/
private theorem exists_decidableInTimeAndSpace_of_rule
    (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {k : ℕ} {State : Type} [Finite State]
    (M : MultiTapePTM k Bool State) {c₁ c₂ : ℕ} {rule : ℕ × ℕ → Bool}
    (hrule : ComputableInPolyTime rule (encPair encUnary encNat) encBool) {L : Set α}
    (hL : ∀ a τ, c₁ * T (enc a).length + c₂ ≤ τ →
      (a ∈ L ↔ rule (τ, M.acceptCount (enc a) τ) = true)) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F⟩ := hnet k State M
  obtain ⟨C, d, h⟩ := exists_computableInO_count F A
    (fun x τ => Complexity.acceptCount_le_two_pow) hT hTn (c := c₁ + c₂ + 1) (by omega) hrule
  obtain ⟨K, hK, -⟩ := h.of_encIn_eq enc fun a => rfl
  refine ⟨(K + K + 1) * (C + 1), K + K + 2 * d,
    decidableInTimeAndSpace_iff.mpr ⟨_, hK.mono (fun a => ?_) fun a => ?_, fun a => ?_⟩⟩
  · have h2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have := Nat.mul_two_pow_div_sqrt_log_two_add_le (a := K) (b := K) (C := C) h2
    simp only [Function.comp_apply, Nat.mul_add, Nat.mul_one] at this ⊢
    exact this
  · have h2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have hpow : T (enc a).length ^ d ≤ (T (enc a).length + 1) ^ d :=
      Nat.pow_le_pow_left (Nat.le_succ _) d
    have := Nat.mul_add_one_pow_add_le_pow (a := K) (b := K) (d := d) h2
    simp only [Function.comp_apply]
    calc K * (T (enc a).length ^ d + 1) ≤ K * (T (enc a).length + 1) ^ d + K := by
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) _
      _ ≤ _ := this
  · have h2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have hτ : c₁ * T (enc a).length + c₂ ≤
        paddedTime ((c₁ + c₂ + 1) * T (enc a).length) := by
      refine le_trans ?_ (le_paddedTime _)
      nlinarith
    simp only [Function.comp_apply]
    exact hL a _ hτ

/-- **Nondeterministic time, deterministically** (conditional on the interfaces). For a
time-constructible `T` with `max n 2 ≤ T n`, every problem in `NTIME[T]` is decided within time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d`, by testing whether the accept count of a
fair-coin normal form is positive. -/
theorem exists_decidableInTimeAndSpace_of_mem_NTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ NTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨k, State, _, M, c₁, c₂, hM⟩ := exists_acceptCount_of_mem_NTIME hL
  exact exists_decidableInTimeAndSpace_of_rule hnet A hT hTn M
    (rule := fun p => decide (0 < p.2)) (by fun_prop) fun a τ hτ => by
      rw [hM a τ hτ, decide_eq_true_iff]

/-- **Bounded-error probabilistic time, deterministically** (conditional on the interfaces). For a
time-constructible `T` with `max n 2 ≤ T n`, every problem in `BPTIME[T]` is decided within time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d`, by comparing the accept count with half of
the padded choice strings. -/
theorem exists_decidableInTimeAndSpace_of_mem_BPTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ BPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨k, State, _, M, c₁, c₂, hM⟩ := exists_acceptCount_of_mem_BPTIME hL
  exact exists_decidableInTimeAndSpace_of_rule hnet A hT hTn M
    (rule := fun p => decide (2 ^ p.1 < 2 * p.2)) (by fun_prop) fun a τ hτ => by
      rw [hM a τ hτ, decide_eq_true_iff]

/-- **Unbounded-error probabilistic time, deterministically** (conditional on the interfaces).
For a time-constructible `T` with `max n 2 ≤ T n`, every problem in `PPTIME[T]` is decided within
time `2 ^ (C * T n / √⌊log₂ (T n)⌋)` and space `T n ^ d`, by the strict-majority comparison of
the accept count. -/
theorem exists_decidableInTimeAndSpace_of_mem_PPTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ PPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨c₁, c₂, k, State, _, M, hM⟩ := hL
  refine exists_decidableInTimeAndSpace_of_rule hnet A hT hTn M (c₁ := c₁) (c₂ := c₂)
    (rule := fun p => decide (2 ^ p.1 < 2 * p.2)) (by fun_prop) fun a τ hτ => ?_
  classical
  -- Run the clock up to `τ` at `a` and leave it elsewhere.
  let t' : α → ℕ := fun a' => if a' = a then τ else c₁ * T (enc a').length + c₂
  have hmono (a' : α) : c₁ * T (enc a').length + c₂ ≤ t' a' := by
    by_cases h : a' = a
    · subst h
      simpa only [t', ite_true] using hτ
    · simp only [t', h, ite_false, le_refl]
  have h := (MultiTapePTM.decidesByMajorityInTime_iff.mp (hM.mono hmono) a).2
  simp only [t', ite_true] at h
  rw [h]
  exact decide_eq_true_iff.symm

private theorem mem_iUnion_DTIME_of_exists {L : Set α}
    (h : ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d)) :
    L ∈ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  obtain ⟨C, d, h⟩ := h
  exact Set.mem_iUnion.mpr ⟨C, 1, 0, fun n => T n ^ d,
    ComputableInTimeAndSpace.mono h (fun a => by rw [Nat.one_mul, Nat.add_zero]) fun _ => le_rfl⟩

/-- **`NTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`** (conditional on the interfaces), for a
time-constructible `T` with `max n 2 ≤ T n`. -/
theorem NTIME_subset_iUnion_DTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME_of_exists
    (exists_decidableInTimeAndSpace_of_mem_NTIME hnet A hT hTn hL)

/-- **`BPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`** (conditional on the interfaces), for a
time-constructible `T` with `max n 2 ≤ T n`. -/
theorem BPTIME_subset_iUnion_DTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME_of_exists
    (exists_decidableInTimeAndSpace_of_mem_BPTIME hnet A hT hTn hL)

/-- **`PPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C * T / √⌊log₂ T⌋)]`** (conditional on the interfaces), for a
time-constructible `T` with `max n 2 ≤ T n`. -/
theorem PPTIME_subset_iUnion_DTIME (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME_of_exists
    (exists_decidableInTimeAndSpace_of_mem_PPTIME hnet A hT hTn hL)

end Cslib.Complexity.CountingSimulation
