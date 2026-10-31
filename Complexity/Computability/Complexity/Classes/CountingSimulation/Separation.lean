/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastSimulation
public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Computability.Complexity.Classes.Constructible.TwoPow
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Strict containments in `DTIME[2 ^ T]` from the counting simulation

For time-constructible `T` with `max n 2 ≤ T n`, the counting simulation of #1833 places
`NTIME[T]`, `BPTIME[T]` and `PPTIME[T]` in `⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`
(`Cslib.Complexity.CountingSimulation.NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two` and its
siblings). That union lies in `DTIME[2 ^ T]` but does not exhaust it. Hence each of these classes
is strictly contained in `DTIME[2 ^ T]` on bit strings.

**The separating language** is the clocked diagonal `Cslib.Complexity.timeDiagonal J` of
`Complexity.Computability.Complexity.Classes.Hierarchy.Time`, with the clock
`J n = 2 ^ (T n / 4)`. This clock is time-constructible
(`Cslib.Complexity.TimeConstructible.two_pow_div`). One language serves every constant `C`:

* it is decidable within time `O((n + 1) ^ 5 * (J n + 1) ^ 3)`, which is `O(2 ^ T n)` because
  `(n + 1) ^ 5 ≤ (T n + 1) ^ 5 = O(2 ^ (T n / 4))`;
* for each `C` and `c`, eventually `c * 2 ^ (C T n / √⌊log₂ T n⌋) + c ≤ J n`, since
  `√⌊log₂ T n⌋ ≥ 8 C` and `2 c ≤ 2 ^ (T n / 8)` from some length on, so the diagonal argument
  (`Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME`) excludes it from each
  `DTIME[2 ^ (C T / √⌊log₂ T⌋)]`.

The polynomial overhead of the native universal machine is absorbed by the gap between
`2 ^ (T / 4)` and `2 ^ T`. No faster universal simulation is assumed.

The same separation applies to every class decided by polynomial-time tests of exact counts in
`Cslib.Complexity.SharpTIME`, such as `⊕TIME[T]`, `Mod_kTIME[T]` and `C₌TIME[T]`
(`Complexity.Computability.Complexity.Classes.CountingSimulation.CountingClasses`).

## Main results

* `Cslib.Complexity.CountingSimulation.iUnion_DTIME_two_pow_div_sqrt_log_two_subset`: the union
  lies in `DTIME[2 ^ T]`.
* `DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: one language of
  `DTIME[2 ^ T]` lies outside every `DTIME[2 ^ (C T / √⌊log₂ T⌋)]`.
* `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_subset_iUnion`: every class inside
  the union is strictly contained in `DTIME[2 ^ T]`.
* `Cslib.Complexity.CountingSimulation.NTIME_ssubset_DTIME_two_pow`,
  `BPTIME_ssubset_DTIME_two_pow`, `PPTIME_ssubset_DTIME_two_pow`: the strict containments.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Filter Turing.MultiTapeTM

variable {T : ℕ → ℕ}

/-- From some length on, `√⌊log₂ (T n)⌋` is at least any given constant. -/
private theorem eventually_le_sqrt_log_two (hTn : ∀ n, n ≤ T n) (C : ℕ) :
    ∀ᶠ n in atTop, C ≤ Nat.sqrt (Nat.log 2 (T n)) := by
  filter_upwards [eventually_ge_atTop (2 ^ (C * C))] with n hn
  exact Nat.le_sqrt.mpr (Nat.le_log_of_pow_le one_lt_two (hn.trans (hTn n)))

/-- **The union lies in `DTIME[2 ^ T]`**: each exponent `C T / √⌊log₂ T⌋` is eventually at
most `T`. -/
theorem iUnion_DTIME_two_pow_div_sqrt_log_two_subset {α : Type} {enc : α ↪ List Bool}
    (hTn : ∀ n, n ≤ T n) :
    (⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)))) ⊆
      DTIME enc fun n => 2 ^ T n := by
  refine Set.iUnion_subset fun C => DTIME_mono_of_eventually_le ?_
  filter_upwards [eventually_le_sqrt_log_two hTn C] with n hn
  exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ hn))

/-- The upper resource bound of the clocked diagonal with clock `2 ^ (T n / 4)` is
`O(2 ^ T n)`. -/
private theorem exists_diagonal_bound_le (hTn : ∀ n, n ≤ T n) :
    ∃ K, ∀ n, (n + 1) ^ 5 * (2 ^ (T n / 4) + 1) ^ 3 ≤ K * 2 ^ T n + K := by
  obtain ⟨C₀, hC₀⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun m => (4 * m + 4) ^ 5) (by fun_prop)
  refine ⟨8 * C₀, fun n => ?_⟩
  set m := T n / 4 with hm
  have h₁ : n + 1 ≤ 4 * m + 4 := by
    have := hTn n
    omega
  have h₂ : (n + 1) ^ 5 ≤ C₀ * 2 ^ m := (Nat.pow_le_pow_left h₁ 5).trans (hC₀ m)
  have h₃ : (2 ^ m + 1) ^ 3 ≤ 8 * 2 ^ (3 * m) := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc (2 ^ m + 1) ^ 3 ≤ (2 * 2 ^ m) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * 2 ^ (3 * m) := by ring
  have h₄ : 2 ^ (m + 3 * m) ≤ 2 ^ T n := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (n + 1) ^ 5 * (2 ^ m + 1) ^ 3 ≤ C₀ * 2 ^ m * (8 * 2 ^ (3 * m)) := Nat.mul_le_mul h₂ h₃
    _ = 8 * C₀ * 2 ^ (m + 3 * m) := by ring
    _ ≤ 8 * C₀ * 2 ^ T n + 8 * C₀ := (Nat.mul_le_mul_left _ h₄).trans (Nat.le_add_right _ _)

/-- The clock `2 ^ (T n / 4)` eventually exceeds every `c * 2 ^ (C T n / √⌊log₂ T n⌋) + c`. -/
private theorem eventually_le_two_pow_div_four (hTn : ∀ n, n ≤ T n) (C c : ℕ) :
    ∀ᶠ n in atTop, c * 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) + c ≤ 2 ^ (T n / 4) := by
  filter_upwards [eventually_le_sqrt_log_two hTn (8 * C),
    eventually_ge_atTop (16 * c + 16)] with n hs hn
  set s := Nat.sqrt (Nat.log 2 (T n))
  set u := T n / 8 with hu
  -- the exponent is at most `T n / 8`
  have hexp : C * T n / s ≤ u := by
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · simp
    · refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      have hdiv := Nat.div_mul_le_self (C * T n) s
      have : C * T n / s * (8 * C) ≤ C * T n := (Nat.mul_le_mul_left _ hs).trans hdiv
      nlinarith
  -- `2 c` is below `2 ^ u`
  have hcu : 2 * c ≤ 2 ^ u := by
    have : 2 * c + 1 ≤ u := by
      have := hTn n
      omega
    exact (Nat.le_succ _).trans (this.trans Nat.lt_two_pow_self.le)
  have hu2 : 2 ^ u * 2 ^ u ≤ 2 ^ (T n / 4) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc c * 2 ^ (C * T n / s) + c ≤ c * 2 ^ u + c * 2 ^ u :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp))
          (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
    _ = 2 * c * 2 ^ u := by ring
    _ ≤ 2 ^ u * 2 ^ u := Nat.mul_le_mul_right _ hcu
    _ ≤ 2 ^ (T n / 4) := hu2

/-- **One language of `DTIME[2 ^ T]` outside every `DTIME[2 ^ (C T / √⌊log₂ T⌋)]`**, for a
time-constructible `T` with `n ≤ T n`: the clocked diagonal with clock `2 ^ (T n / 4)`. -/
theorem DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two
    (hT : TimeConstructible T) (hTn : ∀ n, n ≤ T n) :
    ¬DTIME encBits (fun n => 2 ^ T n) ⊆
      ⋃ C, DTIME encBits fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  intro h
  obtain ⟨K, hK⟩ := exists_diagonal_bound_le hTn
  have hmem := DTIME_mono_of_le_mul_add hK
    (setOf_timeDiagonal_mem_DTIME (hT.two_pow_div (by norm_num : 0 < 4)))
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp (h hmem)
  exact setOf_timeDiagonal_notMem_DTIME (eventually_le_two_pow_div_four hTn C) hC

/-- **Strict containment in `DTIME[2 ^ T]`** of every class of problems on bit strings inside
`⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`, for a time-constructible `T` with `n ≤ T n`. -/
theorem ssubset_DTIME_two_pow_of_subset_iUnion {𝒞 : Set (Set (List Bool))}
    (hT : TimeConstructible T) (hTn : ∀ n, n ≤ T n)
    (h : 𝒞 ⊆ ⋃ C, DTIME encBits fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n)))) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  ⟨h.trans (iUnion_DTIME_two_pow_div_sqrt_log_two_subset hTn), fun hsub =>
    DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT hTn (hsub.trans h)⟩

private theorem le_of_max_le (hTn : ∀ n, max n 2 ≤ T n) (n : ℕ) : n ≤ T n :=
  (le_max_left _ _).trans (hTn n)

/-- **`NTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem NTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_subset_iUnion hT (le_of_max_le hTn)
    (NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT hTn)

/-- **`BPTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem BPTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_subset_iUnion hT (le_of_max_le hTn)
    (BPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT hTn)

/-- **`PPTIME[T] ⊊ DTIME[2 ^ T]`** for time-constructible `T` with `max n 2 ≤ T n`. -/
theorem PPTIME_ssubset_DTIME_two_pow (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME encBits T ⊂ DTIME encBits fun n => 2 ^ T n :=
  ssubset_DTIME_two_pow_of_subset_iUnion hT (le_of_max_le hTn)
    (PPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT hTn)

end Cslib.Complexity.CountingSimulation
