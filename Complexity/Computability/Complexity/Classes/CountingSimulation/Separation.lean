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

For time-constructible `T` with `max n 2 ≤ T n`, the counting simulation of #1833 places counting
classes such as `NTIME[T]`, `BPTIME[T]` and `PPTIME[T]` in
`⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`. That union lies in `DTIME[2 ^ T]` but does not exhaust it.
Hence every class inside it is strictly contained in `DTIME[2 ^ T]` on bit strings.

The same holds for the union at a second bound `t` whose scale is `o(T)`:
`t / √⌊log₂ t⌋ = o(T)`, stated as `C * t n ≤ T n * √⌊log₂ (t n)⌋` eventually for every `C`. The
statements below take this hypothesis. `t = T` satisfies it when `n ≤ T n`
(`Nat.eventually_mul_le_mul_sqrt_log_two`), and so does `t = T * h` for a factor `h ≥ 1` with
`h = o(√⌊log₂ T⌋)` (`Nat.mul_mul_le_mul_sqrt_log_two_mul`). The hypothesis must hold for every
`C` because the constant of the counting simulation depends on the simulated machine. For
`h = ε √⌊log₂ T⌋` the exponents `C T h / √⌊log₂ (T h)⌋` are about `C ε T`, which no single clock
below `2 ^ T` beats for every `C`.

**The separating language** is the clocked diagonal `Cslib.Complexity.timeDiagonal J` of
`Complexity.Computability.Complexity.Classes.Hierarchy.Time`, with the clock
`J n = 2 ^ (T n / 4)`. This clock is time-constructible
(`Cslib.Complexity.TimeConstructible.two_pow_div`). One language serves every constant `C`:

* it is decidable within time `O((n + 1) ^ 5 * (J n + 1) ^ 3)`, which is `O(2 ^ T n)` because
  `(n + 1) ^ 5 ≤ (T n + 1) ^ 5 = O(2 ^ (T n / 4))`;
* for each `C` and `c`, eventually `c * 2 ^ (C t n / √⌊log₂ t n⌋) + c ≤ J n`, since the exponent
  is at most `T n / 8` and `2 c ≤ 2 ^ (T n / 8)` from some length on, so the diagonal argument
  (`Cslib.Complexity.setOf_timeDiagonal_notMem_DTIME`) excludes it from each
  `DTIME[2 ^ (C t / √⌊log₂ t⌋)]`.

The polynomial overhead of the native universal machine is absorbed by the gap between
`2 ^ (T / 4)` and `2 ^ T`. No faster universal simulation is assumed.

The separation is applied in
`Complexity.Computability.Complexity.Classes.CountingSimulation.CountingClasses` to every class
decided by polynomial-time tests of exact counts in `Cslib.Complexity.SharpTIME`: `⊕TIME`,
`Mod_kTIME`, `C₌TIME`, `NTIME`, `BPTIME` and `PPTIME`, at time `T` and at time `T * h`.

## Main results

* `Cslib.Complexity.CountingSimulation.iUnion_DTIME_two_pow_div_sqrt_log_two_subset`: the union
  lies in `DTIME[2 ^ T]`.
* `DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: one language of
  `DTIME[2 ^ T]` lies outside every `DTIME[2 ^ (C t / √⌊log₂ t⌋)]`.
* `Cslib.Complexity.CountingSimulation.ssubset_DTIME_two_pow_of_subset_iUnion`: every class inside
  the union is strictly contained in `DTIME[2 ^ T]`.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Filter Turing.MultiTapeTM

variable {T t : ℕ → ℕ}

/-- **The union lies in `DTIME[2 ^ T]`** when `t / √⌊log₂ t⌋ = o(T)`, that is when
`C * t n ≤ T n * √⌊log₂ (t n)⌋` eventually for every `C`: each exponent `C t / √⌊log₂ t⌋` is
eventually at most `T`. -/
theorem iUnion_DTIME_two_pow_div_sqrt_log_two_subset {α : Type} {enc : α ↪ List Bool}
    (hTt : ∀ C, ∀ᶠ n in atTop, C * t n ≤ T n * Nat.sqrt (Nat.log 2 (t n))) :
    (⋃ C, DTIME enc fun n => 2 ^ (C * t n / Nat.sqrt (Nat.log 2 (t n)))) ⊆
      DTIME enc fun n => 2 ^ T n := by
  refine Set.iUnion_subset fun C => DTIME_mono_of_eventually_le ?_
  filter_upwards [hTt C] with n hn
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.div_le_of_le_mul (hn.trans_eq (Nat.mul_comm _ _)))

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

/-- The clock `2 ^ (T n / 4)` eventually exceeds every `c * 2 ^ e n + c` whose exponent is
eventually at most `T n / 8`. -/
private theorem eventually_le_two_pow_div_four (hTn : ∀ n, n ≤ T n) {e : ℕ → ℕ}
    (he : ∀ᶠ n in atTop, 8 * e n ≤ T n) (c : ℕ) :
    ∀ᶠ n in atTop, c * 2 ^ e n + c ≤ 2 ^ (T n / 4) := by
  filter_upwards [he, eventually_ge_atTop (16 * c + 16)] with n he hn
  set u := T n / 8 with hu
  have hexp : e n ≤ u := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  -- `2 c` is below `2 ^ u`
  have hcu : 2 * c ≤ 2 ^ u := by
    have : 2 * c + 1 ≤ u := by
      have := hTn n
      omega
    exact (Nat.le_succ _).trans (this.trans Nat.lt_two_pow_self.le)
  have hu2 : 2 ^ u * 2 ^ u ≤ 2 ^ (T n / 4) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc c * 2 ^ e n + c ≤ c * 2 ^ u + c * 2 ^ u :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hexp))
          (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
    _ = 2 * c * 2 ^ u := by ring
    _ ≤ 2 ^ u * 2 ^ u := Nat.mul_le_mul_right _ hcu
    _ ≤ 2 ^ (T n / 4) := hu2

/-- The exponent `C t / √⌊log₂ t⌋` is eventually at most `T / 8` when
`t / √⌊log₂ t⌋ = o(T)`. -/
private theorem eventually_eight_mul_div_sqrt_log_two_le
    (hTt : ∀ C, ∀ᶠ n in atTop, C * t n ≤ T n * Nat.sqrt (Nat.log 2 (t n))) (C : ℕ) :
    ∀ᶠ n in atTop, 8 * (C * t n / Nat.sqrt (Nat.log 2 (t n))) ≤ T n := by
  filter_upwards [hTt (8 * C)] with n hn
  set s := Nat.sqrt (Nat.log 2 (t n))
  rcases Nat.eq_zero_or_pos s with hs | hs
  · simp [hs]
  refine Nat.le_of_mul_le_mul_right ?_ hs
  calc 8 * (C * t n / s) * s = 8 * (C * t n / s * s) := Nat.mul_assoc _ _ _
    _ ≤ 8 * (C * t n) := Nat.mul_le_mul_left 8 (Nat.div_mul_le_self _ _)
    _ = 8 * C * t n := (Nat.mul_assoc _ _ _).symm
    _ ≤ T n * s := hn

/-- **One language of `DTIME[2 ^ T]` outside every `DTIME[2 ^ (C t / √⌊log₂ t⌋)]`**, for a
time-constructible `T` with `n ≤ T n` and a bound `t` with `t / √⌊log₂ t⌋ = o(T)`: the clocked
diagonal with clock `2 ^ (T n / 4)`. -/
theorem DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two
    (hT : TimeConstructible T) (hTn : ∀ n, n ≤ T n)
    (hTt : ∀ C, ∀ᶠ n in atTop, C * t n ≤ T n * Nat.sqrt (Nat.log 2 (t n))) :
    ¬DTIME encBits (fun n => 2 ^ T n) ⊆
      ⋃ C, DTIME encBits fun n => 2 ^ (C * t n / Nat.sqrt (Nat.log 2 (t n))) := by
  intro h
  obtain ⟨K, hK⟩ := exists_diagonal_bound_le hTn
  have hmem := DTIME_mono_of_le_mul_add hK
    (setOf_timeDiagonal_mem_DTIME (hT.two_pow_div (by norm_num : 0 < 4)))
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp (h hmem)
  exact setOf_timeDiagonal_notMem_DTIME
    (eventually_le_two_pow_div_four hTn (eventually_eight_mul_div_sqrt_log_two_le hTt C)) hC

/-- **Strict containment in `DTIME[2 ^ T]`** of every class of problems on bit strings inside
`⋃ C, DTIME[2 ^ (C t / √⌊log₂ t⌋)]`, for a time-constructible `T` with `n ≤ T n` and a bound `t`
with `t / √⌊log₂ t⌋ = o(T)`. -/
theorem ssubset_DTIME_two_pow_of_subset_iUnion {𝒞 : Set (Set (List Bool))}
    (hT : TimeConstructible T) (hTn : ∀ n, n ≤ T n)
    (hTt : ∀ C, ∀ᶠ n in atTop, C * t n ≤ T n * Nat.sqrt (Nat.log 2 (t n)))
    (h : 𝒞 ⊆ ⋃ C, DTIME encBits fun n => 2 ^ (C * t n / Nat.sqrt (Nat.log 2 (t n)))) :
    𝒞 ⊂ DTIME encBits fun n => 2 ^ T n :=
  ⟨h.trans (iUnion_DTIME_two_pow_div_sqrt_log_two_subset hTt), fun hsub =>
    DTIME_two_pow_not_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT hTn hTt (hsub.trans h)⟩

end Cslib.Complexity.CountingSimulation
