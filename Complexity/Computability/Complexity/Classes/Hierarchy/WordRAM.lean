/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time.WordRAM
import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Complexity.Classes.Hierarchy.TimePolylog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A time hierarchy for the word RAM

For a time-constructible, polynomially bounded `T` with `n ≤ T n`, some problem is decided by one
fixed word-RAM program over `Basis.additive` within `O(T(n) ^ 5)` instructions, at logarithmic
word sizes, and by no such program within `O(T n)` instructions
(`Cslib.WordRAM.exists_mem_RAMTIME_pow_five_notMem_RAMTIME`). Equivalently,
`RAMTIME .additive encBits T ⊂ RAMTIME .additive encBits (T ^ 5)`
(`Cslib.WordRAM.RAMTIME_ssubset_RAMTIME_pow_five`).

The proof composes the two simulations of
`Complexity.Computability.Complexity.Classes.Time.WordRAM` with the time hierarchy for multi-tape
Turing machines. A program in time `O(T)` is simulated in
`DTIME ((n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3)`, that is `O(T⁴ log³ T)`. The
polylogarithmic-gap hierarchy (`Cslib.Complexity.exists_DTIME_not_subset_DTIME_of_clock_polylog`),
with the clock `(T n * (Nat.size (T n) + 1)) ^ 4`, gives a problem in `DTIME (T ^ 5)` outside that
class. It is in `RAMTIME (T ^ 5)` by the linear simulation of machines, since `T ^ 5` is
polynomially bounded.

The exponent `5` is an artifact of the composition. The exponent `4` of the Turing-machine
simulation of the word RAM comes from the simulator's association-list memory, and the fifth
factor absorbs the logarithms and the polylogarithmic gap of the universal machine. A direct
diagonalization over word-RAM programs would give a smaller gap; this file does not attempt it.
The lower class is over `Basis.additive`, the basis for which an explicit simulation overhead is
proved.

## Main results

* `Cslib.WordRAM.exists_mem_RAMTIME_pow_five_notMem_RAMTIME`: a problem in word-RAM time
  `O(T ^ 5)` and not in word-RAM time `O(T)`.
* `Cslib.WordRAM.RAMTIME_ssubset_RAMTIME_pow_five`: the hierarchy as a strict inclusion.
-/

public section

namespace Cslib.WordRAM

open Cslib.Complexity Filter Turing.MultiTapeTM

/-- The clock `(m * (Nat.size m + 1)) ^ 4` beats `c * (n + m + 1) ^ 4 * (Nat.size n + 1) ^ 3 + c`
for `n ≤ m` once `Nat.size m` exceeds `82 * c`. -/
private theorem mul_overhead_add_le_clock (c : ℕ) {n m : ℕ} (hnm : n ≤ m)
    (hm : max 1 (2 ^ (82 * c)) ≤ m) :
    c * ((n + m + 1) ^ 4 * (Nat.size n + 1) ^ 3) + c ≤ (m * (Nat.size m + 1)) ^ 4 := by
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hsize : 82 * c < Nat.size m := Nat.lt_size.mpr ((le_max_right _ _).trans hm)
  have hsn : Nat.size n ≤ Nat.size m := Nat.size_le_size hnm
  have hX : 1 ≤ m ^ 4 * (Nat.size m + 1) ^ 3 :=
    Nat.mul_pos (Nat.pow_pos hm1) (Nat.pow_pos (Nat.succ_pos _))
  have hf : (n + m + 1) ^ 4 * (Nat.size n + 1) ^ 3 ≤ 81 * (m ^ 4 * (Nat.size m + 1) ^ 3) := by
    calc _ ≤ (3 * m) ^ 4 * (Nat.size m + 1) ^ 3 := by gcongr; omega
      _ = _ := by ring
  calc c * ((n + m + 1) ^ 4 * (Nat.size n + 1) ^ 3) + c
      ≤ c * (81 * (m ^ 4 * (Nat.size m + 1) ^ 3)) + c * (m ^ 4 * (Nat.size m + 1) ^ 3) :=
        Nat.add_le_add (Nat.mul_le_mul_left c hf) (Nat.le_mul_of_pos_right c hX)
    _ = 82 * c * (m ^ 4 * (Nat.size m + 1) ^ 3) := by ring
    _ ≤ (Nat.size m + 1) * (m ^ 4 * (Nat.size m + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
    _ = (m * (Nat.size m + 1)) ^ 4 := by ring

/-- For every `k`, the bound of the polylogarithmic-gap hierarchy for the clock
`J = (m * (Nat.size m + 1)) ^ 4`, `n + (log (n + 1) + 1) ^ k * (J + 1) * (log (J + 1) + 1)`, is
at most `m ^ 5` for `n ≤ m` and large `m`. -/
private theorem exists_polylogBound_clock_le_pow_five (k : ℕ) : ∃ M, ∀ {n m : ℕ}, n ≤ m → M ≤ m →
    n + (Nat.log 2 (n + 1) + 1) ^ k *
      (((m * (Nat.size m + 1)) ^ 4 + 1) * (Nat.log 2 ((m * (Nat.size m + 1)) ^ 4 + 1) + 1)) ≤
      m ^ 5 := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    (PolynomiallyBounded.eventually_lt_two_pow (f := fun L => 34 * (L + 1) ^ (k + 5))
      (by fun_prop))
  refine ⟨max 1 (2 ^ L₀), fun {n m} hnm hm => ?_⟩
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hL : L₀ < Nat.size m := Nat.lt_size.mpr ((le_max_right _ _).trans hm)
  -- `2 ^ size m ≤ 2 m`, so `34 (size m + 1) ^ (k + 5) < 2 m`.
  have hpow : 2 ^ Nat.size m ≤ 2 * m := by
    have : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.mp (by omega)
    calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * m := by omega
  have hY := hL₀ (Nat.size m) hL.le
  have hlt : m < 2 ^ Nat.size m := Nat.lt_size_self m
  have hℓ : Nat.size m + 1 ≤ 2 ^ Nat.size m := Nat.lt_two_pow_self
  have hlogn : Nat.log 2 (n + 1) ≤ Nat.size m := by
    calc Nat.log 2 (n + 1) ≤ Nat.log 2 (2 ^ Nat.size m) := Nat.log_mono_right (by omega)
      _ = Nat.size m := Nat.log_pow (by norm_num) _
  have hJ : (m * (Nat.size m + 1)) ^ 4 + 1 ≤ 2 ^ (8 * Nat.size m) := by
    have h₁ : m * (Nat.size m + 1) < 2 ^ Nat.size m * 2 ^ Nat.size m :=
      Nat.mul_lt_mul_of_lt_of_le hlt hℓ (Nat.pow_pos (by norm_num))
    have h₂ : (m * (Nat.size m + 1)) ^ 4 < (2 ^ Nat.size m * 2 ^ Nat.size m) ^ 4 :=
      Nat.pow_lt_pow_left h₁ (by norm_num)
    calc _ ≤ (2 ^ Nat.size m * 2 ^ Nat.size m) ^ 4 := h₂
      _ = 2 ^ (8 * Nat.size m) := by rw [← pow_add, ← pow_mul]; ring_nf
  have hlogJ : Nat.log 2 ((m * (Nat.size m + 1)) ^ 4 + 1) ≤ 8 * Nat.size m := by
    calc _ ≤ Nat.log 2 (2 ^ (8 * Nat.size m)) := Nat.log_mono_right hJ
      _ = 8 * Nat.size m := Nat.log_pow (by norm_num) _
  have hJ2 : (m * (Nat.size m + 1)) ^ 4 + 1 ≤ 2 * (m ^ 4 * (Nat.size m + 1) ^ 4) := by
    have : 1 ≤ m ^ 4 * (Nat.size m + 1) ^ 4 :=
      Nat.mul_pos (Nat.pow_pos hm1) (Nat.pow_pos (Nat.succ_pos _))
    rw [mul_pow]
    omega
  have hm4 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) _
  have hY1 : 1 ≤ (Nat.size m + 1) ^ (k + 5) := Nat.pow_pos (Nat.succ_pos _)
  calc n + (Nat.log 2 (n + 1) + 1) ^ k *
        (((m * (Nat.size m + 1)) ^ 4 + 1) * (Nat.log 2 ((m * (Nat.size m + 1)) ^ 4 + 1) + 1))
      ≤ m + (Nat.size m + 1) ^ k *
          ((2 * (m ^ 4 * (Nat.size m + 1) ^ 4)) * (8 * (Nat.size m + 1))) := by
        gcongr
        omega
    _ = m + 16 * (Nat.size m + 1) ^ (k + 5) * m ^ 4 := by ring
    _ ≤ m ^ 4 + 16 * (Nat.size m + 1) ^ (k + 5) * m ^ 4 := Nat.add_le_add_right hm4 _
    _ = (1 + 16 * (Nat.size m + 1) ^ (k + 5)) * m ^ 4 := by ring
    _ ≤ m * m ^ 4 := Nat.mul_le_mul_right _ (by omega)
    _ = m ^ 5 := by ring

/-- **A time hierarchy for the word RAM.** For a time-constructible, polynomially bounded `T` with
`n ≤ T n`, some problem is decided by one fixed program over `Basis.additive` within `O(T(n) ^ 5)`
instructions at logarithmic word sizes, and by no fixed program over `Basis.additive` within
`O(T n)` instructions at logarithmic word sizes. -/
theorem exists_mem_RAMTIME_pow_five_notMem_RAMTIME {T : ℕ → ℕ} (hT : TimeConstructible T)
    (hn : ∀ n, n ≤ T n) (hpoly : PolynomiallyBounded T) :
    ∃ A : Set (List Bool), A ∈ RAMTIME .additive encBits (fun n => T n ^ 5) ∧
      A ∉ RAMTIME .additive encBits T := by
  obtain ⟨k, hk⟩ := exists_DTIME_not_subset_DTIME_of_clock_polylog
  obtain ⟨M, hM⟩ := exists_polylogBound_clock_le_pow_five k
  have hpow : Turing.MultiTapeTM.ComputableInPolyTime (fun m : ℕ => m ^ 4) encNat encNat :=
    ComputableInPolyTime.binary_pow' ComputableInPolyTime.id' (ComputableInPolyTime.const 4)
  have hJ : TimeConstructible fun n => (T n * (Nat.size (T n) + 1)) ^ 4 :=
    hT.mul_size_succ.comp_of_computableInPolyTime hpow fun n => Nat.le_self_pow (by norm_num) _
  have hsep := hk (f := fun n => (n + T n + 1) ^ 4 * (Nat.size n + 1) ^ 3)
    (g := fun n => T n ^ 5) hJ
    (fun c => Eventually.frequently <| by
      filter_upwards [eventually_ge_atTop (max 1 (2 ^ (82 * c)))] with n hc
      exact mul_overhead_add_le_clock c (hn n) (hc.trans (hn n)))
    (by
      filter_upwards [eventually_ge_atTop M] with n hM'
      exact hM (hn n) (hM'.trans (hn n)))
  obtain ⟨A, hAg, hAf⟩ := Set.not_subset.mp hsep
  exact ⟨A, DTIME_subset_RAMTIME_additive (by fun_prop) hAg,
    fun h => hAf (RAMTIME_additive_subset_DTIME hT h)⟩

/-- **The word-RAM time hierarchy as a strict inclusion.** For a time-constructible, polynomially
bounded `T` with `n ≤ T n`, `RAMTIME .additive encBits T ⊂ RAMTIME .additive encBits (T ^ 5)`. -/
theorem RAMTIME_ssubset_RAMTIME_pow_five {T : ℕ → ℕ} (hT : TimeConstructible T)
    (hn : ∀ n, n ≤ T n) (hpoly : PolynomiallyBounded T) :
    RAMTIME .additive encBits T ⊂ RAMTIME .additive encBits fun n => T n ^ 5 := by
  obtain ⟨A, hA, hA'⟩ := exists_mem_RAMTIME_pow_five_notMem_RAMTIME hT hn hpoly
  exact (Set.ssubset_iff_of_subset
    (RAMTIME_mono fun n => Nat.le_self_pow (by norm_num) _)).mpr ⟨A, hA, hA'⟩

end Cslib.WordRAM
