/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Complexity.Classes.Constructible.TwoPow
import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Classes.Space.Closure
import Complexity.Computability.Complexity.Problems.BoundedHalting
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Separations of linear exponential time

For problems on bit words, `P ⊊ E ⊊ EXP`. The first inclusion is strict because the diagonal
problem `Cslib.Complexity.diagonal`, which is not in `P`, is decided within time `O(2 ^ (4 * n))`.
The second is strict by the time hierarchy theorem. The clocked diagonal with the
time-constructible clock `2 ^ (n + 1) ^ 2` (`Cslib.Complexity.timeDiagonal`) is decided within time
`O((n + 1) ^ 5 * (2 ^ (n + 1) ^ 2 + 1) ^ 3)`, which is within `2 ^ n ^ 3` for `n ≥ 5`. The clock
eventually exceeds every `c * 2 ^ (k * n) + c`, so this problem is in no class
`DTIME (2 ^ (k * n))`.

**Book's theorem** [Book][Book1974]: `E` is not closed under polynomial-time many-one reductions.
Bounded halting with a binary time bound is in `E` and hard for `EXP`
(`Cslib.Complexity.BoundedHalting.polyTimeComplete_E`,
`Cslib.Complexity.BoundedHalting.polyTimeHard_EXP`). Closure would therefore put all of `EXP` in
`E`. Consequently `E` differs from every class closed under these reductions
(`Cslib.Complexity.E_ne_of_polyTimeReducible_mem`), in particular `NP`, `PSPACE` and `P`; for `P`
this also follows from `Cslib.Complexity.P_ssubset_E`. These separations say nothing about the
inclusions between `E` and `NP` or `PSPACE`, which are open.

## Main results

* `Cslib.Complexity.P_ssubset_E`: polynomial time is strictly within linear exponential time.
* `Cslib.Complexity.E_ssubset_EXP`: linear exponential time is strictly within exponential time.
* `Cslib.Complexity.exists_polyTimeReducible_mem_E_notMem_E`: `E` is not closed under
  polynomial-time many-one reductions.
* `Cslib.Complexity.E_ne_of_polyTimeReducible_mem`: `E` differs from every class closed under
  these reductions.
* `Cslib.Complexity.E_ne_NP`, `Cslib.Complexity.E_ne_PSPACE`: `E` is neither `NP` nor `PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 3.1][AroraBarak09]
* [R. V. Book, *Comparing complexity classes*][Book1974]
-/

open Turing Turing.MultiTapeTM Filter

public section

namespace Cslib.Complexity

/-- `2 ^ (n + 1) ^ 2` is time-constructible. -/
private theorem timeConstructible_two_pow_succ_sq :
    TimeConstructible fun n => 2 ^ (n + 1) ^ 2 := by
  simpa only [Nat.div_one] using timeConstructible_succ_sq.two_pow_div one_pos

/-- **Polynomial time is strictly within linear exponential time**, for problems on bit words: the
diagonal problem is decided within time `O(2 ^ (4 * n))` and is not in `P`. -/
theorem P_ssubset_E : P encBits ⊂ E encBits :=
  (Set.ssubset_iff_of_subset P_subset_E).mpr ⟨_, mem_E_iff.mpr ⟨4,
    setOf_mem_DTIME_of_computableInO computableInO_diagonal fun _ => le_rfl⟩, diagonal_notMem_P⟩

/-- **Linear exponential time is strictly within exponential time**, for problems on bit words:
the clocked diagonal with clock `2 ^ (n + 1) ^ 2` is in `DTIME (2 ^ n ^ 3)` and in no class
`DTIME (2 ^ (k * n))` [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem E_ssubset_EXP : E encBits ⊂ EXP encBits := by
  have hJ := timeConstructible_two_pow_succ_sq
  refine (Set.ssubset_iff_of_subset E_subset_EXP).mpr ⟨_, mem_EXP_iff.mpr ⟨3,
    DTIME_mono_of_eventually_le ?_ (setOf_timeDiagonal_mem_DTIME hJ)⟩, fun h => ?_⟩
  · -- the running time of the clocked diagonal is within `2 ^ n ^ 3` from `n = 5` on
    filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := fun n => (n + 1) ^ 5)
      (by fun_prop), eventually_ge_atTop 5] with n hn h5
    have h₁ : 2 ^ (n + 1) ^ 2 + 1 ≤ 2 ^ ((n + 1) ^ 2 + 1) := by
      rw [pow_succ 2 ((n + 1) ^ 2)]
      have := Nat.one_le_two_pow (n := (n + 1) ^ 2)
      omega
    have hexp : n + 3 * ((n + 1) ^ 2 + 1) ≤ n ^ 3 := by nlinarith
    calc (n + 1) ^ 5 * (2 ^ (n + 1) ^ 2 + 1) ^ 3
        ≤ 2 ^ n * (2 ^ ((n + 1) ^ 2 + 1)) ^ 3 :=
          Nat.mul_le_mul hn.le (Nat.pow_le_pow_left h₁ 3)
      _ = 2 ^ (n + 3 * ((n + 1) ^ 2 + 1)) := by rw [← pow_mul, ← pow_add, mul_comm]
      _ ≤ 2 ^ n ^ 3 := Nat.pow_le_pow_right (by norm_num) hexp
  · -- the clock eventually exceeds every `c * 2 ^ (k * n) + c`
    obtain ⟨k, hk⟩ := mem_E_iff.mp h
    refine setOf_timeDiagonal_notMem_DTIME (fun c => ?_) hk
    filter_upwards [eventually_ge_atTop (k + c + 1)] with n hn
    have hc : c + c ≤ 2 ^ (c + 1) := by
      rw [pow_succ 2 c]
      have := Nat.lt_two_pow_self (n := c)
      omega
    have hexp : c + 1 + k * n ≤ (n + 1) ^ 2 := by nlinarith
    calc c * 2 ^ (k * n) + c ≤ (c + c) * 2 ^ (k * n) := by
          have := Nat.one_le_two_pow (n := k * n)
          nlinarith
      _ ≤ 2 ^ (c + 1) * 2 ^ (k * n) := Nat.mul_le_mul_right _ hc
      _ = 2 ^ (c + 1 + k * n) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (n + 1) ^ 2 := Nat.pow_le_pow_right (by norm_num) hexp

/-- **`E` is not closed under polynomial-time many-one reductions** [Book][Book1974]: a problem in
`EXP` but not in `E` reduces to bounded halting, which is in `E`. -/
theorem exists_polyTimeReducible_mem_E_notMem_E :
    ∃ A B : Set (List Bool), PolyTimeReducible encBits encBits A B ∧ B ∈ E encBits ∧
      A ∉ E encBits :=
  let ⟨A, hA, hAE⟩ := Set.exists_of_ssubset E_ssubset_EXP
  ⟨A, _, BoundedHalting.polyTimeHard_EXP encBits A hA, BoundedHalting.mem_E, hAE⟩

/-- **`E` differs from every class closed under polynomial-time many-one reductions**
[Book][Book1974]. -/
theorem E_ne_of_polyTimeReducible_mem {C : Set (Set (List Bool))}
    (hC : ∀ ⦃A B : Set (List Bool)⦄, PolyTimeReducible encBits encBits A B → B ∈ C → A ∈ C) :
    E encBits ≠ C := by
  rintro rfl
  obtain ⟨A, B, hAB, hB, hA⟩ := exists_polyTimeReducible_mem_E_notMem_E
  exact hA (hC hAB hB)

/-- **Linear exponential time is not `NP`** [Book][Book1974]. Whether either class contains the
other is open. -/
theorem E_ne_NP : E encBits ≠ NP encBits :=
  E_ne_of_polyTimeReducible_mem fun _ _ h hB => h.mem_NP hB

/-- **Linear exponential time is not `PSPACE`** [Book][Book1974]. Whether either class contains
the other is open. -/
theorem E_ne_PSPACE : E encBits ≠ PSPACE encBits :=
  E_ne_of_polyTimeReducible_mem fun _ _ h hB => h.mem_PSPACE hB

end Cslib.Complexity
