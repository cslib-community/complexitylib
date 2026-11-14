/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Classes.Padding.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Polynomial space classes are not closed under polynomial-time reductions

For `k ≥ 1`, the class `DSPACE (n ^ k)` of problems on bit words is not closed under
polynomial-time many-one reductions. By the space hierarchy theorem
(`Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ`), some problem `A` is in
`DSPACE (n ^ (k + 1))` but not in `DSPACE (n ^ k)`. Padding instances of `A` of length `m` to
length `(m + 1) ^ 2` gives a problem in `DSPACE (n ^ k)`
(`Cslib.Complexity.polynomialPadded_mem_DSPACE`), and `A` reduces to it in polynomial time
(`Cslib.Complexity.polyTimeReducible_polynomialPadded`).

So `DSPACE (n ^ k)` differs from every class closed under these reductions
(`Cslib.Complexity.DSPACE_pow_ne_of_polyTimeReducible_mem`). For linear space this is **Book's
theorem** `SPACE(n) ≠ NP` [Book][Book1974], [Arora and Barak, Exercise 3.2][AroraBarak07]
(`Cslib.Complexity.DSPACE_ne_NP`), and also `SPACE(n) ≠ P` and `SPACE(n) ≠ PSPACE`. Whether either
of `SPACE(n)` and `NP` contains the other is open. The argument is the space analogue of
`Cslib.Complexity.E_ne_NP`.

Space counts visited work cells, as in `Cslib.Complexity.DSPACE`. The draft's Definition 4.1 counts
ever-non-blank cells instead. The separation `≠` concerns the library's class.

## Main results

* `Cslib.Complexity.exists_polyTimeReducible_mem_DSPACE_pow_notMem`: `DSPACE (n ^ k)` is not closed
  under polynomial-time many-one reductions, for `k ≥ 1`.
* `Cslib.Complexity.DSPACE_pow_ne_of_polyTimeReducible_mem`,
  `Cslib.Complexity.DSPACE_ne_of_polyTimeReducible_mem`: these classes differ from every class
  closed under such reductions.
* `Cslib.Complexity.DSPACE_ne_NP`, `Cslib.Complexity.DSPACE_ne_P`,
  `Cslib.Complexity.DSPACE_ne_PSPACE`: linear space is neither `NP`, `P` nor `PSPACE`.

## References

* [R. V. Book, *Comparing complexity classes*][Book1974]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **`DSPACE (n ^ k)` is not closed under polynomial-time many-one reductions**, for `k ≥ 1`: a
problem in `DSPACE (n ^ (k + 1))` but not in `DSPACE (n ^ k)` reduces to its padded language, which
is in `DSPACE (n ^ k)`. -/
theorem exists_polyTimeReducible_mem_DSPACE_pow_notMem {k : ℕ} (hk : 1 ≤ k) :
    ∃ A B : Set (List Bool), PolyTimeReducible encBits encBits A B ∧
      B ∈ DSPACE encBits (· ^ k) ∧ A ∉ DSPACE encBits (· ^ k) := by
  obtain ⟨A, hA, hAk⟩ := Set.exists_of_ssubset (DSPACE_pow_ssubset_DSPACE_pow_succ k)
  refine ⟨A, polynomialPadded A 2, polyTimeReducible_polynomialPadded A (by norm_num),
    DSPACE_mono_of_le_mul_add (Nat.add_one_pow_le_two_pow_mul_add k)
      (polynomialPadded_mem_DSPACE hk (DSPACE_mono (fun n => ?_) hA)), hAk⟩
  calc n ^ (k + 1) ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_succ n) _
    _ ≤ (n + 1) ^ (k * 2) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)

/-- **`DSPACE (n ^ k)` differs from every class closed under polynomial-time many-one
reductions**, for `k ≥ 1`. -/
theorem DSPACE_pow_ne_of_polyTimeReducible_mem {k : ℕ} (hk : 1 ≤ k) {C : Set (Set (List Bool))}
    (hC : ∀ ⦃A B : Set (List Bool)⦄, PolyTimeReducible encBits encBits A B → B ∈ C → A ∈ C) :
    DSPACE encBits (· ^ k) ≠ C := by
  rintro rfl
  obtain ⟨A, B, hAB, hB, hA⟩ := exists_polyTimeReducible_mem_DSPACE_pow_notMem hk
  exact hA (hC hAB hB)

/-- **Linear space differs from every class closed under polynomial-time many-one reductions**
[Book][Book1974]. -/
theorem DSPACE_ne_of_polyTimeReducible_mem {C : Set (Set (List Bool))}
    (hC : ∀ ⦃A B : Set (List Bool)⦄, PolyTimeReducible encBits encBits A B → B ∈ C → A ∈ C) :
    DSPACE encBits (fun n => n) ≠ C := by
  simpa only [pow_one] using DSPACE_pow_ne_of_polyTimeReducible_mem le_rfl hC

/-- **Book's theorem: linear space is not `NP`** [Book][Book1974],
[Arora and Barak, Exercise 3.2][AroraBarak07]. Whether either class contains the other is open. -/
theorem DSPACE_ne_NP : DSPACE encBits (fun n => n) ≠ NP encBits :=
  DSPACE_ne_of_polyTimeReducible_mem fun _ _ h hB => h.mem_NP hB

/-- **Linear space is not `P`** [Book][Book1974]. Whether either class contains the other is open.
-/
theorem DSPACE_ne_P : DSPACE encBits (fun n => n) ≠ P encBits :=
  DSPACE_ne_of_polyTimeReducible_mem fun _ _ h hB => h.mem_P hB

/-- **Linear space is not `PSPACE`**. This also follows from the space hierarchy theorem. -/
theorem DSPACE_ne_PSPACE : DSPACE encBits (fun n => n) ≠ PSPACE encBits :=
  DSPACE_ne_of_polyTimeReducible_mem fun _ _ h hB => h.mem_PSPACE hB

end Cslib.Complexity
