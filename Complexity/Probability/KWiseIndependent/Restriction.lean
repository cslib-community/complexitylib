/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent

/-!
# Restriction-Fiber Cardinalities for `k`-Wise Independent Hash Families

This module provides exact natural-number fiber-cardinality identities for restrictions
`T.restrict (h i) = y` (`#T ≤ k`) and full evaluations `h i = y` (`Fintype.card X ≤ k`) of a
`k`-wise independent hash family `h : ι → X → Y`.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.card_filter_restrict_eq`: for `#T ≤ k` and `y : T → Y`
  with `[Nonempty Y]`,
  `Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} = Fintype.card ι`.
* `Cslib.Probability.IsKWiseIndependentHash.card_filter_eq_of_card_le`: for `Fintype.card X ≤ k` and
  `y : X → Y` with `[Nonempty Y]`,
  `#{i : ι | h i = y} * Fintype.card Y ^ Fintype.card X = Fintype.card ι`.
-/

public section

namespace Cslib.Probability.IsKWiseIndependentHash

open Finset Fintype

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Exact natural-number fiber cardinality of `T.restrict (h i) = y` under a `k`-wise independent
hash family `h : ι → X → Y` over a nonempty codomain `Y`. -/
theorem card_filter_restrict_eq {k : ℕ} {h : ι → X → Y}
    (hh : IsKWiseIndependentHash k h) {T : Finset X} (hT : #T ≤ k) (y : T → Y) :
    Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} = Fintype.card ι := by
  have : Nonempty ι := hh.nonempty
  have hdens := hh.dens_filter_restrict_eq hT y
  rw [Finset.dens_eq_card_div_card] at hdens
  have hι_ne : (Fintype.card ι : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY_ne : ((Fintype.card Y : ℚ≥0) ^ #T) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hq :
      ((Fintype.card Y ^ #T * #{i : ι | T.restrict (h i) = y} : ℕ) : ℚ≥0) =
        (Fintype.card ι : ℚ≥0) := by
    push_cast
    rw [div_eq_iff hι_ne] at hdens
    rw [hdens, ← mul_assoc, mul_inv_cancel₀ hY_ne, one_mul]
  exact Nat.cast_inj.mp hq

/-- Exact natural-number fiber cardinality of `h i = y` on a finite domain `X` with
`Fintype.card X ≤ k` under a `k`-wise independent hash family `h : ι → X → Y`. -/
theorem card_filter_eq_of_card_le [Fintype X] {k : ℕ} {h : ι → X → Y}
    (hh : IsKWiseIndependentHash k h) (hX : Fintype.card X ≤ k) (y : X → Y) :
    #{i : ι | h i = y} * Fintype.card Y ^ Fintype.card X = Fintype.card ι := by
  let T : Finset X := Finset.univ
  have hT : #T ≤ k := by simpa [T] using hX
  have h1 := hh.card_filter_restrict_eq hT (fun a => y a.1)
  have hset :
      #{i : ι | T.restrict (h i) = fun a => y a.1} = #{i : ι | h i = y} := by
    congr 1
    ext i
    simp [T, funext_iff, Finset.restrict]
  have hT_card : #T = Fintype.card X := by simp [T]
  rw [hset, hT_card, Nat.mul_comm] at h1
  exact h1

end Cslib.Probability.IsKWiseIndependentHash
