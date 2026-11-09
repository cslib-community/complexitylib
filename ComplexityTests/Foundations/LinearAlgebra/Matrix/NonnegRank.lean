/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Communication.Nondeterministic.ExtensionComplexity
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for nonnegative rank and the rectangle covering bound

Concrete matrices over `ℚ`. A matrix with a negative entry has no nonnegative factorization, so its
nonnegative rank is `⊤`. The `3 × 3` cyclic permutation matrix has nonnegative rank `3`: the
upper bound is trivial and the lower bound is the fooling set of its three `1`-entries. So the
`1`-cover number of its support is `3`, and its nondeterministic complexity `N¹` is
`⌈log₂ 3⌉ = 2`.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.NonnegRankTests

open Matrix Cslib.Communication Cslib.Communication.Nondeterministic

/-- A matrix with a negative entry has infinite nonnegative rank. -/
example : (!![(-1 : ℚ)]).nonnegRank = ⊤ := by
  by_contra h
  have := (nonnegRank_ne_top_iff.1 h) 0 0
  norm_num at this

/-- Nonvacuity: the identity has a nonnegative factorization through its rows. -/
example : (1 : Matrix (Fin 2) (Fin 2) ℚ).HasNonnegFactorization (Fin 2) :=
  hasNonnegFactorization_height fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> norm_num

/-- The cyclic permutation matrix. -/
abbrev cyc : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- Its three `1`-entries form a fooling set of its support. -/
theorem cyc_isFoolingSet :
    IsFoolingSet (fun i j => decide (cyc i j ≠ 0)) true {(0, 1), (1, 2), (2, 0)} := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The cyclic permutation matrix has nonnegative rank `3`. -/
theorem nonnegRank_cyc : cyc.nonnegRank = 3 := by
  refine le_antisymm ?_ ?_
  · simpa using nonnegRank_le_card_height (M := cyc) fun i j => by
      fin_cases i <;> fin_cases j <;> norm_num
  · simpa using card_le_nonnegRank_of_isFoolingSet cyc_isFoolingSet

/-- `rank ≤ rank₊` gives the upper bound `3` on the rank. -/
example : (cyc.rank : ℕ∞) ≤ 3 := nonnegRank_cyc ▸ rank_le_nonnegRank

/-- The rank is `3` too: `cyc` has determinant `1`. -/
example : cyc.rank = 3 := by
  rw [rank_of_isUnit cyc ((isUnit_iff_isUnit_det cyc).2 (isUnit_iff_ne_zero.2 (by
    norm_num [det_fin_three]))), Fintype.card_fin]

/-- The `1`-cover number of the support of the cyclic permutation matrix is `3`. -/
theorem coverNumberFun_cyc :
    coverNumberFun true (fun i j => decide (cyc i j ≠ 0)) Set.univ Set.univ = 3 := by
  refine le_antisymm (nonnegRank_cyc ▸ coverNumberFun_ne_zero_le_nonnegRank cyc) ?_
  simpa using card_le_coverNumberFun_of_isFoolingSet cyc_isFoolingSet fun _ _ =>
    ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Hence `N¹` of its support is `⌈log₂ 3⌉ = 2`. -/
example : ecomplexityFun true (fun i j => decide (cyc i j ≠ 0)) Set.univ Set.univ = 2 := by
  rw [ecomplexityFun, ecomplexity_eq_clog_coverNumber (r := 3) coverNumberFun_cyc,
    show Nat.clog 2 3 = 2 by decide]
  rfl

end Cslib.LinearAlgebra.NonnegRankTests
