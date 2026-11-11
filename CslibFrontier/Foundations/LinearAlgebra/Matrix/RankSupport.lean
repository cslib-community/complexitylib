/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, rank lower bounds from sparse rows and columns)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Rank lower bounds from matrix support

If every row of a matrix has at most `d` nonzero entries, then its nonzero columns are covered
by the supports of a row basis. Consequently, the number of nonzero columns is at most
`rank * d` (`Matrix.card_nonzero_columns_le_rank_mul`). If every column also has at most `e`
nonzero entries, the total number of nonzero entries is at most `rank * d * e`
(`Matrix.card_nonzero_entries_le_rank_mul_mul`). These inequalities are valid over every field;
the division-free formulation also covers empty matrices and zero support bounds.

The second statement generalizes the sparse-matrix rank estimate in
[C. Lee, J. Lee, and S. Oum, *Rank-width of random graphs*][LeeLeeOum2012], Lemma 4.3 of
arXiv:1001.0461v1, from `𝔽₂` and one common support bound to every field and separate row and
column bounds. The proof here retains the intermediate nonzero-column bound, which also
applies to neighborhood expansion and cut ranks.

## Main results

* `Matrix.card_nonzero_columns_le_rank_mul`: a row basis covers every nonzero column.
* `Matrix.card_nonzero_entries_le_rank_mul_mul`: bounded row and column supports give a rank
  lower bound from the number of nonzero entries.

## References

* [C. Lee, J. Lee, and S. Oum, *Rank-width of random graphs*][LeeLeeOum2012]
-/

public section

namespace Matrix

open Finset Submodule
open scoped BigOperators

variable {m n K : Type*} [Fintype m] [Fintype n] [Field K] [DecidableEq K]

/-- If every row has at most `d` nonzero entries, then the number of nonzero columns is at most
`rank * d`. The supports of a row basis cover all the nonzero columns. -/
theorem card_nonzero_columns_le_rank_mul (M : Matrix m n K) (d : ℕ)
    (hrow : ∀ i, #{j | M i j ≠ 0} ≤ d) :
    #{j | ∃ i, M i j ≠ 0} ≤ M.rank * d := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K M.row
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hrank : M.rank = Fintype.card κ := by
    rw [rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  have hcover : ({j | ∃ i, M i j ≠ 0} : Finset n) ⊆
      univ.biUnion (fun k : κ ↦ {j | M (a k) j ≠ 0}) := by
    intro j hj
    by_contra hj'
    have hzero (k : κ) : M (a k) j = 0 := by
      by_contra hk
      exact hj' (mem_biUnion.mpr ⟨k, mem_univ k, mem_filter.mpr ⟨mem_univ j, hk⟩⟩)
    have heval (v : n → K) (hv : v ∈ span K (Set.range (M.row ∘ a))) : v j = 0 := by
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨k, rfl⟩ := hv
        exact hzero k
      | zero => rfl
      | add v w _ _ hv hw => simp [hv, hw]
      | smul c v _ hv => simp [hv]
    obtain ⟨i, hi⟩ := (mem_filter.mp hj).2
    apply hi
    apply heval
    rw [hspan]
    exact subset_span ⟨i, rfl⟩
  calc
    #{j | ∃ i, M i j ≠ 0} ≤ #(univ.biUnion (fun k : κ ↦ {j | M (a k) j ≠ 0})) :=
      card_le_card hcover
    _ ≤ #(@univ κ _) * d :=
      card_biUnion_le_card_mul _ _ _ fun k _ ↦ hrow (a k)
    _ = M.rank * d := by rw [card_univ, hrank]

/-- If rows have at most `d` and columns at most `e` nonzero entries, the matrix has at most
`rank * d * e` nonzero entries. This generalizes
[Lee, Lee, and Oum, arXiv:1001.0461v1, Lemma 4.3][LeeLeeOum2012]. -/
theorem card_nonzero_entries_le_rank_mul_mul (M : Matrix m n K) (d e : ℕ)
    (hrow : ∀ i, #{j | M i j ≠ 0} ≤ d)
    (hcol : ∀ j, #{i | M i j ≠ 0} ≤ e) :
    #{p : m × n | M p.1 p.2 ≠ 0} ≤ M.rank * d * e := by
  classical
  have hcount : #{p : m × n | M p.1 p.2 ≠ 0} = ∑ j, #{i | M i j ≠ 0} := by
    simp only [card_filter, ← univ_product_univ, sum_product]
    exact sum_comm
  calc
    #{p : m × n | M p.1 p.2 ≠ 0} = ∑ j, #{i | M i j ≠ 0} := hcount
    _ ≤ ∑ j : n, if ∃ i, M i j ≠ 0 then e else 0 := by
      refine sum_le_sum fun j _ ↦ ?_
      by_cases hj : ∃ i, M i j ≠ 0
      · simpa only [ite_eq_left hj] using hcol j
      · have hz : ∀ i, M i j = 0 := by simpa only [not_exists, not_not] using hj
        simp [hz]
    _ = #{j | ∃ i, M i j ≠ 0} * e := by
      rw [← sum_filter]
      simp only [sum_const, smul_eq_mul]
    _ ≤ M.rank * d * e := Nat.mul_le_mul_right e (M.card_nonzero_columns_le_rank_mul d hrow)

end Matrix
