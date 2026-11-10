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
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for extended formulations and Yannakakis's factorization theorem

Concrete polytopes over `ℚ`.

* The triangle `conv {0, e₀, e₁} = {x | -x₀ ≤ 0, -x₁ ≤ 0, x₀ + x₁ ≤ 1}` has a permutation matrix
  as slack matrix, and extension complexity `3`.
* The unit square `conv {0, e₀, e₁, e₀ + e₁} = {x | 0 ≤ x₀ ≤ 1, 0 ≤ x₁ ≤ 1}` has a slack matrix of
  rank `3` (its last row is a signed combination of the others) but of nonnegative rank `4`,
  witnessed by a fooling set of four `1`-entries; so its extension complexity is `4`.
* The hexagon with vertices `(±2, 0)`, `(±1, ±1)`, an affine image of the regular hexagon, has six
  facets, but its slack matrix has an explicit nonnegative factorization of inner dimension `5`,
  and it has an extended formulation with five inequalities and one extra variable. So its
  extension complexity is at most `5`, below the number of facets.
* The point `{0} ⊆ ℚ`, described by `x ≤ 0`, `-x ≤ 0` and the redundant `x ≤ 1`, has extension
  complexity `0` (the extended formulation `x = 0` has no inequalities), while its slack matrix has
  nonnegative rank `1`. This is why Yannakakis's theorem
  (`extensionComplexity_eq_nonnegRank_slackMatrix`) assumes `P.Nontrivial`.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.ExtendedFormulationTests

open Matrix Cslib.Communication Cslib.Communication.Nondeterministic

/-! ### The triangle -/

/-- The inequalities `-x₀ ≤ 0`, `-x₁ ≤ 0`, `x₀ + x₁ ≤ 1` of the triangle. -/
abbrev triA : Matrix (Fin 3) (Fin 2) ℚ := !![-1, 0; 0, -1; 1, 1]

/-- The right-hand side of the triangle's inequalities. -/
abbrev trib : Fin 3 → ℚ := ![0, 0, 1]

/-- The vertices `0`, `e₀`, `e₁` of the triangle. -/
abbrev triV : Fin 3 → Fin 2 → ℚ := ![![0, 0], ![1, 0], ![0, 1]]

/-- The triangle. -/
abbrev triangle : Set (Fin 2 → ℚ) := {x | triA *ᵥ x ≤ trib}

theorem triangle_eq_convexHull : triangle = convexHull ℚ (Set.range triV) := by
  refine subset_antisymm (fun x hx => ?_) (convexHull_range_subset_setOf_mulVec_le fun j i => ?_)
  · have h0 : -x 0 ≤ 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 0
    have h1 : -x 1 ≤ 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 1
    have h2 : x 0 + x 1 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 2
    have hx' : x = ∑ j, ![1 - x 0 - x 1, x 0, x 1] j • triV j := by
      funext i
      fin_cases i <;> simp [Fin.sum_univ_three]
    rw [hx']
    refine Convex.sum_mem (convex_convexHull ℚ _) (fun j _ => ?_) ?_ fun j _ =>
      subset_convexHull ℚ _ ⟨j, rfl⟩
    · fin_cases j
      · change 0 ≤ 1 - x 0 - x 1
        linarith
      · change 0 ≤ x 0
        linarith
      · change 0 ≤ x 1
        linarith
    · simp only [Fin.sum_univ_three, cons_val_zero, cons_val_one, cons_val_two, Nat.succ_eq_add_one,
        Nat.reduceAdd, tail_cons, head_cons]
      ring
  · fin_cases j <;> fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem triangle_nontrivial : triangle.Nontrivial := by
  rw [triangle_eq_convexHull]
  exact ⟨triV 0, subset_convexHull ℚ _ ⟨0, rfl⟩, triV 1, subset_convexHull ℚ _ ⟨1, rfl⟩,
    fun h => by simpa using congrFun h 0⟩

/-- The slack matrix of the triangle is a permutation matrix. -/
theorem slackMatrix_triangle : triA.slackMatrix trib triV = !![0, 1, 0; 0, 0, 1; 1, 0, 0] :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [dotProduct, Fin.sum_univ_two]

/-- **The triangle has extension complexity `3`**: three inequalities suffice, and the three
`1`-entries of its slack matrix form a fooling set. -/
theorem extensionComplexity_triangle : extensionComplexity triangle = 3 := by
  refine le_antisymm (by simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    extensionComplexity_setOf_mulVec_le_le triA trib) ?_
  have hS : IsFoolingSet (fun i j => decide (triA.slackMatrix trib triV i j ≠ 0)) true
      {(0, 1), (1, 2), (2, 0)} := by
    rw [slackMatrix_triangle]
    refine ⟨?_, ?_⟩ <;> decide
  have h := card_le_extensionComplexity_of_isFoolingSet rfl triangle_eq_convexHull
    triangle_nontrivial hS
  rwa [show ({(0, 1), (1, 2), (2, 0)} : Finset (Fin 3 × Fin 3)).card = 3 by decide,
    Nat.cast_ofNat] at h

/-- Yannakakis's theorem for the triangle: the slack matrix has nonnegative rank `3`. -/
example : (triA.slackMatrix trib triV).nonnegRank = 3 := by
  rw [← extensionComplexity_eq_nonnegRank_slackMatrix rfl triangle_eq_convexHull
    triangle_nontrivial, extensionComplexity_triangle]

/-! ### The square -/

/-- The inequalities `-x₀ ≤ 0`, `x₀ ≤ 1`, `-x₁ ≤ 0`, `x₁ ≤ 1` of the unit square. -/
abbrev sqA : Matrix (Fin 4) (Fin 2) ℚ := !![-1, 0; 1, 0; 0, -1; 0, 1]

/-- The right-hand side of the square's inequalities. -/
abbrev sqb : Fin 4 → ℚ := ![0, 1, 0, 1]

/-- The vertices `0`, `e₀`, `e₁`, `e₀ + e₁` of the square. -/
abbrev sqV : Fin 4 → Fin 2 → ℚ := ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]

/-- The unit square. -/
abbrev square : Set (Fin 2 → ℚ) := {x | sqA *ᵥ x ≤ sqb}

theorem square_eq_convexHull : square = convexHull ℚ (Set.range sqV) := by
  refine subset_antisymm (fun x hx => ?_) (convexHull_range_subset_setOf_mulVec_le fun j i => ?_)
  · have h0 : -x 0 ≤ 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 0
    have h1 : x 0 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 1
    have h2 : -x 1 ≤ 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 2
    have h3 : x 1 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 3
    have hx' : x = ∑ j, ![(1 - x 0) * (1 - x 1), x 0 * (1 - x 1), (1 - x 0) * x 1, x 0 * x 1] j •
        sqV j := by
      funext i
      fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
    rw [hx']
    refine Convex.sum_mem (convex_convexHull ℚ _) (fun j _ => ?_) ?_ fun j _ =>
      subset_convexHull ℚ _ ⟨j, rfl⟩
    · fin_cases j
      · exact mul_nonneg (by change 0 ≤ 1 - x 0; linarith) (by change 0 ≤ 1 - x 1; linarith)
      · exact mul_nonneg (by change 0 ≤ x 0; linarith) (by change 0 ≤ 1 - x 1; linarith)
      · exact mul_nonneg (by change 0 ≤ 1 - x 0; linarith) (by change 0 ≤ x 1; linarith)
      · exact mul_nonneg (by change 0 ≤ x 0; linarith) (by change 0 ≤ x 1; linarith)
    · simp only [Fin.sum_univ_four, cons_val_zero, cons_val_one, cons_val_two, cons_val_three,
        Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons]
      ring
  · fin_cases j <;> fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem square_nontrivial : square.Nontrivial := by
  rw [square_eq_convexHull]
  exact ⟨sqV 0, subset_convexHull ℚ _ ⟨0, rfl⟩, sqV 1, subset_convexHull ℚ _ ⟨1, rfl⟩,
    fun h => by simpa using congrFun h 0⟩

/-- The slack matrix of the square. -/
theorem slackMatrix_square :
    sqA.slackMatrix sqb sqV = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 0, 1, 1; 1, 1, 0, 0] :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [dotProduct, Fin.sum_univ_two]

/-- The slack matrix of the square has rank at most `3`: its last row is the sum of the first two
minus the third. -/
theorem rank_slackMatrix_square_le : (sqA.slackMatrix sqb sqV).rank ≤ 3 := by
  have h : sqA.slackMatrix sqb sqV =
      !![(1 : ℚ), 0, 0; 0, 1, 0; 0, 0, 1; 1, 1, -1] *
        !![(0 : ℚ), 1, 0, 1; 1, 0, 1, 0; 0, 0, 1, 1] := by
    rw [slackMatrix_square]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  exact (rank_mul_le_right _ _).trans (rank_le_card_height _ |>.trans_eq (Fintype.card_fin 3))

/-- The slack matrix of the square has rank at least `3`: rows `0, 1, 2` and columns `0, 1, 2` form
an invertible submatrix, so `1 = P * S * C` for suitable `P` and `C`. -/
theorem three_le_rank_slackMatrix_square : 3 ≤ (sqA.slackMatrix sqb sqV).rank := by
  have h : (1 : Matrix (Fin 3) (Fin 3) ℚ) =
      !![(1 : ℚ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] * sqA.slackMatrix sqb sqV *
        !![(0 : ℚ), 1, -1; 1, 0, 0; 0, 0, 1; 0, 0, 0] := by
    rw [slackMatrix_square]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  calc 3 = (1 : Matrix (Fin 3) (Fin 3) ℚ).rank := by rw [rank_one, Fintype.card_fin]
    _ ≤ _ := by rw [h]; exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- The slack matrix of the square has rank exactly `3`. -/
theorem rank_slackMatrix_square : (sqA.slackMatrix sqb sqV).rank = 3 :=
  le_antisymm rank_slackMatrix_square_le three_le_rank_slackMatrix_square

/-- **The square has extension complexity `4`**: four inequalities suffice, and the slack matrix
has a fooling set of four `1`-entries. So the slack matrix has nonnegative rank `4` but rank `3`.
-/
theorem extensionComplexity_square : extensionComplexity square = 4 := by
  refine le_antisymm (by simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    extensionComplexity_setOf_mulVec_le_le sqA sqb) ?_
  have hS : IsFoolingSet (fun i j => decide (sqA.slackMatrix sqb sqV i j ≠ 0)) true
      {(0, 3), (1, 0), (2, 2), (3, 1)} := by
    rw [slackMatrix_square]
    refine ⟨?_, ?_⟩ <;> decide
  have h := card_le_extensionComplexity_of_isFoolingSet rfl square_eq_convexHull square_nontrivial
    hS
  rwa [show ({(0, 3), (1, 0), (2, 2), (3, 1)} : Finset (Fin 4 × Fin 4)).card = 4 by decide,
    Nat.cast_ofNat] at h

/-- Nonnegative rank exceeds rank for the slack matrix of the square. -/
example : ((sqA.slackMatrix sqb sqV).rank : ℕ∞) < (sqA.slackMatrix sqb sqV).nonnegRank := by
  rw [← extensionComplexity_eq_nonnegRank_slackMatrix rfl square_eq_convexHull square_nontrivial,
    extensionComplexity_square]
  rw [rank_slackMatrix_square]
  norm_num

/-! ### The hexagon: fewer inequalities than facets -/

/-- The six facet inequalities `x₀ + x₁ ≤ 2`, `x₁ ≤ 1`, `-x₀ + x₁ ≤ 2`, `-x₀ - x₁ ≤ 2`, `-x₁ ≤ 1`,
`x₀ - x₁ ≤ 2` of the hexagon with vertices `(2, 0)`, `(1, 1)`, `(-1, 1)`, `(-2, 0)`, `(-1, -1)`,
`(1, -1)`, an affine image of the regular hexagon. -/
abbrev hexA : Matrix (Fin 6) (Fin 2) ℚ := !![1, 1; 0, 1; -1, 1; -1, -1; 0, -1; 1, -1]

/-- The right-hand side of the hexagon's inequalities. -/
abbrev hexb : Fin 6 → ℚ := ![2, 1, 2, 2, 1, 2]

/-- The vertices of the hexagon, in cyclic order. -/
abbrev hexV : Fin 6 → Fin 2 → ℚ := ![![2, 0], ![1, 1], ![-1, 1], ![-2, 0], ![-1, -1], ![1, -1]]

/-- The hexagon `|x₁| + max (-x₀ - 1) 0 (x₀ - 1) ≤ 1`. -/
abbrev hexagon : Set (Fin 2 → ℚ) := {x | hexA *ᵥ x ≤ hexb}

/-- The slack matrix of the hexagon. -/
theorem slackMatrix_hexagon :
    hexA.slackMatrix hexb hexV =
      !![0, 0, 2, 4, 4, 2; 1, 0, 0, 1, 2, 2; 4, 2, 0, 0, 2, 4;
        4, 4, 2, 0, 0, 2; 1, 2, 2, 1, 0, 0; 0, 2, 4, 4, 2, 0] :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_two]

/-- **A nonnegative factorization of inner dimension `5`** of the hexagon's slack matrix, which has
six rows: each facet slack is the sum of two of the five slacks of the extended formulation
`hexEF`, evaluated at lifts of the vertices. -/
theorem slackMatrix_hexagon_eq_mul :
    hexA.slackMatrix hexb hexV =
      !![(1 : ℚ), 0, 0, 0, 1; 1, 0, 0, 1, 0; 1, 0, 1, 0, 0;
        0, 1, 1, 0, 0; 0, 1, 0, 1, 0; 0, 1, 0, 0, 1] *
      !![(0 : ℚ), 0, 0, 0, 2, 2; 0, 2, 2, 0, 0, 0; 4, 2, 0, 0, 0, 2;
        1, 0, 0, 1, 0, 0; 0, 0, 2, 4, 2, 0] := by
  rw [slackMatrix_hexagon]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_five]

/-- So the slack matrix of the hexagon has nonnegative rank at most `5`, below its six rows. -/
theorem nonnegRank_slackMatrix_hexagon_le : (hexA.slackMatrix hexb hexV).nonnegRank ≤ 5 := by
  have h := HasNonnegFactorization.nonnegRank_le (M := hexA.slackMatrix hexb hexV)
    ⟨_, _, fun i k => by fin_cases i <;> fin_cases k <;> norm_num,
      fun k j => by fin_cases k <;> fin_cases j <;> norm_num, slackMatrix_hexagon_eq_mul.symm⟩
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

/-- The inequalities `x₁ + z ≤ 1`, `-x₁ + z ≤ 1`, `-x₀ - z ≤ 1`, `-z ≤ 0`, `x₀ - z ≤ 1` in the
variables `x` and one extra variable `z`: the hexagon is `|x₁| + z ≤ 1` with
`z ≥ max (-x₀ - 1) 0 (x₀ - 1)`. -/
abbrev hexE : Matrix (Fin 5) (Fin 2) ℚ := !![0, 1; 0, -1; -1, 0; 0, 0; 1, 0]

/-- The coefficients of the extra variable `z` in `hexE`. -/
abbrev hexF : Matrix (Fin 5) (Fin 1) ℚ := !![1; 1; -1; -1; -1]

/-- The right-hand side of the extended formulation of the hexagon. -/
abbrev hexg : Fin 5 → ℚ := ![1, 1, 1, 0, 1]

/-- **The hexagon has an extended formulation with five inequalities** and one extra variable,
although it has six facets. -/
theorem isExtendedFormulation_hexagon :
    IsExtendedFormulation hexagon hexE hexF hexg (0 : Matrix (Fin 0) (Fin 2) ℚ)
      (0 : Matrix (Fin 0) (Fin 1) ℚ) 0 := by
  intro x
  constructor
  · intro hx
    have h0 : x 0 + x 1 ≤ 2 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 0
    have h1 : x 1 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 1
    have h2 : -x 0 + x 1 ≤ 2 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 2
    have h3 : -x 0 - x 1 ≤ 2 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 3
    have h4 : -x 1 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 4
    have h5 : x 0 - x 1 ≤ 2 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hx 5
    have ha : -x 0 - 1 ≤ max (-x 0 - 1) (max 0 (x 0 - 1)) := le_max_left _ _
    have hb : 0 ≤ max (-x 0 - 1) (max 0 (x 0 - 1)) := le_max_of_le_right (le_max_left _ _)
    have hc : x 0 - 1 ≤ max (-x 0 - 1) (max 0 (x 0 - 1)) :=
      le_max_of_le_right (le_max_right _ _)
    have hd : x 1 + max (-x 0 - 1) (max 0 (x 0 - 1)) ≤ 1 := by
      rcases le_total (-x 0 - 1) (max 0 (x 0 - 1)) with h | h
      · rw [max_eq_right h]
        rcases le_total 0 (x 0 - 1) with h' | h'
        · rw [max_eq_right h']
          linarith
        · rw [max_eq_left h']
          linarith
      · rw [max_eq_left h]
        linarith
    have he : -x 1 + max (-x 0 - 1) (max 0 (x 0 - 1)) ≤ 1 := by
      rcases le_total (-x 0 - 1) (max 0 (x 0 - 1)) with h | h
      · rw [max_eq_right h]
        rcases le_total 0 (x 0 - 1) with h' | h'
        · rw [max_eq_right h']
          linarith
        · rw [max_eq_left h']
          linarith
      · rw [max_eq_left h]
        linarith
    generalize max (-x 0 - 1) (max 0 (x 0 - 1)) = z at ha hb hc hd he
    refine ⟨fun _ => z, fun i => ?_, Subsingleton.elim _ _⟩
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> linarith
  · rintro ⟨y, hy, -⟩
    have r0 : x 1 + y 0 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hy 0
    have r1 : -x 1 + y 0 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hy 1
    have r2 : -x 0 - y 0 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hy 2
    have r3 : -y 0 ≤ 0 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hy 3
    have r4 : x 0 - y 0 ≤ 1 := by simpa [mulVec, dotProduct, Fin.sum_univ_two] using hy 4
    intro i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> linarith

/-- So the hexagon has extension complexity at most `5`, one less than its number of facets. -/
theorem extensionComplexity_hexagon_le : extensionComplexity hexagon ≤ 5 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    isExtendedFormulation_hexagon.extensionComplexity_le

/-! ### The point: why `P.Nontrivial` is needed -/

/-- The inequalities `x ≤ 0`, `-x ≤ 0` and the redundant `x ≤ 1`. -/
abbrev ptA : Matrix (Fin 3) (Fin 1) ℚ := !![1; -1; 1]

/-- The right-hand side of the point's inequalities. -/
abbrev ptb : Fin 3 → ℚ := ![0, 0, 1]

/-- The single point `0`. -/
abbrev ptV : Fin 1 → Fin 1 → ℚ := ![0]

theorem setOf_ptA_eq_convexHull : {x | ptA *ᵥ x ≤ ptb} = convexHull ℚ (Set.range ptV) := by
  rw [show Set.range ptV = {0} from Set.range_unique.trans (by rfl), convexHull_singleton]
  refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have h0 : x 0 ≤ 0 := by simpa [mulVec, dotProduct] using hx 0
    have h1 : -x 0 ≤ 0 := by simpa [mulVec, dotProduct] using hx 1
    exact funext fun i => by rw [Subsingleton.elim i 0]; exact le_antisymm h0 (neg_nonpos.1 h1)
  · rw [Set.mem_singleton_iff.1 hx]
    intro i
    fin_cases i <;> simp

/-- The point has extension complexity `0`: the equation `x = 0` is an extended formulation with no
inequalities. -/
theorem extensionComplexity_pt : extensionComplexity {x | ptA *ᵥ x ≤ ptb} = 0 := by
  refine nonpos_iff_eq_zero.1 ?_
  have h : IsExtendedFormulation {x | ptA *ᵥ x ≤ ptb} (0 : Matrix (Fin 0) (Fin 1) ℚ)
      (0 : Matrix (Fin 0) (Fin 0) ℚ) 0 (1 : Matrix (Fin 1) (Fin 1) ℚ)
      (0 : Matrix (Fin 1) (Fin 0) ℚ) 0 := by
    intro x
    rw [setOf_ptA_eq_convexHull, show Set.range ptV = {0} from Set.range_unique.trans (by rfl),
      convexHull_singleton, Set.mem_singleton_iff]
    exact ⟨fun hx => ⟨0, fun i => i.elim0, by simp [hx]⟩, fun ⟨_, _, hy⟩ => by simpa using hy⟩
  simpa using h.extensionComplexity_le

/-- But its slack matrix `(0, 0, 1)ᵀ` has nonnegative rank `1`, so Yannakakis's theorem fails
without `P.Nontrivial`. -/
theorem nonnegRank_slackMatrix_pt : (ptA.slackMatrix ptb ptV).nonnegRank = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using nonnegRank_le_card_width (M := ptA.slackMatrix ptb ptV)
      (slackMatrix_nonneg fun j => (setOf_ptA_eq_convexHull ▸ subset_convexHull ℚ _ ⟨j, rfl⟩ :
        ptV j ∈ {x | ptA *ᵥ x ≤ ptb}))
  · refine Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 fun h => ?_)
    have := congrFun (congrFun (nonnegRank_eq_zero_iff.1 h) 2) 0
    norm_num [dotProduct] at this

/-- The extension complexity of the point is strictly below the nonnegative rank of this slack
matrix. -/
example : extensionComplexity {x | ptA *ᵥ x ≤ ptb} < (ptA.slackMatrix ptb ptV).nonnegRank := by
  rw [extensionComplexity_pt, nonnegRank_slackMatrix_pt]
  exact zero_lt_one

end Cslib.LinearAlgebra.ExtendedFormulationTests
