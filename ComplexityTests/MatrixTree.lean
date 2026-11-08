/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Digraph.MatrixTree
import Complexity.Foundations.Combinatorics.SimpleGraph.MatrixTree

/-!
# Regression tests for the weighted and directed matrix-tree theorems

The reduced Laplacian at the root `0` of an arbitrary weight matrix on `Fin 3` is computed by
hand. Through the matrix-tree theorems this gives:

* the weighted spanning-tree polynomial of the triangle `K₃`, whose spanning trees are its three
  pairs of edges, and its all-ones specialization, which agrees with Cayley's formula;
* the weighted arborescence polynomial on `Fin 3` at root `0`, with its three in-arborescences
  `{1 → 0, 2 → 0}`, `{1 → 0, 2 → 1}` and `{1 → 2, 2 → 0}`;
* arborescence counts: `3` in the complete digraph (loops included), `1` in the directed
  `3`-cycle, `0` for the out-star at `0`, and `1` for the transposed out-star, which counts the
  out-arborescences of the out-star.

`Digraph.IsInArborescence` holds for the path `2 → 1 → 0` and fails for the `3`-cycle (the root
has an outgoing arc) and for the `2`-cycle `1 ⇄ 2`. The `2`-cycle satisfies the first two fields,
and the counting theorem shows that reachability of the root is needed.
-/

namespace ComplexityTests.MatrixTree

open Matrix

/-- The reduced Laplacian at root `0` of any matrix on `Fin 3`. -/
theorem det_laplacian_submatrix_zero {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    (A.laplacian.submatrix (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).det =
      (A 1 0 + A 1 2) * (A 2 0 + A 2 1) - A 1 2 * A 2 1 := by
  refine (det_submatrix_equiv_self (finSuccAboveEquiv (0 : Fin 3))
    (A.laplacian.submatrix (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val)).symm.trans ?_
  rw [submatrix_submatrix, det_fin_two]
  simp [laplacian_apply, Fin.sum_univ_three, finSuccAboveEquiv]
  ring

/-! ### The weighted matrix-tree theorem -/

section Weighted

open SimpleGraph

/-- The weighted spanning-tree polynomial of the triangle: its spanning trees are its three pairs
of edges. -/
theorem finsum_isTree_top_fin_three {R : Type*} [CommRing R] (w : Sym2 (Fin 3) → R) :
    ∑ᶠ (T : SimpleGraph (Fin 3)) (_ : T ≤ ⊤ ∧ T.IsTree), ∏ᶠ e ∈ T.edgeSet, w e =
      w s(0, 1) * w s(0, 2) + w s(0, 1) * w s(1, 2) + w s(0, 2) * w s(1, 2) := by
  rw [← det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree w 0,
    det_laplacian_submatrix_zero]
  have h10 : s((1 : Fin 3), 0) = s(0, 1) := Sym2.eq_swap
  have h20 : s((2 : Fin 3), 0) = s(0, 2) := Sym2.eq_swap
  have h21 : s((2 : Fin 3), 1) = s(1, 2) := Sym2.eq_swap
  simp [h10, h20, h21]
  ring

-- All weights `1`: the triangle has `3` spanning trees, as Cayley's formula `3 ^ (3 - 2)` says.
example : ∑ᶠ (T : SimpleGraph (Fin 3)) (_ : T ≤ ⊤ ∧ T.IsTree), ∏ᶠ e ∈ T.edgeSet, (1 : ℤ) = 3 := by
  rw [finsum_isTree_top_fin_three]
  norm_num

example : Nat.card {T : SimpleGraph (Fin 3) // T ≤ ⊤ ∧ T.IsTree} = 3 := by
  have h := det_lapMatrix_submatrix_eq_natCard_isTree' (G := (⊤ : SimpleGraph (Fin 3))) ℤ 0
  rw [lapMatrix_eq_laplacian_weightedAdjMatrix,
    det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree, finsum_isTree_top_fin_three] at h
  norm_num at h ⊢
  exact_mod_cast h.symm

example : Nat.card {T : SimpleGraph (Fin 3) // T.IsTree} = 3 ^ (3 - 2) :=
  natCard_isTree_eq_card_pow

end Weighted

/-! ### The directed matrix-tree theorem -/

section Directed

open Digraph

/-- The weighted arborescence polynomial on `Fin 3` at root `0`: the in-arborescences are
`{1 → 0, 2 → 0}`, `{1 → 0, 2 → 1}` and `{1 → 2, 2 → 0}`. -/
example {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    ∑ᶠ (T : Digraph (Fin 3)) (_ : T.IsInArborescence 0),
        ∏ᶠ (p : Fin 3 × Fin 3) (_ : T.Adj p.1 p.2), A p.1 p.2 =
      A 1 0 * A 2 0 + A 1 0 * A 2 1 + A 1 2 * A 2 0 := by
  rw [← det_laplacian_submatrix_eq_finsum_isInArborescence, det_laplacian_submatrix_zero]
  ring

-- The complete digraph on `Fin 3`, loops included, has `3` arborescences rooted at `0`.
example : Nat.card {T : Digraph (Fin 3) // T ≤ ⊤ ∧ T.IsInArborescence 0} = 3 := by
  have h := det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence ℤ
    (⊤ : Digraph (Fin 3)) 0
  rw [det_laplacian_submatrix_zero] at h
  simp only [adjMatrix_apply, top_adj, ite_true] at h
  norm_num at h ⊢
  exact_mod_cast h.symm

/-- The directed `3`-cycle `0 → 1 → 2 → 0`. -/
def cycle3 : Digraph (Fin 3) where
  Adj v w := w = v + 1

instance : DecidableRel cycle3.Adj := fun v w => inferInstanceAs (Decidable (w = v + 1))

-- The `3`-cycle has exactly one arborescence rooted at `0`: `1 → 2`, `2 → 0`.
example : Nat.card {T : Digraph (Fin 3) // T ≤ cycle3 ∧ T.IsInArborescence 0} = 1 := by
  have h := det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence ℤ cycle3 0
  rw [det_laplacian_submatrix_zero] at h
  have h10 : ¬ cycle3.Adj 1 0 := by decide
  have h12 : cycle3.Adj 1 2 := by decide
  have h20 : cycle3.Adj 2 0 := by decide
  have h21 : ¬ cycle3.Adj 2 1 := by decide
  simp only [adjMatrix_apply, h10, h12, h20, h21, ite_true, ite_false] at h
  norm_num at h
  exact_mod_cast h.symm

-- The `3`-cycle is not an in-arborescence rooted at `0`: the root has the outgoing arc `0 → 1`.
example : ¬ cycle3.IsInArborescence 0 := fun h => h.not_adj_root 1 (by decide)

/-- The out-star at `0`: the arcs `0 → 1` and `0 → 2`. -/
def outStar : Digraph (Fin 3) where
  Adj v w := v = 0 ∧ w ≠ 0

instance : DecidableRel outStar.Adj := fun v w => inferInstanceAs (Decidable (v = 0 ∧ w ≠ 0))

-- The out-star has no in-arborescence rooted at `0`.
example : Nat.card {T : Digraph (Fin 3) // T ≤ outStar ∧ T.IsInArborescence 0} = 0 := by
  have h := det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence ℤ outStar 0
  rw [det_laplacian_submatrix_zero] at h
  have h10 : ¬ outStar.Adj 1 0 := by decide
  have h12 : ¬ outStar.Adj 1 2 := by decide
  have h20 : ¬ outStar.Adj 2 0 := by decide
  have h21 : ¬ outStar.Adj 2 1 := by decide
  simp only [adjMatrix_apply, h10, h12, h20, h21, ite_false] at h
  norm_num at h
  exact_mod_cast h.symm

-- Transposing the weights reverses the arcs: the transposed out-star has one in-arborescence
-- rooted at `0`, the out-star itself read backwards, so the out-star has one out-arborescence.
example : (((outStar.adjMatrix ℤ)ᵀ).laplacian.submatrix
    (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).det = 1 := by
  rw [det_laplacian_submatrix_zero]
  have h01 : outStar.Adj 0 1 := by decide
  have h21 : ¬ outStar.Adj 2 1 := by decide
  have h02 : outStar.Adj 0 2 := by decide
  have h12 : ¬ outStar.Adj 1 2 := by decide
  simp only [transpose_apply, adjMatrix_apply, h01, h21, h02, h12, ite_true, ite_false]
  norm_num

/-- The path `2 → 1 → 0`. -/
def path3 : Digraph (Fin 3) where
  Adj v w := (v = 2 ∧ w = 1) ∨ (v = 1 ∧ w = 0)

instance : DecidableRel path3.Adj := fun v w =>
  inferInstanceAs (Decidable ((v = 2 ∧ w = 1) ∨ (v = 1 ∧ w = 0)))

-- The path `2 → 1 → 0` is an in-arborescence rooted at `0`.
example : path3.IsInArborescence 0 where
  not_adj_root := by decide
  existsUnique_adj v hv := by
    fin_cases v
    · exact absurd rfl hv
    · exact ⟨0, by decide, fun y hy => by revert y; decide⟩
    · exact ⟨1, by decide, fun y hy => by revert y; decide⟩
  reachable v := by
    have h10 : path3.Adj 1 0 := by decide
    have h21 : path3.Adj 2 1 := by decide
    fin_cases v
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h10
    · exact Relation.ReflTransGen.head h21 (Relation.ReflTransGen.single h10)

/-- The `2`-cycle `1 ⇄ 2`. -/
def twoCycle : Digraph (Fin 3) where
  Adj v w := (v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 1)

instance : DecidableRel twoCycle.Adj := fun v w =>
  inferInstanceAs (Decidable ((v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 1)))

-- The `2`-cycle has the first two properties of an in-arborescence rooted at `0` ...
example : (∀ w, ¬ twoCycle.Adj 0 w) ∧ ∀ v, v ≠ 0 → ∃! w, twoCycle.Adj v w := by
  refine ⟨by decide, fun v hv => ?_⟩
  fin_cases v
  · exact absurd rfl hv
  · exact ⟨2, by decide, fun y hy => by revert y; decide⟩
  · exact ⟨1, by decide, fun y hy => by revert y; decide⟩

-- ... but it is not one, since no in-arborescence rooted at `0` lies below it.
example : ¬ twoCycle.IsInArborescence 0 := by
  intro hT
  have h := det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence ℤ twoCycle 0
  rw [det_laplacian_submatrix_zero] at h
  have h10 : ¬ twoCycle.Adj 1 0 := by decide
  have h12 : twoCycle.Adj 1 2 := by decide
  have h20 : ¬ twoCycle.Adj 2 0 := by decide
  have h21 : twoCycle.Adj 2 1 := by decide
  simp only [adjMatrix_apply, h10, h12, h20, h21, ite_true, ite_false] at h
  norm_num at h
  have : Nonempty {T : Digraph (Fin 3) // T ≤ twoCycle ∧ T.IsInArborescence 0} :=
    ⟨⟨twoCycle, le_rfl, hT⟩⟩
  have hpos := Nat.card_pos (α := {T : Digraph (Fin 3) // T ≤ twoCycle ∧ T.IsInArborescence 0})
  omega

end Directed

end ComplexityTests.MatrixTree
