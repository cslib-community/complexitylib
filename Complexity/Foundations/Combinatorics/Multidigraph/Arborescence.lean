/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Digraph.MatrixTree
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

/-!
# Spanning in-arborescences of finite multidigraphs

A multidigraph on the vertices `V` with arcs `E`, parallel arcs and loops allowed, is given here by
the maps `src tgt : E → V` sending each arc to its source and its target. A *spanning
in-arborescence rooted at `r`* chooses, for every vertex `v ≠ r`, an arc `f v` out of `v`, such
that following the chosen arcs leads from every vertex to `r`
(`Cslib.Multidigraph.IsInArborescence`). The chosen arcs form an oriented spanning tree with every
arc directed towards `r`, and conversely, so arborescences that differ only in a parallel arc are
counted separately.

Their number is the determinant of the reduced Laplacian of the *arc-count matrix*, whose entry
`(u, w)` is the number of arcs from `u` to `w` (`Cslib.Multidigraph.arcMatrix`). This is the
directed matrix-tree theorem [Tutte1948] for multidigraphs
(`Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence`), derived from
the parent-function form `Digraph.det_laplacian_submatrix_eq_finsum_reachable` by sorting the
arborescences by the vertices `tgt (f v)` that their arcs reach.

## Main definitions

* `Cslib.Multidigraph.IsInArborescence`: spanning in-arborescences of a multidigraph.
* `Cslib.Multidigraph.arcMatrix`: the arc-count matrix of a multidigraph.

## Main results

* `Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence`: the
  directed matrix-tree theorem for multidigraphs.

## References

* [W. T. Tutte, *The dissection of equilateral triangles into equilateral triangles*][Tutte1948]
  (Theorem 3.6, according to [Stanley2013], Chapter 10 notes; the primary source was not
  inspected)
* [R. P. Stanley, *Topics in Algebraic Combinatorics*][Stanley2013], Theorem 10.4 (the directed
  matrix-tree theorem for digraphs with parallel arcs and loops)
-/

public section

open Matrix

namespace Cslib.Multidigraph

variable {V E : Type*} (src tgt : E → V)

/-- `f` is a **spanning in-arborescence rooted at `r`** of the multidigraph `src tgt : E → V`: it
chooses an arc `f v` out of every vertex `v ≠ r`, and following the chosen arcs leads from every
vertex to `r`. -/
structure IsInArborescence (r : V) (f : {v // v ≠ r} → E) : Prop where
  /-- The arc chosen at `v` leaves `v`. -/
  src_eq : ∀ v, src (f v) = v
  /-- Following the chosen arcs leads from every vertex to the root. -/
  reachable : ∀ v, Relation.ReflTransGen (fun v w => ∃ h : v ≠ r, tgt (f ⟨v, h⟩) = w) v r

variable (R : Type*) [NatCast R] [Fintype E] [DecidableEq V] in
/-- The **arc-count matrix** of a multidigraph: the entry `(u, w)` is the number of arcs from `u`
to `w`. -/
def arcMatrix : Matrix V V R :=
  Matrix.of fun u w => ((Finset.univ.filter fun e => src e = u ∧ tgt e = w).card : R)

/-- The entries of the arc-count matrix. -/
@[simp]
theorem arcMatrix_apply {R : Type*} [NatCast R] [Fintype E] [DecidableEq V] (u w : V) :
    arcMatrix src tgt R u w = ((Finset.univ.filter fun e => src e = u ∧ tgt e = w).card : R) := by
  rw [arcMatrix, Matrix.of_apply]

/-- **The directed matrix-tree theorem** for multidigraphs [Tutte1948] ([Stanley2013],
Theorem 10.4). The determinant of the reduced Laplacian of the arc-count matrix, the out-degree
matrix minus the arc-count matrix with the row and column of `r` deleted, is the number of spanning
in-arborescences rooted at `r` (arcs directed towards `r`). Loops do not contribute. The source
assumes a connected digraph; connectivity is not needed. -/
theorem det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence (R : Type*) [CommRing R]
    [Fintype V] [DecidableEq V] [Fintype E] (r : V) :
    ((arcMatrix src tgt R).laplacian.submatrix (Subtype.val : {v // v ≠ r} → V)
        Subtype.val).det =
      Nat.card {f : {v // v ≠ r} → E // IsInArborescence src tgt r f} := by
  classical
  rw [Digraph.det_laplacian_submatrix_eq_finsum_reachable]
  let P : ({v // v ≠ r} → V) → Prop := fun g =>
    ∀ v, Relation.ReflTransGen (fun v w => ∃ h : v ≠ r, g ⟨v, h⟩ = w) v r
  let Arb := {f : {v // v ≠ r} → E // IsInArborescence src tgt r f}
  let φ : Arb → {g // P g} := fun f => ⟨fun v => tgt (f.1 v), f.2.reachable⟩
  have hfib : ∀ g : {g // P g}, Nat.card {f // φ f = g} =
      ∏ i : {v // v ≠ r}, (Finset.univ.filter fun e => src e = i ∧ tgt e = g.1 i).card := by
    intro g
    let ψ : {f // φ f = g} ≃ ((i : {v // v ≠ r}) → {e // src e = i ∧ tgt e = g.1 i}) :=
      { toFun := fun f i => ⟨f.1.1 i, f.1.2.src_eq i, congrFun (congrArg Subtype.val f.2) i⟩
        invFun := fun h => ⟨⟨fun i => (h i).1, fun i => (h i).2.1, by
            have hg : (fun v => tgt (h v).1) = g.1 := funext fun i => (h i).2.2
            have := g.2
            simp only [P, ← hg] at this
            exact this⟩,
          Subtype.ext (funext fun i => (h i).2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr ψ, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : Nat.card Arb = ∑ g : {g // P g},
      ∏ i : {v // v ≠ r}, (Finset.univ.filter fun e => src e = i ∧ tgt e = g.1 i).card := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv φ), Nat.card_sigma]
    exact Finset.sum_congr rfl fun g _ => hfib g
  change _ = ((Nat.card Arb : ℕ) : R)
  rw [hcard, Nat.cast_sum, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl fun i _ => arcMatrix_apply src tgt _ _

end Cslib.Multidigraph
