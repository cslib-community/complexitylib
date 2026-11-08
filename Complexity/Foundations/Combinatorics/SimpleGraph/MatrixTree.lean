/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MatrixTree.lean`)

public import Complexity.Foundations.Combinatorics.SimpleGraph.OrientedIncidence
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexity.Foundations.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.PowersetCard
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Kirchhoff's matrix-tree theorem

For a finite simple graph `G` and a vertex `r`, the determinant of the reduced Laplacian, the
submatrix of `G.lapMatrix ℤ` on the rows and columns of the vertices other than `r`, is the number
of spanning trees of `G` (`SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree`); this is
Kirchhoff's theorem [Kirchhoff1847] in its modern determinant form. A spanning tree is a subgraph
`T ≤ G` on all of `V` with `T.IsTree`. The same holds over any commutative ring
(`SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree'`).

Both are the case of all weights `1` of the **weighted matrix-tree theorem**
(`SimpleGraph.det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree`). For edge weights
`w : Sym2 V → R` in a commutative ring, the reduced Laplacian of the weighted adjacency matrix
`SimpleGraph.weightedAdjMatrix G w` has determinant `∑ T, ∏ e ∈ T.edgeSet, w e`, the sum over the
spanning trees `T ≤ G`.

The proof is the standard one by the Cauchy–Binet formula. Write `N'` for the oriented incidence
matrix `SimpleGraph.orientedIncMatrix G` with the row of `r` deleted. Then the reduced weighted
Laplacian is `N' * diagonal w * N'ᵀ`
(`SimpleGraph.orientedIncMatrix_map_mul_diagonal_mul_transpose`), and its determinant is the sum
over the sets `S` of `|V| - 1` edges of `det (N'_S) ^ 2 * ∏ e ∈ S, w e`, by
`Matrix.det_mul_eq_sum_powersetCard_of_equiv`. For any family `g` of edges indexed by the vertices
other than `r` (an edge `g v` need not be incident to `v`):

* if the edges chosen by `g` do not connect a vertex `w` to `r`, the indicator vector of the
  vertices reachable from `w` is a nonzero left kernel vector of `N'_g`, so `det N'_g = 0`
  (`SimpleGraph.det_orientedIncMatrix_submatrix_eq_zero`);
* if they form a connected spanning subgraph, give each vertex `v ≠ r` the chosen edge joining it
  to a neighbour closer to `r`. This bijection makes `N'_g`, up to a permutation of columns,
  triangular for the distance to `r` with diagonal entries `±1`, so `det N'_g ^ 2 = 1`
  (`SimpleGraph.det_orientedIncMatrix_submatrix_sq_eq_one`).

A connected spanning subgraph with `|V| - 1` edges is a spanning tree, and conversely.

As a corollary, the complete graph on `n ≥ 1` vertices has `n ^ (n - 2)` spanning trees
(**Cayley's formula** [Cayley1889], `SimpleGraph.natCard_isTree_eq_card_pow`): its reduced
Laplacian is `n • 1` minus the all-ones matrix of size `n - 1`, whose determinant is
`n ^ (n - 1) * (1 - (n - 1) / n)` by the matrix determinant lemma.

The directed analogue, Tutte's matrix-tree theorem for arborescences, is in
`Complexity.Foundations.Combinatorics.Digraph.MatrixTree`.

## Main results

* `SimpleGraph.lapMatrix_submatrix_eq_mul_transpose`: the reduced Laplacian is `N' * N'ᵀ`.
* `SimpleGraph.det_orientedIncMatrix_submatrix_eq_zero`,
  `SimpleGraph.det_orientedIncMatrix_submatrix_sq_eq_one`,
  `SimpleGraph.det_orientedIncMatrix_submatrix_sq`: the squared minors of `N'` on `|V| - 1`
  columns are `1` on connected spanning subgraphs and `0` otherwise.
* `SimpleGraph.det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree`: **the weighted
  matrix-tree theorem**.
* `SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree`: **Kirchhoff's matrix-tree theorem**.
* `SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree'`: the same over a commutative ring.
* `SimpleGraph.natCard_isTree_eq_card_pow`: **Cayley's formula**, there are `n ^ (n - 2)` trees
  on a type with `n ≥ 1` elements.

## References

* [G. Kirchhoff, *Ueber die Auflösung der Gleichungen, auf welche man bei der Untersuchung der
  linearen Vertheilung galvanischer Ströme geführt wird*][Kirchhoff1847]
* [A. Cayley, *A theorem on trees*][Cayley1889]
* [C. Godsil, G. Royle, *Algebraic Graph Theory*][GodsilRoyle2001], §13.2, Theorem 13.2.1, proved
  there by deletion and contraction (locator from secondary sources, unverified)
-/

public section

open Matrix Set.powersetCard

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Adjacency in the spanning subgraph whose edges are the values of a family `g` of edges. -/
theorem fromEdgeSet_range_adj {ι : Type*} (g : ι → G.edgeSet) {a b : V} :
    (fromEdgeSet (Set.range fun k => (g k : Sym2 V))).Adj a b ↔
      ∃ k, (g k : Sym2 V) = s(a, b) := by
  rw [fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨k, hk⟩, -⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, hk⟩, fun hab => ?_⟩
    subst hab
    exact G.not_isDiag_of_mem_edgeSet (hk ▸ (g k).2) (Sym2.mk_isDiag_iff.mpr rfl)

/-- In a connected graph, a vertex `v ≠ r` has a neighbour one step closer to `r`. -/
private theorem exists_adj_dist_add_one {H : SimpleGraph V} (hH : H.Connected) {r v : V}
    (hv : v ≠ r) : ∃ u, H.Adj v u ∧ H.dist u r + 1 = H.dist v r := by
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist v r
  cases p with
  | nil => exact absurd rfl hv
  | cons h q =>
    refine ⟨_, h, le_antisymm ?_ ?_⟩
    · rw [← hp, Walk.length_cons]
      exact Nat.succ_le_succ (dist_le q)
    · obtain ⟨q', hq'⟩ := hH.exists_walk_length_eq_dist _ r
      have := dist_le (Walk.cons h q')
      rw [Walk.length_cons, hq'] at this
      exact this

variable [Fintype V] [DecidableEq V]

/-- If the edges of a family `g` indexed by the vertices other than `r` do not connect `w` to `r`,
then the minor of the oriented incidence matrix on the rows `v ≠ r` and the columns `g` vanishes. -/
theorem det_orientedIncMatrix_submatrix_eq_zero {r w : V} (g : {v // v ≠ r} → G.edgeSet)
    (hw : ¬ (fromEdgeSet (Set.range fun k => (g k : Sym2 V))).Reachable r w) :
    (G.orientedIncMatrix.submatrix Subtype.val g).det = 0 := by
  classical
  set H := fromEdgeSet (Set.range fun k => (g k : Sym2 V))
  have hwr : w ≠ r := fun h => hw (h ▸ Reachable.refl _)
  have hw' : ¬ H.Reachable w r := fun h => hw h.symm
  rw [← exists_vecMul_eq_zero_iff]
  refine ⟨fun v => if H.Reachable w v then 1 else 0, fun h => ?_, ?_⟩
  · have := congrFun h ⟨w, hwr⟩
    simp at this
  · ext k
    simp only [vecMul, dotProduct, submatrix_apply, Pi.zero_apply]
    have hs := Fintype.sum_eq_add_sum_subtype_ne
      (fun v => (if H.Reachable w v then (1 : ℤ) else 0) * G.orientedIncMatrix v (g k)) r
    simp only [hw', ite_false, zero_mul, zero_add] at hs
    rw [← hs, sum_mul_orientedIncMatrix]
    have hadj : H.Adj (g k : Sym2 V).out.1 (g k : Sym2 V).out.2 :=
      (fromEdgeSet_range_adj g).2 ⟨k, (Sym2.mk_fst_out_snd_out _).symm⟩
    have : H.Reachable w (g k : Sym2 V).out.1 ↔ H.Reachable w (g k : Sym2 V).out.2 :=
      ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    by_cases h1 : H.Reachable w (g k : Sym2 V).out.1
    · simp [h1, this.1 h1]
    · simp [h1, mt this.2 h1]

/-- If the edges of a family `g` indexed by the vertices other than `r` form a connected spanning
subgraph, then the square of the minor of the oriented incidence matrix on the rows `v ≠ r` and
the columns `g` is `1`. -/
theorem det_orientedIncMatrix_submatrix_sq_eq_one {r : V} (g : {v // v ≠ r} → G.edgeSet)
    (hc : (fromEdgeSet (Set.range fun k => (g k : Sym2 V))).Connected) :
    (G.orientedIncMatrix.submatrix Subtype.val g).det ^ 2 = 1 := by
  classical
  set H := fromEdgeSet (Set.range fun k => (g k : Sym2 V))
  have hpar : ∀ v : {v // v ≠ r}, ∃ u, H.Adj v u ∧ H.dist u r + 1 = H.dist v r :=
    fun v => exists_adj_dist_add_one hc v.2
  choose par hparadj hpardist using hpar
  have hk : ∀ v : {v // v ≠ r}, ∃ k, (g k : Sym2 V) = s((v : V), par v) :=
    fun v => (fromEdgeSet_range_adj g).1 (hparadj v)
  choose p hp using hk
  have hpinj : Function.Injective p := by
    intro v w hvw
    have h := (hp v).symm.trans (hvw ▸ hp w)
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h1
    · have h3 := hpardist v
      have h4 := hpardist w
      rw [h2] at h3
      rw [← h1] at h4
      omega
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm {v // v ≠ r}, ⇑π = p :=
    ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.mp hpinj), rfl⟩
  have hdet := det_permute' π (G.orientedIncMatrix.submatrix Subtype.val g)
  rw [submatrix_submatrix, Function.comp_id, Int.cast_id] at hdet
  have hmem : ∀ v : {v // v ≠ r}, ∀ u : V, u ∈ (g (p v) : Sym2 V) ↔ u = v ∨ u = par v := by
    intro v u
    rw [hp v, Sym2.mem_iff]
  have htri : (G.orientedIncMatrix.submatrix Subtype.val (g ∘ π)).det =
      ∏ v : {v // v ≠ r}, G.orientedIncMatrix v (g (p v)) := by
    refine (det_eq_prod_diag_of_weight (G.orientedIncMatrix.submatrix Subtype.val (g ∘ π))
      (fun u => H.dist (u : V) r) ?_).trans ?_
    · intro u v huv hne
      simp only [submatrix_apply, Function.comp_apply, hπ] at hne
      have : (u : V) ∈ (g (p v) : Sym2 V) := by
        by_contra hu
        exact hne (orientedIncMatrix_eq_zero_of_notMem hu)
      rcases (hmem v u).1 this with h | h
      · exact absurd (Subtype.ext h) huv
      · rw [h]
        have := hpardist v
        omega
    · simp [hπ]
  have hdiag : ∀ v : {v // v ≠ r}, G.orientedIncMatrix v (g (p v)) ^ 2 = 1 := by
    intro v
    rw [sq, orientedIncMatrix_mul_self, ite_eq_left_iff.mpr
      (fun h => absurd ((hmem v v).2 (Or.inl rfl)) h)]
  have hsign : ((Equiv.Perm.sign π : ℤˣ) : ℤ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  calc (G.orientedIncMatrix.submatrix Subtype.val g).det ^ 2
      = (G.orientedIncMatrix.submatrix Subtype.val (g ∘ π)).det ^ 2 := by
        rw [hdet, mul_pow, hsign, one_mul]
    _ = 1 := by
        rw [htri, ← Finset.prod_pow]
        simp [hdiag]

/-- The square of the minor of the oriented incidence matrix on the rows `v ≠ r` and the columns
`g` is `1` if the edges chosen by `g` form a connected spanning subgraph, and `0` otherwise. -/
theorem det_orientedIncMatrix_submatrix_sq {r : V} (g : {v // v ≠ r} → G.edgeSet) :
    (G.orientedIncMatrix.submatrix Subtype.val g).det ^ 2 =
      if (fromEdgeSet (Set.range fun k => (g k : Sym2 V))).Connected then 1 else 0 := by
  split_ifs with hc
  · exact det_orientedIncMatrix_submatrix_sq_eq_one g hc
  · obtain ⟨w, hw⟩ : ∃ w, ¬ (fromEdgeSet (Set.range fun k => (g k : Sym2 V))).Reachable r w := by
      by_contra! h
      exact hc ((connected_iff_exists_forall_reachable _).2 ⟨r, h⟩)
    rw [det_orientedIncMatrix_submatrix_eq_zero g hw]
    simp

variable [DecidableRel G.Adj]

/-- The reduced Laplacian on the vertices other than `r` is `N' * N'ᵀ`, where `N'` is the oriented
incidence matrix with the row of `r` deleted. -/
theorem lapMatrix_submatrix_eq_mul_transpose (r : V) :
    (G.lapMatrix ℤ).submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val =
      G.orientedIncMatrix.submatrix (Subtype.val : {v // v ≠ r} → V) id *
        (G.orientedIncMatrix.submatrix (Subtype.val : {v // v ≠ r} → V) id)ᵀ := by
  rw [← orientedIncMatrix_mul_transpose, submatrix_mul _ _ _ _ _ Function.bijective_id]
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The edge set of the spanning subgraph on a set of edges of `G` is that set. -/
private theorem edgeSet_fromEdgeSet_image (s : Set G.edgeSet) :
    (fromEdgeSet (Subtype.val '' s)).edgeSet = Subtype.val '' s := by
  rw [edgeSet_fromEdgeSet]
  ext x
  simp only [Set.mem_sdiff, Sym2.mem_diagSet, and_iff_left_iff_imp]
  rintro ⟨y, -, rfl⟩
  exact G.not_isDiag_of_mem_edgeSet y.2

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- On a vertex type with `m + 1` elements, the sets of `m` edges of `G` that form a connected
spanning subgraph correspond to the spanning trees of `G`. -/
private theorem bijective_spanningTree {m : ℕ} (hm : Fintype.card V = m + 1) :
    ∃ h : ∀ s : {s : Set.powersetCard G.edgeSet m //
        (fromEdgeSet (Subtype.val '' (s : Set G.edgeSet))).Connected},
        fromEdgeSet (Subtype.val '' (s.1 : Set G.edgeSet)) ≤ G ∧
          (fromEdgeSet (Subtype.val '' (s.1 : Set G.edgeSet))).IsTree,
      Function.Bijective fun s => (⟨_, h s⟩ : {T : SimpleGraph V // T ≤ G ∧ T.IsTree}) := by
  classical
  refine ⟨fun s => ⟨?_, ?_⟩, fun s t hst => ?_, fun T => ?_⟩
  · rw [← edgeSet_subset_edgeSet, edgeSet_fromEdgeSet_image]
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [isTree_iff_connected_and_card, edgeSet_fromEdgeSet_image, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ Subtype.val_injective, ncard_eq, Nat.card_eq_fintype_card, hm]
    exact ⟨s.2, rfl⟩
  · have h2 := congrArg SimpleGraph.edgeSet (congrArg Subtype.val hst)
    simp only [edgeSet_fromEdgeSet_image] at h2
    have h3 := Set.image_injective.mpr Subtype.val_injective h2
    exact Subtype.ext (Subtype.ext (SetLike.coe_injective h3))
  · obtain ⟨T, hle, htree⟩ := T
    let S : Finset G.edgeSet := Finset.univ.filter fun x => (x : Sym2 V) ∈ T.edgeSet
    have himage : Subtype.val '' (S : Set G.edgeSet) = T.edgeSet := by
      ext x
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, edgeSet_subset_edgeSet.2 hle hx⟩, hx, rfl⟩
    have hScard : S.card = m := by
      have := (isTree_iff_connected_and_card.1 htree).2
      rw [Nat.card_coe_set_eq, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective,
        Set.ncard_coe_finset, Nat.card_eq_fintype_card, hm] at this
      omega
    have hT : fromEdgeSet (Subtype.val '' (S : Set G.edgeSet)) = T := by
      rw [← edgeSet_inj, edgeSet_fromEdgeSet_image]
      exact himage
    refine ⟨⟨⟨S, hScard⟩, ?_⟩, ?_⟩
    · change (fromEdgeSet (Subtype.val '' (S : Set G.edgeSet))).Connected
      rw [hT]
      exact htree.connected
    · exact Subtype.ext hT

/-- **The weighted matrix-tree theorem** [Kirchhoff1847]. For edge weights `w : Sym2 V → R` in a
commutative ring and every vertex `r` of a finite simple graph `G`, the determinant of the reduced
weighted Laplacian, the submatrix of `(G.weightedAdjMatrix w).laplacian` on the vertices other
than `r`, is the sum over the spanning trees `T ≤ G` of the product of the weights of the edges
of `T`. -/
theorem det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree {R : Type*} [CommRing R]
    (w : Sym2 V → R) (r : V) :
    ((G.weightedAdjMatrix w).laplacian.submatrix (Subtype.val : {v // v ≠ r} → V)
        Subtype.val).det =
      ∑ᶠ (T : SimpleGraph V) (_ : T ≤ G ∧ T.IsTree), ∏ᶠ e ∈ T.edgeSet, w e := by
  classical
  set m := Fintype.card {v // v ≠ r}
  let e : {v // v ≠ r} ≃ Fin m := Fintype.equivFin _
  let _ : LinearOrder G.edgeSet := LinearOrder.lift' (Fintype.equivFin G.edgeSet)
    (Fintype.equivFin G.edgeSet).injective
  have hcardV : Fintype.card V = m + 1 := by
    rw [← Fintype.card_congr (Equiv.optionSubtypeNe r), Fintype.card_option]
  set N : Matrix {v // v ≠ r} G.edgeSet R :=
    (G.orientedIncMatrix.map (Int.cast : ℤ → R)).submatrix Subtype.val id with hN
  have hfac : (G.weightedAdjMatrix w).laplacian.submatrix (Subtype.val : {v // v ≠ r} → V)
      Subtype.val = (N * diagonal fun x : G.edgeSet => w x) * Nᵀ := by
    rw [← orientedIncMatrix_map_mul_diagonal_mul_transpose,
      submatrix_mul _ _ _ _ _ Function.bijective_id,
      submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  have hterm : ∀ s : Set.powersetCard G.edgeSet m,
      ((N * diagonal fun x : G.edgeSet => w x).submatrix id (ofFinEmbEquiv.symm s ∘ e)).det *
          (Nᵀ.submatrix (ofFinEmbEquiv.symm s ∘ e) id).det =
        if (fromEdgeSet (Subtype.val '' (s : Set G.edgeSet))).Connected then
          ∏ᶠ x ∈ (fromEdgeSet (Subtype.val '' (s : Set G.edgeSet))).edgeSet, w x
        else 0 := by
    intro s
    set g := ofFinEmbEquiv.symm s ∘ e with hg
    have hdiag : (N * diagonal fun x : G.edgeSet => w x).submatrix id g =
        N.submatrix id g * diagonal fun k => w (g k) := by
      ext i k
      simp only [submatrix_apply, mul_diagonal, id]
    have hcast : (N.submatrix id g).det =
        ((G.orientedIncMatrix.submatrix Subtype.val g).det : R) := by
      rw [show N.submatrix id g = (G.orientedIncMatrix.submatrix Subtype.val g).map
          (Int.castRingHom R) from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    have hinj : Function.Injective fun k => ((g k : G.edgeSet) : Sym2 V) :=
      Subtype.val_injective.comp ((ofFinEmbEquiv.symm s).injective.comp e.injective)
    have hr : Set.range (fun k => ((g k : G.edgeSet) : Sym2 V)) =
        Subtype.val '' (s : Set G.edgeSet) := by
      ext x
      simp only [g, Set.mem_range, Function.comp_apply, Set.mem_image]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨_, (mem_range_ofFinEmbEquiv_symm_iff_mem s _).1 ⟨e k, rfl⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s y).2 hy
        exact ⟨e.symm j, by simp [hj]⟩
    rw [← transpose_submatrix, det_transpose, hdiag, det_mul, det_diagonal, hcast,
      mul_right_comm, ← sq, ← Int.cast_pow, det_orientedIncMatrix_submatrix_sq]
    simp only [hr]
    split_ifs with hc
    · rw [Int.cast_one, one_mul, edgeSet_fromEdgeSet_image, ← hr, finprod_mem_range hinj,
        finprod_eq_prod_of_fintype]
    · rw [Int.cast_zero, zero_mul]
  obtain ⟨h, hbij⟩ := bijective_spanningTree (G := G) hcardV
  rw [hfac, det_mul_eq_sum_powersetCard_of_equiv e]
  simp only [hterm]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun s : Set.powersetCard G.edgeSet m =>
      (fromEdgeSet (Subtype.val '' (s : Set G.edgeSet))).Connected) _ (fun s => by simp),
    ← finsum_subtype_eq_finsum_cond,
    ← finsum_comp_equiv (Equiv.ofBijective _ hbij), finsum_eq_sum_of_fintype]
  rfl

/-- **Kirchhoff's matrix-tree theorem over a commutative ring**: the determinant of the reduced
Laplacian `G.lapMatrix R` on the vertices other than `r` is the number of spanning trees of `G`,
cast to `R`. This is the case of all weights `1` of
`SimpleGraph.det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree`. -/
theorem det_lapMatrix_submatrix_eq_natCard_isTree' (R : Type*) [CommRing R] (r : V) :
    ((G.lapMatrix R).submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree} := by
  classical
  rw [lapMatrix_eq_laplacian_weightedAdjMatrix,
    det_laplacian_weightedAdjMatrix_submatrix_eq_finsum_isTree]
  simp only [finprod_one]
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- **Kirchhoff's matrix-tree theorem** [Kirchhoff1847], in its modern determinant form
([GodsilRoyle2001], §13.2, Theorem 13.2.1; locator from secondary sources, unverified). For
every vertex `r` of a finite simple graph `G`, the determinant of the reduced Laplacian, the
submatrix of `G.lapMatrix ℤ` on the vertices other than `r`, is the number of spanning trees
`T ≤ G` of `G`. -/
theorem det_lapMatrix_submatrix_eq_natCard_isTree (r : V) :
    ((G.lapMatrix ℤ).submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree} :=
  det_lapMatrix_submatrix_eq_natCard_isTree' ℤ r

/-- The Laplacian over a commutative ring is the image of the integer Laplacian. -/
theorem lapMatrix_eq_map_intCast (R : Type*) [CommRing R] :
    G.lapMatrix R = (G.lapMatrix ℤ).map (Int.castRingHom R) := by
  ext u w
  by_cases huw : u = w
  · subst huw
    simp [lapMatrix, degMatrix, adjMatrix_apply]
  · by_cases hadj : G.Adj u w <;>
      simp [lapMatrix, degMatrix, adjMatrix_apply, diagonal_apply_ne _ huw, hadj]

omit [DecidableEq V] in
/-- **Cayley's formula**: there are `n ^ (n - 2)` trees on a type with `n ≥ 1` elements, that is,
the complete graph on `n` labelled vertices has `n ^ (n - 2)` spanning trees [Cayley1889]. The
proof applies the matrix-tree theorem `SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree'` to
`⊤` over `ℚ`. -/
theorem natCard_isTree_eq_card_pow [Nonempty V] :
    Nat.card {T : SimpleGraph V // T.IsTree} = Fintype.card V ^ (Fintype.card V - 2) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty V›
  set n := Fintype.card V with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hm : Fintype.card {v // v ≠ r} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hcard : Nat.card {T : SimpleGraph V // T.IsTree} =
      Nat.card {T : SimpleGraph V // T ≤ ⊤ ∧ T.IsTree} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun T => by simp)
  rw [hcard]
  apply Nat.cast_injective (R := ℚ)
  rw [← det_lapMatrix_submatrix_eq_natCard_isTree' (G := (⊤ : SimpleGraph V)) ℚ r]
  set u : {v // v ≠ r} → ℚ := fun _ => 1
  have hsub : (lapMatrix ℚ (⊤ : SimpleGraph V)).submatrix (Subtype.val : {v // v ≠ r} → V)
      Subtype.val = (n : ℚ) • (1 + replicateCol Unit (-(n : ℚ)⁻¹ • u) * replicateRow Unit u) := by
    rw [← vecMulVec_eq]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hn1 : 1 ≤ n := hn0
      simp only [ne_eq, lapMatrix, degMatrix, ← completeGraph_eq_top, complete_graph_degree,
        adjMatrix_top, submatrix_apply, Matrix.sub_apply, diagonal_apply_eq, of_apply,
        ↓reduceIte, sub_zero, neg_smul, neg_vecMulVec, smul_vecMulVec, Matrix.smul_apply,
        Matrix.add_apply, one_apply_eq, Matrix.neg_apply, vecMulVec_apply, mul_one, smul_eq_mul,
        u]
      rw [← hn, Nat.cast_sub hn1]
      field_simp
      ring
    · have hij' : (i : V) ≠ j := fun h => hij (Subtype.ext h)
      simp [lapMatrix, degMatrix, u, vecMulVec_apply, hn', hij, hij']
  rw [hsub, det_smul, det_one_add_replicateCol_mul_replicateRow, hm]
  simp only [u, dotProduct, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, hm, nsmul_eq_mul]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have h1 : n = 1 := by omega
    rw [h1]
    norm_num
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [hk]
    push_cast
    field_simp
    ring

end SimpleGraph
