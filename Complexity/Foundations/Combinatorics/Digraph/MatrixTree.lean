/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/MatrixTree.lean`)

public import Complexity.Foundations.LinearAlgebra.Matrix.Laplacian
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# The directed matrix-tree theorem

Let `A : Matrix V V R` be a matrix over a commutative ring, read as the arc weights of a complete
weighted digraph on a finite vertex type `V`, and let `r : V`. The *reduced Laplacian* is the
submatrix of the out-degree Laplacian `Matrix.laplacian A = diagonal (fun u => ∑ v, A u v) - A` on
the rows and columns of the vertices other than `r`. Its determinant is the sum, over the spanning
in-arborescences `T` rooted at `r`, of the product of the weights `A v w` of the arcs `v → w` of
`T` (`Digraph.det_laplacian_submatrix_eq_finsum_isInArborescence`). This is Tutte's directed
matrix-tree theorem [Tutte1948]. A spanning in-arborescence rooted at `r` is a digraph on all of
`V` in which `r` has no outgoing arc, every other vertex has exactly one outgoing arc, and every
vertex reaches `r` along arcs (`Digraph.IsInArborescence`). Its arcs point towards the root.

For a digraph `G` with adjacency matrix `Digraph.adjMatrix R G`, the reduced Laplacian is the
out-degree matrix minus the adjacency matrix with the row and column of `r` deleted, and its
determinant is the number of spanning in-arborescences `T ≤ G` rooted at `r`
(`Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence`). Out-arborescences,
whose arcs point away from the root, are counted by applying these results to the transposed
weight matrix `Aᵀ`, which reverses every arc. The diagonal of `A` (loops) never contributes.

The proof expands the determinant multilinearly along its rows. Row `v` of the reduced Laplacian
is `∑ u, A v u • (e_v - e_u)`, where `e_r` is read as `0`. The determinant is therefore the sum,
over the *parent functions* `f` assigning to each vertex `v ≠ r` a vertex `f v`, of
`∏ v, A v (f v)` times the determinant of the matrix with rows `e_v - e_{f v}`. That determinant
is `1` when iterating `f` from every vertex reaches `r`: ordered by the number of steps to `r`, the
matrix is triangular with unit diagonal. Otherwise `f` has a cycle avoiding `r`, and the
indicator vector of the vertices that never reach `r` lies in its kernel, so it is `0`. The parent
functions that reach `r` correspond to the in-arborescences rooted at `r`, by `T.Adj v w ↔ w = f v`.

## Main definitions

* `Digraph.IsInArborescence`: spanning in-arborescences rooted at a vertex.
* `Digraph.adjMatrix`: the adjacency matrix of a digraph.

## Main results

* `Digraph.det_laplacian_submatrix_eq_finsum_isInArborescence`: **the directed matrix-tree
  theorem**, weighted form.
* `Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence`: the directed
  matrix-tree theorem, counting form.

## References

* [W. T. Tutte, *The dissection of equilateral triangles into equilateral triangles*][Tutte1948]
  (the directed matrix-tree theorem is attributed to this paper by secondary sources; theorem
  locator unverified)
-/

public section

open Matrix

namespace Digraph

variable {V : Type*}

/-- `T` is a **spanning in-arborescence rooted at `r`**, an oriented spanning tree with every arc
directed towards `r`: the root has no outgoing arc, every other vertex has exactly one outgoing
arc, and every vertex reaches `r` along arcs. -/
structure IsInArborescence (T : Digraph V) (r : V) : Prop where
  /-- The root has no outgoing arc. -/
  not_adj_root : ∀ w, ¬ T.Adj r w
  /-- Every vertex other than the root has exactly one outgoing arc. -/
  existsUnique_adj : ∀ v, v ≠ r → ∃! w, T.Adj v w
  /-- Every vertex reaches the root along arcs. -/
  reachable : ∀ v, Relation.ReflTransGen T.Adj v r

variable (R : Type*) [Zero R] [One R] in
/-- The **adjacency matrix** of a digraph: the entry `(v, w)` is `1` if `v → w` is an arc and `0`
otherwise. -/
def adjMatrix (G : Digraph V) [DecidableRel G.Adj] : Matrix V V R :=
  Matrix.of fun v w => if G.Adj v w then 1 else 0

/-- The entries of the adjacency matrix. -/
@[simp]
theorem adjMatrix_apply {R : Type*} [Zero R] [One R] (G : Digraph V) [DecidableRel G.Adj]
    (v w : V) : G.adjMatrix R v w = if G.Adj v w then 1 else 0 := by
  rw [adjMatrix, Matrix.of_apply]

/-! ### Parent functions -/

section Parent

variable {r : V}

/-- A parent function, extended by `r ↦ r`. -/
private def withRoot [DecidableEq V] (f : {v // v ≠ r} → V) (v : V) : V :=
  if h : v = r then r else f ⟨v, h⟩

private theorem withRoot_of_ne [DecidableEq V] (f : {v // v ≠ r} → V) {v : V} (h : v ≠ r) :
    withRoot f v = f ⟨v, h⟩ := by
  simp [withRoot, h]

/-- Iterating the parent function reaches `r` from every vertex. -/
private def Acyclic [DecidableEq V] (f : {v // v ≠ r} → V) : Prop :=
  ∀ v, ∃ n, (withRoot f)^[n] v = r

/-- The digraph of a parent function: the arcs `v → f v` for `v ≠ r`. -/
private def toDigraph (f : {v // v ≠ r} → V) : Digraph V where
  Adj v w := ∃ h : v ≠ r, f ⟨v, h⟩ = w

private theorem toDigraph_injective : Function.Injective (toDigraph (r := r)) := by
  intro f g hfg
  funext ⟨v, hv⟩
  have : (toDigraph g).Adj v (f ⟨v, hv⟩) := hfg ▸ ⟨hv, rfl⟩
  obtain ⟨_, h⟩ := this
  exact h.symm

/-- The arcs of the digraph of a parent function are the pairs `(v, f v)`. -/
private theorem setOf_adj_toDigraph (f : {v // v ≠ r} → V) :
    {p : V × V | (toDigraph f).Adj p.1 p.2} =
      Set.range fun v : {v // v ≠ r} => ((v : V), f v) := by
  ext ⟨v, w⟩
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, Prod.ext rfl h⟩
  · rintro ⟨⟨u, hu⟩, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hu, rfl⟩

variable [DecidableEq V]

private theorem reflTransGen_of_iterate (f : {v // v ≠ r} → V) :
    ∀ (n : ℕ) (v : V), (withRoot f)^[n] v = r → Relation.ReflTransGen (toDigraph f).Adj v r := by
  intro n
  induction n with
  | zero =>
    intro v hv
    rw [Function.iterate_zero_apply] at hv
    rw [hv]
  | succ n ih =>
    intro v hv
    by_cases hvr : v = r
    · rw [hvr]
    · rw [Function.iterate_succ_apply] at hv
      exact Relation.ReflTransGen.head ⟨hvr, (withRoot_of_ne f hvr).symm⟩ (ih _ hv)

private theorem exists_iterate_of_reflTransGen (f : {v // v ≠ r} → V) {v : V}
    (h : Relation.ReflTransGen (toDigraph f).Adj v r) : ∃ n, (withRoot f)^[n] v = r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨ha, rfl⟩ := hab
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, withRoot_of_ne f ha, hn]⟩

private theorem isInArborescence_toDigraph {f : {v // v ≠ r} → V} (hf : Acyclic f) :
    (toDigraph f).IsInArborescence r where
  not_adj_root _ := fun ⟨h, _⟩ => h rfl
  existsUnique_adj v hv := ⟨f ⟨v, hv⟩, ⟨hv, rfl⟩, fun _ ⟨_, hw⟩ => hw.symm⟩
  reachable v := by
    obtain ⟨n, hn⟩ := hf v
    exact reflTransGen_of_iterate f n v hn

private theorem exists_toDigraph_eq {T : Digraph V} (hT : T.IsInArborescence r) :
    ∃ f : {v // v ≠ r} → V, Acyclic f ∧ toDigraph f = T := by
  choose f hf using fun v : {v // v ≠ r} => (hT.existsUnique_adj v v.2).exists
  have hTf : toDigraph f = T := by
    ext v w
    constructor
    · rintro ⟨hv, rfl⟩
      exact hf ⟨v, hv⟩
    · intro hvw
      have hv : v ≠ r := fun h => hT.not_adj_root w (h ▸ hvw)
      exact ⟨hv, (hT.existsUnique_adj v hv).unique (hf ⟨v, hv⟩) hvw⟩
  refine ⟨f, fun v => ?_, hTf⟩
  apply exists_iterate_of_reflTransGen
  rw [hTf]
  exact hT.reachable v

/-- Parent functions that reach `r` are equivalent to in-arborescences rooted at `r`. -/
private noncomputable def parentEquiv :
    {f : {v // v ≠ r} → V // Acyclic f} ≃ {T : Digraph V // T.IsInArborescence r} :=
  Equiv.ofBijective (fun f => ⟨toDigraph f.1, isInArborescence_toDigraph f.2⟩)
    ⟨fun _ _ h => Subtype.ext (toDigraph_injective (congrArg Subtype.val h)),
      fun T => by
        obtain ⟨f, hf, hfT⟩ := exists_toDigraph_eq T.2
        exact ⟨⟨f, hf⟩, Subtype.ext hfT⟩⟩

end Parent

/-! ### The determinant expansion -/

section Det

variable [Fintype V] [DecidableEq V] {R : Type*} [CommRing R] {r : V}

/-- The matrix with rows `e_v - e_{f v}`, where `e_r` is read as `0`. -/
private def parentMatrix (f : {v // v ≠ r} → V) : Matrix {v // v ≠ r} {v // v ≠ r} R :=
  Matrix.of fun i j => (if i = j then 1 else 0) - (if f i = (j : V) then 1 else 0)

private theorem det_parentMatrix_of_not_acyclic {f : {v // v ≠ r} → V} (hf : ¬ Acyclic f) :
    (parentMatrix f : Matrix _ _ R).det = 0 := by
  classical
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, ∀ n, (withRoot f)^[n] v₀ ≠ r := by
    by_contra! h
    exact hf h
  set C : V → Prop := fun v => ∀ n, (withRoot f)^[n] v ≠ r
  have hCr : ¬ C r := fun h => h 0 rfl
  have hC : ∀ i : {v // v ≠ r}, C i ↔ C (f i) := by
    intro i
    constructor
    · intro h n
      have := h (n + 1)
      rwa [Function.iterate_succ_apply, withRoot_of_ne f i.2] at this
    · intro h n
      cases n with
      | zero => exact i.2
      | succ n =>
        rw [Function.iterate_succ_apply, withRoot_of_ne f i.2]
        exact h n
  set c : {v // v ≠ r} → R := fun j => if C j then 1 else 0
  have hv₀r : v₀ ≠ r := fun h => hv₀ 0 h
  have hker : ∀ i, ∑ j, parentMatrix f i j * c j = 0 := by
    intro i
    simp only [parentMatrix, Matrix.of_apply, sub_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hfi : f i = r
    · have : ∑ j : {v // v ≠ r}, (if f i = (j : V) then c j else 0) = 0 :=
        Finset.sum_eq_zero fun j _ =>
          ite_eq_right_iff.mpr fun h => absurd (h.symm.trans hfi) j.2
      rw [this, sub_zero]
      have : ¬ C i := fun h => hCr (hfi ▸ (hC i).1 h)
      simp [c, this]
    · rw [Finset.sum_eq_single ⟨f i, hfi⟩]
      · simp [c, hC i]
      · intro j _ hj
        exact ite_eq_right_iff.mpr fun h => absurd (Subtype.ext h.symm) hj
      · simp
  have := det_updateCol_sum (parentMatrix f : Matrix _ _ R) ⟨v₀, hv₀r⟩ c
  have hzero : (fun k => ∑ i, c i • (parentMatrix f : Matrix _ _ R) k i) = 0 := by
    funext k
    simp only [smul_eq_mul, Pi.zero_apply]
    rw [← hker k]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hzero] at this
  have hc : c ⟨v₀, hv₀r⟩ = 1 := by simp [c, C, hv₀]
  rw [hc, one_smul] at this
  rw [← this]
  exact det_eq_zero_of_column_eq_zero ⟨v₀, hv₀r⟩ fun i => by simp

private theorem det_parentMatrix_of_acyclic {f : {v // v ≠ r} → V} (hf : Acyclic f) :
    (parentMatrix f : Matrix _ _ R).det = 1 := by
  classical
  let d : V → ℕ := fun v => Nat.find (hf v)
  have hd : ∀ i : {v // v ≠ r}, d (f i) < d i := by
    intro i
    have h1 : (withRoot f)^[d i] i = r := Nat.find_spec (hf i)
    have hpos : d i ≠ 0 := by
      intro h0
      rw [h0, Function.iterate_zero_apply] at h1
      exact i.2 h1
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm, Function.iterate_succ_apply, withRoot_of_ne f i.2] at h1
    have : d (f i) ≤ m := Nat.find_min' (hf (f i)) h1
    omega
  have hne : ∀ i : {v // v ≠ r}, f i ≠ i := fun i h => by
    have := hd i
    rw [h] at this
    exact lt_irrefl _ this
  rw [← det_transpose]
  refine (det_eq_prod_diag_of_weight (parentMatrix f : Matrix _ _ R)ᵀ (fun i => d i)
    fun i j hij h => ?_).trans ?_
  · simp only [transpose_apply, parentMatrix, Matrix.of_apply, Ne.symm hij, ↓reduceIte,
      zero_sub, ne_eq, neg_eq_zero, ite_eq_right_iff, Classical.not_imp] at h
    obtain ⟨h, -⟩ := h
    rw [← h]
    exact hd j
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [parentMatrix, hne i]

/-- The determinant of the reduced Laplacian expands over parent functions. -/
private theorem det_laplacian_submatrix_eq_sum (A : Matrix V V R) (r : V) :
    (A.laplacian.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      ∑ f : {v // v ≠ r} → V, (∏ i : {v // v ≠ r}, A i (f i)) *
        (parentMatrix f : Matrix _ _ R).det := by
  classical
  have hrow : (A.laplacian.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val) =
      fun i : {v // v ≠ r} => ∑ u : V, A i u • fun j : {v // v ≠ r} =>
        (if i = j then (1 : R) else 0) - (if u = (j : V) then 1 else 0) := by
    funext i j
    rw [submatrix_apply, laplacian_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hij : i = j
    · subst hij
      simp
    · have : (i : V) ≠ j := fun h => hij (Subtype.ext h)
      simp [hij, this]
  rw [hrow]
  refine ((detRowAlternating : ({v // v ≠ r} → R) [⋀^{v // v ≠ r}]→ₗ[R] R).toMultilinearMap.map_sum
    (fun (i : {v // v ≠ r}) (u : V) => A i u • fun j : {v // v ≠ r} =>
      (if i = j then (1 : R) else 0) - (if u = (j : V) then 1 else 0))).trans
    (Finset.sum_congr rfl fun f _ => ?_)
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- **The directed matrix-tree theorem** [Tutte1948]. For a matrix `A` of arc weights over a
commutative ring and a vertex `r`, the determinant of the reduced Laplacian, the submatrix of
`Matrix.laplacian A` on the vertices other than `r`, is the sum, over the spanning
in-arborescences `T` rooted at `r` (arcs directed towards `r`), of the product of the weights
`A v w` of the arcs `v → w` of `T`. The Laplacian is the out-degree one,
`diagonal (fun v => ∑ w, A v w) - A`. Applied to `Aᵀ`, the same statement sums over the
out-arborescences of `A` rooted at `r`. -/
theorem det_laplacian_submatrix_eq_finsum_isInArborescence (A : Matrix V V R) (r : V) :
    (A.laplacian.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      ∑ᶠ (T : Digraph V) (_ : T.IsInArborescence r),
        ∏ᶠ (p : V × V) (_ : T.Adj p.1 p.2), A p.1 p.2 := by
  classical
  rw [det_laplacian_submatrix_eq_sum]
  have hterm : ∀ f : {v // v ≠ r} → V,
      (∏ i : {v // v ≠ r}, A i (f i)) * (parentMatrix f : Matrix _ _ R).det =
        if Acyclic f then ∏ i : {v // v ≠ r}, A i (f i) else 0 := by
    intro f
    split_ifs with hf
    · rw [det_parentMatrix_of_acyclic hf, mul_one]
    · rw [det_parentMatrix_of_not_acyclic hf, mul_zero]
  simp only [hterm]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := Acyclic) _ (fun f => by simp),
    ← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv parentEquiv, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun f _ => ?_
  change _ = ∏ᶠ (p : V × V) (_ : p ∈ {p : V × V | (toDigraph f.1).Adj p.1 p.2}), A p.1 p.2
  rw [setOf_adj_toDigraph, finprod_mem_range (fun a b h => Subtype.ext (congrArg Prod.fst h)),
    finprod_eq_prod_of_fintype]

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- The product of the weights `G.adjMatrix R` over the arcs of `T` is `1` if `T ≤ G` and `0`
otherwise. -/
private theorem finprod_adjMatrix [Finite V] (G T : Digraph V) [DecidableRel G.Adj] :
    ∏ᶠ (p : V × V) (_ : T.Adj p.1 p.2), G.adjMatrix R p.1 p.2 = if T ≤ G then 1 else 0 := by
  have : Fintype V := Fintype.ofFinite V
  split_ifs with hTG
  · exact finprod_mem_eq_one_of_forall_eq_one (s := {p : V × V | T.Adj p.1 p.2})
      fun p hp => by simp [hTG hp]
  · obtain ⟨v, w, hT, hG⟩ : ∃ v w, T.Adj v w ∧ ¬ G.Adj v w := by
      by_contra! h
      exact hTG fun v w => h v w
    change ∏ᶠ (p : V × V) (_ : p ∈ {p : V × V | T.Adj p.1 p.2}), G.adjMatrix R p.1 p.2 = 0
    rw [finprod_mem_eq_toFinset_prod]
    exact Finset.prod_eq_zero (i := (v, w)) (by simpa using hT) (by simp [hG])

/-- **The directed matrix-tree theorem**, counting form [Tutte1948]. For a finite digraph `G` and
a vertex `r`, the determinant of the reduced Laplacian of `G`, the out-degree matrix minus the
adjacency matrix with the row and column of `r` deleted, is the number of spanning
in-arborescences `T ≤ G` rooted at `r` (arcs directed towards `r`). Loops of `G` do not
contribute. -/
theorem det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence (G : Digraph V)
    [DecidableRel G.Adj] (r : V) :
    ((G.adjMatrix R).laplacian.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).det =
      Nat.card {T : Digraph V // T ≤ G ∧ T.IsInArborescence r} := by
  classical
  rw [det_laplacian_submatrix_eq_finsum_isInArborescence]
  simp only [finprod_adjMatrix, finsum_eq_if]
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [← ite_and, Finset.sum_boole]
  congr 2
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

end Det

end Digraph
