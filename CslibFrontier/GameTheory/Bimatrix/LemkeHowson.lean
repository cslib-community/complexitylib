/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The Lemke–Howson graph of a pair of labelled polyhedra

Let `A₁ *ᵥ x ≤ b₁` (with `x : ι₁ → K`) and `A₂ *ᵥ y ≤ b₂` (with `y : ι₂ → K`) be two systems of
inequalities whose rows are indexed by the same set `κ` of *labels*. A label of a point is a row
that is tight there (`Matrix.tightRows`). A pair `(x, y)` is *completely labelled*
(`LemkeHowson.CompletelyLabeled`) if every label is a label of `x` or of `y`, and, for a fixed
label `k`, *`k`-almost completely labelled* if every label other than `k` is.

This is the combinatorial core of the Lemke–Howson algorithm [LemkeHowson1964], in the polytope
form of [vonStengel2007], Section 3.4. Suppose both systems are nondegenerate and bounded, and
`card κ = card ι₁ + card ι₂`. The `k`-almost completely labelled vertex pairs are the nodes of the
graph `LemkeHowson.graph`, whose edges keep one of the two vertices and replace the other by an
adjacent vertex of its polyhedron (`Matrix.VertexAdj`, a pivot). A node has degree `1` if it is
completely labelled (`LemkeHowson.ncard_neighborSet_of_completelyLabeled`) and degree `2` otherwise
(`LemkeHowson.ncard_neighborSet_of_not_completelyLabeled`). At a completely labelled pair the two
label sets are disjoint, so only `k` can be dropped, from the side that has it. At any other node
`k` is missing and exactly one label is duplicate, and it can be dropped from either side. Since a
finite graph has an even number of odd-degree vertices, the number of completely labelled vertex
pairs is even (`LemkeHowson.even_ncard_completelyLabeled`).

For a bimatrix game, the completely labelled vertex pairs of the two best response polytopes are
the Nash equilibria together with the artificial pair `(0, 0)`, so a nondegenerate bimatrix game
has an odd number of Nash equilibria; see
`CslibFrontier.GameTheory.Bimatrix.BestResponsePolytope`.

## Main definitions

* `LemkeHowson.CompletelyLabeled`: every label is a tight row of `x` or of `y`.
* `LemkeHowson.Node`: a `k`-almost completely labelled vertex pair.
* `LemkeHowson.graph`: the Lemke–Howson graph on `k`-almost completely labelled vertex pairs.

## Main results

* `LemkeHowson.graph_adj_iff`: the neighbours of a node are obtained by dropping either the label
  `k` or a duplicate label, from `x` or from `y`.
* `LemkeHowson.ncard_neighborSet_of_completelyLabeled`,
  `LemkeHowson.ncard_neighborSet_of_not_completelyLabeled`: the degree is `1` at completely
  labelled nodes and `2` elsewhere.
* `LemkeHowson.isVertex_left_of_completelyLabeled`: a feasible completely labelled pair consists
  of vertices.
* `LemkeHowson.even_ncard_completelyLabeled`: there is an even number of completely labelled
  vertex pairs.

## References

* [C. E. Lemke and J. T. Howson, Jr., *Equilibrium points of bimatrix games*][LemkeHowson1964]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Section 3.4
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.LemkeHowson

variable {K : Type*} [Field K] [LinearOrder K]
variable {ι₁ ι₂ κ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ]
variable (A₁ : Matrix κ ι₁ K) (b₁ : κ → K) (A₂ : Matrix κ ι₂ K) (b₂ : κ → K)

/-- `(x, y)` is *completely labelled*: every label is a tight row of `x` or of `y`. -/
def CompletelyLabeled (x : ι₁ → K) (y : ι₂ → K) : Prop :=
  ∀ j, j ∈ tightRows A₁ b₁ x ∨ j ∈ tightRows A₂ b₂ y

/-- A *node* of the Lemke–Howson graph for the missing label `k`: a pair of vertices of the two
polyhedra in which every label other than `k` is a tight row of `x` or of `y`. -/
structure Node (k : κ) where
  /-- The vertex of the first polyhedron. -/
  x : ι₁ → K
  /-- The vertex of the second polyhedron. -/
  y : ι₂ → K
  /-- `x` is a vertex of the first polyhedron. -/
  isVertex_x : IsVertex A₁ b₁ x
  /-- `y` is a vertex of the second polyhedron. -/
  isVertex_y : IsVertex A₂ b₂ y
  /-- The pair is `k`-almost completely labelled. -/
  almostCompletelyLabeled : ∀ j, j ≠ k → j ∈ tightRows A₁ b₁ x ∨ j ∈ tightRows A₂ b₂ y

variable {A₁ b₁ A₂ b₂} {k : κ}

theorem completelyLabeled_iff {x : ι₁ → K} {y : ι₂ → K} :
    CompletelyLabeled A₁ b₁ A₂ b₂ x y ↔ ∀ j, j ∈ tightRows A₁ b₁ x ∨ j ∈ tightRows A₂ b₂ y :=
  Iff.rfl

@[ext]
theorem Node.ext {p q : Node A₁ b₁ A₂ b₂ k} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p; cases q; cases hx; cases hy; rfl

/-- The pair of vertices of a node. -/
def Node.toProd (p : Node A₁ b₁ A₂ b₂ k) : (ι₁ → K) × (ι₂ → K) := (p.x, p.y)

theorem Node.toProd_injective :
    Function.Injective (Node.toProd : Node A₁ b₁ A₂ b₂ k → (ι₁ → K) × (ι₂ → K)) :=
  fun p q h => Node.ext (by simpa [Node.toProd] using congrArg Prod.fst h)
    (by simpa [Node.toProd] using congrArg Prod.snd h)

/-- The pair of vertices of `Node.mk x y _ _ _` is `(x, y)`. -/
theorem Node.toProd_mk {x : ι₁ → K} {y : ι₂ → K} (hx : IsVertex A₁ b₁ x) (hy : IsVertex A₂ b₂ y)
    (h : ∀ j, j ≠ k → j ∈ tightRows A₁ b₁ x ∨ j ∈ tightRows A₂ b₂ y) :
    (Node.mk x y hx hy h).toProd = (x, y) := by
  rw [Node.toProd]

/-- There are finitely many nodes. -/
theorem finite_node : Finite (Node A₁ b₁ A₂ b₂ k) := by
  have := ((setOf_isVertex_finite (A := A₁) (b := b₁)).prod
    (setOf_isVertex_finite (A := A₂) (b := b₂))).to_subtype
  exact Finite.of_injective
    (fun p : Node A₁ b₁ A₂ b₂ k => (⟨(p.x, p.y), p.isVertex_x, p.isVertex_y⟩ :
      ↥({x | IsVertex A₁ b₁ x} ×ˢ {y | IsVertex A₂ b₂ y})))
    (fun _ _ h => Node.toProd_injective (by simpa [Node.toProd] using congrArg Subtype.val h))

variable [DecidableEq κ]

variable (A₁ b₁ A₂ b₂ k) in
/-- The *Lemke–Howson graph* for the missing label `k`: two `k`-almost completely labelled vertex
pairs are adjacent if they agree in one polyhedron and are adjacent vertices in the other. -/
def graph : SimpleGraph (Node A₁ b₁ A₂ b₂ k) where
  Adj p q := (p.x = q.x ∧ VertexAdj A₂ b₂ p.y q.y) ∨ (p.y = q.y ∧ VertexAdj A₁ b₁ p.x q.x)
  symm := ⟨fun _ _ h => h.elim (fun h => .inl ⟨h.1.symm, h.2.symm⟩)
    (fun h => .inr ⟨h.1.symm, h.2.symm⟩)⟩
  loopless := ⟨fun p h => by
    rcases h with h | h
    · exact h.2.ne rfl
    · exact h.2.ne rfl⟩

theorem graph_adj {p q : Node A₁ b₁ A₂ b₂ k} : (graph A₁ b₁ A₂ b₂ k).Adj p q ↔
    (p.x = q.x ∧ VertexAdj A₂ b₂ p.y q.y) ∨ (p.y = q.y ∧ VertexAdj A₁ b₁ p.x q.x) := by
  rw [graph]

omit [Fintype κ] in
/-- Dropping the label `l` from one side of a `k`-almost completely labelled pair keeps it
`k`-almost completely labelled iff `l = k` or `l` is a label of the other side. -/
private theorem acl_pivot_iff {T T' S : Finset κ} {l : κ} (hT : ∀ j, j ≠ k → j ∈ T ∨ j ∈ S)
    (hT' : T.erase l ⊆ T') (hl : l ∉ T') :
    (∀ j, j ≠ k → j ∈ T' ∨ j ∈ S) ↔ l = k ∨ l ∈ S := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rcases h l hne.1 with h | h
    · exact hl h
    · exact hne.2 h
  · intro h j hj
    by_cases hjl : j = l
    · subst hjl
      exact .inr (h.resolve_left hj)
    · rcases hT j hj with h' | h'
      · exact .inl (hT' (mem_erase.2 ⟨hjl, h'⟩))
      · exact .inr h'

/-- If the label sets of a completely labelled pair have sizes adding up to `card κ`, then
exactly one label can be dropped: `k` itself, from the side that has it. -/
private theorem card_filter_add_card_filter_of_forall {T₁ T₂ : Finset κ}
    (hcard : #T₁ + #T₂ = Fintype.card κ) (hcl : ∀ j, j ∈ T₁ ∨ j ∈ T₂) :
    #{l ∈ T₁ | l = k ∨ l ∈ T₂} + #{l ∈ T₂ | l = k ∨ l ∈ T₁} = 1 := by
  have hui := card_union_add_card_inter T₁ T₂
  have hu : T₁ ∪ T₂ = univ := eq_univ_of_forall fun j => mem_union.2 (hcl j)
  rw [hu, card_univ] at hui
  have hdisj : Disjoint T₁ T₂ := disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 (by omega))
  rw [filter_congr (q := (· = k)) fun l hl => or_iff_left (disjoint_left.1 hdisj hl),
    filter_congr (q := (· = k)) fun l hl => or_iff_left (disjoint_right.1 hdisj hl),
    filter_eq', filter_eq']
  rcases hcl k with h | h
  · simp [h, disjoint_left.1 hdisj h]
  · simp [h, disjoint_right.1 hdisj h]

/-- If the label sets of a `k`-almost but not completely labelled pair have sizes adding up to
`card κ`, then exactly one label is duplicate, and it can be dropped from either side. -/
private theorem card_filter_add_card_filter_of_not_forall {T₁ T₂ : Finset κ}
    (hcard : #T₁ + #T₂ = Fintype.card κ) (hacl : ∀ j, j ≠ k → j ∈ T₁ ∨ j ∈ T₂)
    (hcl : ¬ ∀ j, j ∈ T₁ ∨ j ∈ T₂) :
    #{l ∈ T₁ | l = k ∨ l ∈ T₂} + #{l ∈ T₂ | l = k ∨ l ∈ T₁} = 2 := by
  push Not at hcl
  obtain ⟨j, hj1, hj2⟩ := hcl
  have hjk : j = k := by
    by_contra h
    rcases hacl j h with h | h <;> contradiction
  subst hjk
  have hui := card_union_add_card_inter T₁ T₂
  have hu : T₁ ∪ T₂ = univ.erase j := by
    ext l
    simp only [mem_union, mem_erase, mem_univ, and_true]
    constructor
    · rintro (h | h) rfl <;> contradiction
    · exact hacl l
  have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.2 ⟨j⟩
  rw [hu, card_erase_of_mem (mem_univ _), card_univ] at hui
  rw [filter_congr (q := (· ∈ T₂)) fun l hl => or_iff_right (fun (h : l = j) => hj1 (h ▸ hl)),
    filter_congr (q := (· ∈ T₁)) fun l hl => or_iff_right (fun (h : l = j) => hj2 (h ▸ hl)),
    filter_mem_eq_inter, filter_mem_eq_inter, inter_comm T₂]
  omega

variable [IsStrictOrderedRing K]

omit [DecidableEq κ] in
/-- A feasible completely labelled pair in two bounded nondegenerate systems with
`card κ = card ι₁ + card ι₂` consists of vertices: the first point is a vertex. -/
theorem isVertex_left_of_completelyLabeled (hnd₁ : IsNondegenerateSystem A₁ b₁)
    (hrec₁ : ∀ v, A₁ *ᵥ v ≤ 0 → v = 0) (hnd₂ : IsNondegenerateSystem A₂ b₂)
    (hcard : Fintype.card κ = Fintype.card ι₁ + Fintype.card ι₂) {x : ι₁ → K} {y : ι₂ → K}
    (hx : A₁ *ᵥ x ≤ b₁) (hy : A₂ *ᵥ y ≤ b₂) (hcl : CompletelyLabeled A₁ b₁ A₂ b₂ x y) :
    IsVertex A₁ b₁ x := by
  classical
  refine isVertex_of_card_tightRows hnd₁ hrec₁ hx ?_
  have hu : tightRows A₁ b₁ x ∪ tightRows A₂ b₂ y = univ :=
    eq_univ_of_forall fun j => mem_union.2 (hcl j)
  have h1 := card_union_le (tightRows A₁ b₁ x) (tightRows A₂ b₂ y)
  rw [hu, card_univ, hcard] at h1
  have h2 := isNondegenerateSystem_iff.1 hnd₂ y hy
  omega

omit [DecidableEq κ] in
/-- A feasible completely labelled pair in two bounded nondegenerate systems with
`card κ = card ι₁ + card ι₂` consists of vertices: the second point is a vertex. -/
theorem isVertex_right_of_completelyLabeled (hnd₁ : IsNondegenerateSystem A₁ b₁)
    (hnd₂ : IsNondegenerateSystem A₂ b₂) (hrec₂ : ∀ v, A₂ *ᵥ v ≤ 0 → v = 0)
    (hcard : Fintype.card κ = Fintype.card ι₁ + Fintype.card ι₂) {x : ι₁ → K} {y : ι₂ → K}
    (hx : A₁ *ᵥ x ≤ b₁) (hy : A₂ *ᵥ y ≤ b₂) (hcl : CompletelyLabeled A₁ b₁ A₂ b₂ x y) :
    IsVertex A₂ b₂ y := by
  classical
  refine isVertex_of_card_tightRows hnd₂ hrec₂ hy ?_
  have hu : tightRows A₁ b₁ x ∪ tightRows A₂ b₂ y = univ :=
    eq_univ_of_forall fun j => mem_union.2 (hcl j)
  have h1 := card_union_le (tightRows A₁ b₁ x) (tightRows A₂ b₂ y)
  rw [hu, card_univ, hcard] at h1
  have h2 := isNondegenerateSystem_iff.1 hnd₁ x hx
  omega

variable (hnd₁ : IsNondegenerateSystem A₁ b₁) (hrec₁ : ∀ v, A₁ *ᵥ v ≤ 0 → v = 0)
  (hnd₂ : IsNondegenerateSystem A₂ b₂) (hrec₂ : ∀ v, A₂ *ᵥ v ≤ 0 → v = 0)
include hnd₁ hrec₁ hnd₂ hrec₂

/-- The neighbours of a node `p` in the Lemke–Howson graph: either `x` pivots on a label `l` that is
`k` or a label of `y`, or `y` pivots on a label `l` that is `k` or a label of `x`. -/
theorem graph_adj_iff {p q : Node A₁ b₁ A₂ b₂ k} :
    (graph A₁ b₁ A₂ b₂ k).Adj p q ↔
      (∃ l ∈ tightRows A₁ b₁ p.x, (l = k ∨ l ∈ tightRows A₂ b₂ p.y) ∧
        q.x = pivotVertex A₁ b₁ p.x l ∧ q.y = p.y) ∨
      (∃ l ∈ tightRows A₂ b₂ p.y, (l = k ∨ l ∈ tightRows A₁ b₁ p.x) ∧
        q.y = pivotVertex A₂ b₂ p.y l ∧ q.x = p.x) := by
  rw [graph_adj]
  constructor
  · rintro (⟨hxe, hadj⟩ | ⟨hye, hadj⟩)
    · obtain ⟨l, hl, hq⟩ := (vertexAdj_iff_exists_pivotVertex hnd₂ hrec₂ p.isVertex_y).1 hadj
      obtain ⟨-, -, hT⟩ := p.isVertex_y.pivotVertex_spec hnd₂ hrec₂ hl
      have hlq := p.isVertex_y.notMem_tightRows_pivotVertex hnd₂ hrec₂ hl
      have key := (acl_pivot_iff (S := tightRows A₁ b₁ p.x)
        (fun j hj => (p.almostCompletelyLabeled j hj).symm) hT hlq).1
        (fun j hj => by rw [← hq, hxe]; exact (q.almostCompletelyLabeled j hj).symm)
      exact .inr ⟨l, hl, key, hq, hxe.symm⟩
    · obtain ⟨l, hl, hq⟩ := (vertexAdj_iff_exists_pivotVertex hnd₁ hrec₁ p.isVertex_x).1 hadj
      obtain ⟨-, -, hT⟩ := p.isVertex_x.pivotVertex_spec hnd₁ hrec₁ hl
      have hlq := p.isVertex_x.notMem_tightRows_pivotVertex hnd₁ hrec₁ hl
      have key := (acl_pivot_iff (S := tightRows A₂ b₂ p.y) p.almostCompletelyLabeled hT hlq).1
        (fun j hj => by rw [← hq, hye]; exact q.almostCompletelyLabeled j hj)
      exact .inl ⟨l, hl, key, hq, hye.symm⟩
  · rintro (⟨l, hl, -, hqx, hqy⟩ | ⟨l, hl, -, hqy, hqx⟩)
    · exact .inr ⟨hqy.symm, hqx ▸ (vertexAdj_iff_exists_pivotVertex hnd₁ hrec₁ p.isVertex_x).2
        ⟨l, hl, rfl⟩⟩
    · exact .inl ⟨hqx.symm, hqy ▸ (vertexAdj_iff_exists_pivotVertex hnd₂ hrec₂ p.isVertex_y).2
        ⟨l, hl, rfl⟩⟩

/-- The degree of a node is the number of labels that may be dropped: labels of `x` that are `k`
or labels of `y`, plus labels of `y` that are `k` or labels of `x`. -/
theorem ncard_neighborSet (p : Node A₁ b₁ A₂ b₂ k) :
    ((graph A₁ b₁ A₂ b₂ k).neighborSet p).ncard =
      #{l ∈ tightRows A₁ b₁ p.x | l = k ∨ l ∈ tightRows A₂ b₂ p.y} +
      #{l ∈ tightRows A₂ b₂ p.y | l = k ∨ l ∈ tightRows A₁ b₁ p.x} := by
  have himage : Node.toProd '' (graph A₁ b₁ A₂ b₂ k).neighborSet p =
      ↑(({l ∈ tightRows A₁ b₁ p.x | l = k ∨ l ∈ tightRows A₂ b₂ p.y} : Finset κ).image
          (fun l => (pivotVertex A₁ b₁ p.x l, p.y)) ∪
        ({l ∈ tightRows A₂ b₂ p.y | l = k ∨ l ∈ tightRows A₁ b₁ p.x} : Finset κ).image
          (fun l => (p.x, pivotVertex A₂ b₂ p.y l))) := by
    ext ⟨u, w⟩
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet, coe_union, coe_image, Set.mem_union,
      mem_coe, mem_filter]
    constructor
    · rintro ⟨q, hq, hqe⟩
      rw [graph_adj_iff hnd₁ hrec₁ hnd₂ hrec₂] at hq
      simp only [Node.toProd, Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      rcases hq with ⟨l, hl, hlk, hqx, hqy⟩ | ⟨l, hl, hlk, hqy, hqx⟩
      · exact .inl ⟨l, ⟨hl, hlk⟩, by rw [hqx, hqy]⟩
      · exact .inr ⟨l, ⟨hl, hlk⟩, by rw [hqx, hqy]⟩
    · rintro (⟨l, ⟨hl, hlk⟩, he⟩ | ⟨l, ⟨hl, hlk⟩, he⟩)
      · obtain ⟨hv, -, hT⟩ := p.isVertex_x.pivotVertex_spec hnd₁ hrec₁ hl
        have hlq := p.isVertex_x.notMem_tightRows_pivotVertex hnd₁ hrec₁ hl
        refine ⟨⟨pivotVertex A₁ b₁ p.x l, p.y, hv, p.isVertex_y,
          (acl_pivot_iff p.almostCompletelyLabeled hT hlq).2 hlk⟩, ?_, he⟩
        rw [graph_adj_iff hnd₁ hrec₁ hnd₂ hrec₂]
        exact .inl ⟨l, hl, hlk, rfl, rfl⟩
      · obtain ⟨hv, -, hT⟩ := p.isVertex_y.pivotVertex_spec hnd₂ hrec₂ hl
        have hlq := p.isVertex_y.notMem_tightRows_pivotVertex hnd₂ hrec₂ hl
        refine ⟨⟨p.x, pivotVertex A₂ b₂ p.y l, p.isVertex_x, hv, fun j hj =>
          ((acl_pivot_iff (fun j hj => (p.almostCompletelyLabeled j hj).symm) hT hlq).2 hlk j
            hj).symm⟩, ?_, he⟩
        rw [graph_adj_iff hnd₁ hrec₁ hnd₂ hrec₂]
        exact .inr ⟨l, hl, hlk, rfl, rfl⟩
  rw [← Set.ncard_image_of_injective _ Node.toProd_injective, himage, Set.ncard_coe_finset,
    card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn]
  · intro l₁ hl₁ l₂ hl₂ h
    exact p.isVertex_y.pivotVertex_injOn hnd₂ hrec₂ (mem_filter.1 hl₁).1 (mem_filter.1 hl₂).1
      (congrArg Prod.snd h)
  · intro l₁ hl₁ l₂ hl₂ h
    exact p.isVertex_x.pivotVertex_injOn hnd₁ hrec₁ (mem_filter.1 hl₁).1 (mem_filter.1 hl₂).1
      (congrArg Prod.fst h)
  · rw [disjoint_left]
    intro u hu₁ hu₂
    simp only [mem_image] at hu₁ hu₂
    obtain ⟨l₁, hl₁, rfl⟩ := hu₁
    obtain ⟨l₂, -, he⟩ := hu₂
    exact (p.isVertex_x.pivotVertex_spec hnd₁ hrec₁ (mem_filter.1 hl₁).1).2.1
      (congrArg Prod.fst he).symm

/-- A completely labelled node has exactly one neighbour in the Lemke–Howson graph. -/
theorem ncard_neighborSet_of_completelyLabeled
    (hcard : Fintype.card κ = Fintype.card ι₁ + Fintype.card ι₂) (p : Node A₁ b₁ A₂ b₂ k)
    (h : CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y) :
    ((graph A₁ b₁ A₂ b₂ k).neighborSet p).ncard = 1 := by
  rw [ncard_neighborSet hnd₁ hrec₁ hnd₂ hrec₂]
  exact card_filter_add_card_filter_of_forall
    (by rw [p.isVertex_x.card_tightRows hnd₁, p.isVertex_y.card_tightRows hnd₂, hcard]) h

/-- A node that is not completely labelled has exactly two neighbours in the Lemke–Howson
graph. -/
theorem ncard_neighborSet_of_not_completelyLabeled
    (hcard : Fintype.card κ = Fintype.card ι₁ + Fintype.card ι₂) (p : Node A₁ b₁ A₂ b₂ k)
    (h : ¬ CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y) :
    ((graph A₁ b₁ A₂ b₂ k).neighborSet p).ncard = 2 := by
  rw [ncard_neighborSet hnd₁ hrec₁ hnd₂ hrec₂]
  exact card_filter_add_card_filter_of_not_forall
    (by rw [p.isVertex_x.card_tightRows hnd₁, p.isVertex_y.card_tightRows hnd₂, hcard])
    p.almostCompletelyLabeled h

omit [DecidableEq κ] in
/-- **Parity of completely labelled vertex pairs** ([vonStengel2007], Section 3.4). For two bounded
nondegenerate systems whose rows are labelled by a nonempty set `κ` with
`card κ = card ι₁ + card ι₂`, the number of completely labelled vertex pairs is even: they are
the odd-degree vertices of the Lemke–Howson graph for any missing label. -/
theorem even_ncard_completelyLabeled [Nonempty κ]
    (hcard : Fintype.card κ = Fintype.card ι₁ + Fintype.card ι₂) :
    Even {p : (ι₁ → K) × (ι₂ → K) | IsVertex A₁ b₁ p.1 ∧ IsVertex A₂ b₂ p.2 ∧
      CompletelyLabeled A₁ b₁ A₂ b₂ p.1 p.2}.ncard := by
  classical
  obtain ⟨k⟩ := ‹Nonempty κ›
  have := finite_node (A₁ := A₁) (b₁ := b₁) (A₂ := A₂) (b₂ := b₂) (k := k)
  let := Fintype.ofFinite (Node A₁ b₁ A₂ b₂ k)
  have heven := (graph A₁ b₁ A₂ b₂ k).even_card_odd_degree_vertices
  have hodd : (univ.filter fun p => Odd ((graph A₁ b₁ A₂ b₂ k).degree p)) =
      univ.filter fun p : Node A₁ b₁ A₂ b₂ k => CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      SimpleGraph.coe_neighborFinset]
    by_cases h : CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y
    · simp [h, ncard_neighborSet_of_completelyLabeled hnd₁ hrec₁ hnd₂ hrec₂ hcard p h]
    · simp [h, ncard_neighborSet_of_not_completelyLabeled hnd₁ hrec₁ hnd₂ hrec₂ hcard p h]
  rw [hodd] at heven
  convert heven using 1
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Node.toProd_injective]
  congr 1
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, coe_filter, mem_univ, true_and, Set.mem_image]
  constructor
  · rintro ⟨hx, hy, hcl⟩
    exact ⟨⟨x, y, hx, hy, fun j _ => hcl j⟩, hcl, Node.toProd_mk _ _ _⟩
  · rintro ⟨p, hcl, he⟩
    simp only [Node.toProd, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨p.isVertex_x, p.isVertex_y, hcl⟩

end Cslib.GameTheory.LemkeHowson
