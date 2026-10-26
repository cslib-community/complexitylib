/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.RegularConstraintGraph
public import Complexity.Foundations.Combinatorics.Expander.Mixing
import Complexity.Foundations.Data.Finset.Quantile

/-!
# Degree reduction

The first step of Dinur's preprocessing [Dinur, Section 3.1][Dinur2005]: an arbitrary constraint
graph, whose vertices may have wildly different degrees, is replaced by a regular one over the same
alphabet, losing at most a constant factor of its value. This is the expander replacement of
Papadimitriou and Yannakakis: every vertex is split into one copy per edge end at it, and the
copies of a vertex are joined by an expander carrying equality constraints.

The vertices of the new constraint graph `G.degreeReduce H` are the **half-edges** `(e, b)` of `G`:
an edge `e` with one of its ends, the first one for `b = false` and the second one for `b = true`.
There are `2 |E|` of them, whatever the degrees of `G`. Each half-edge has

* one **edge-link**, labelled `inl ()`, to the other half of its edge, carrying the constraint of
  that edge, and
* `|D|` **cloud-links**, labelled `inr i`, given by a regular multigraph `H v` on the **cloud** of
  half-edges at the same vertex `v`, carrying equality constraints.

So `G.degreeReduce H` is `(1 + |D|)`-regular. A labelling satisfying `G` labels every half-edge by
the label of its vertex and satisfies the new constraint graph (`satisfiable_degreeReduce`). In the
other direction, from a labelling `A` of the half-edges, label every vertex `v` by a most frequent
label `σ v` of its cloud. A half-edge disagreeing with the label of its vertex is charged to the
cloud-links joining differently labelled half-edges of its cloud, which all violate their equality
constraints. When `H v` is an expander there are many of them: at least `(1 - μ) |D|` per
disagreeing half-edge, since the half-edges with any label `a` are at most as many as those with
the label `σ v`, so that many edges leave them
(`Cslib.RotationMap.mul_card_filter_ne_le_card_filter_ne_neighbor`). An edge violated by `σ`
either has a disagreeing half-edge, or its edge-links are violated by `A`. Trading the two charges
off shows that the proportion of darts violated by `A` is at least
`min 1 ((1 - μ) |D|) / (2 (1 + |D|))` times the value of `G`, when the spectral expansion of every
`H v` is at most `μ` (`le_unsatVal_degreeReduce`). The constant does not depend on the alphabet, as
in Dinur's analysis.

## Main definitions

* `Cslib.PCP.ConstraintGraph.endpoint`, `Cslib.PCP.ConstraintGraph.Cloud`: the vertex of a
  half-edge, and the half-edges at a vertex.
* `Cslib.PCP.ConstraintGraph.cloudGraph`: the regular multigraph on the half-edges joining each
  cloud by a given multigraph.
* `Cslib.PCP.ConstraintGraph.degreeReduce`: the degree-reduced regular constraint graph.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_degreeReduce`: completeness.
* `Cslib.PCP.ConstraintGraph.one_add_card_mul_unsatVal_degreeReduce_le`: degree reduction divides
  the value by at least `1 + |D|`.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_degreeReduce`: soundness.
* `Cslib.PCP.ConstraintGraph.satisfiable_degreeReduce_iff`: with expanders on the clouds, degree
  reduction preserves satisfiability.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

open Finset

namespace Cslib.PCP

namespace ConstraintGraph

variable {V E D α : Type*} (G : ConstraintGraph V E α)

/-! ### Half-edges and clouds -/

/-- The vertex of a half-edge `(e, b)`: the first end of `e` for `b = false`, the second one for
`b = true`. -/
def endpoint : E × Bool → V
  | (e, false) => G.src e
  | (e, true) => G.dst e

/-- The vertex of the first half of an edge is its first end. -/
@[simp]
theorem endpoint_false (e : E) : G.endpoint (e, false) = G.src e :=
  rfl

/-- The vertex of the second half of an edge is its second end. -/
@[simp]
theorem endpoint_true (e : E) : G.endpoint (e, true) = G.dst e :=
  rfl

/-- The cloud of a vertex: the half-edges at it. -/
abbrev Cloud (v : V) : Type _ :=
  {p : E × Bool // G.endpoint p = v}

/-- The regular multigraph on the half-edges whose edges join, within the cloud of every vertex
`v`, the half-edges as `H v` does. -/
def cloudGraph (H : ∀ v, RotationMap (G.Cloud v) D) : RotationMap (E × Bool) D where
  rot p := Prod.map Subtype.val id ((H (G.endpoint p.1)).rot (⟨p.1, rfl⟩, p.2))
  rot_involutive := by
    have key (v : V) (x : G.Cloud v) (i : D) :
        Prod.map Subtype.val id ((H (G.endpoint x.1)).rot (⟨x.1, rfl⟩, i)) =
          Prod.map Subtype.val id ((H v).rot (x, i)) := by
      obtain ⟨x, rfl⟩ := x
      rfl
    rintro ⟨x, i⟩
    simp only [Prod.map_fst, Prod.map_snd]
    rw [key _ ((H (G.endpoint x)).rot (⟨x, rfl⟩, i)).1, id, Prod.mk.eta, RotationMap.rot_rot]
    rfl

variable {G} (H : ∀ v, RotationMap (G.Cloud v) D)

/-- The neighbors of a half-edge in the cloud graph are its neighbors in the multigraph on its
cloud. -/
private theorem neighbor_cloudGraph {v : V} (x : G.Cloud v) (i : D) :
    (G.cloudGraph H).neighbor x.1 i = ((H v).neighbor x i).1 := by
  obtain ⟨x, rfl⟩ := x
  rfl

/-- The neighbors of a half-edge in the cloud graph are in its cloud. -/
@[simp]
theorem endpoint_neighbor_cloudGraph (p : E × Bool) (i : D) :
    G.endpoint ((G.cloudGraph H).neighbor p i) = G.endpoint p := by
  rw [neighbor_cloudGraph H (⟨p, rfl⟩ : G.Cloud (G.endpoint p))]
  exact ((H _).neighbor _ i).2

/-! ### The degree-reduced constraint graph -/

variable (G)

/-- The `1`-regular multigraph joining the two halves of every edge. -/
def halfEdgeGraph : RotationMap (E × Bool) Unit :=
  RotationMap.ofInvolutive (Prod.map id not) fun p ↦ Prod.ext rfl (Bool.not_not p.2)

/-- The other half of the half-edge `(e, b)` is `(e, !b)`. -/
@[simp]
theorem neighbor_halfEdgeGraph (e : E) (b : Bool) (i : Unit) :
    (halfEdgeGraph (E := E)).neighbor (e, b) i = (e, !b) :=
  rfl

/-- The **degree-reduced constraint graph** [Dinur, Section 3.1][Dinur2005]: its vertices are the
half-edges of `G`; the edge-link `inl ()` joins the two halves of an edge `e` and carries the
constraint of `e`, read from its first end to its second one; the cloud-links `inr i` join the
half-edges of every cloud as `H` does and carry equality constraints. -/
def degreeReduce (H : ∀ v, RotationMap (G.Cloud v) D) :
    RegularConstraintGraph (E × Bool) (Unit ⊕ D) α where
  graph := halfEdgeGraph.union (G.cloudGraph H)
  rel q := q.2.elim (fun _ ↦ bif q.1.2 then flip (G.rel q.1.1) else G.rel q.1.1) fun _ ↦ Eq

variable {G}

/-- The underlying multigraph of the degree-reduced constraint graph: the edge-links followed by
the cloud-links. -/
@[simp]
theorem graph_degreeReduce : (G.degreeReduce H).graph = halfEdgeGraph.union (G.cloudGraph H) :=
  rfl

/-- The edge-links at both halves of an edge carry its constraint, read from its first end to its
second one. -/
private theorem satisfies_degreeReduce_inl {A : E × Bool → α} {p : E × Bool} {i : Unit} :
    (G.degreeReduce H).toConstraintGraph.Satisfies A (p, .inl i) ↔
      G.rel p.1 (A (p.1, false)) (A (p.1, true)) := by
  obtain ⟨e, _ | _⟩ := p <;> rfl

/-- The cloud-links carry equality constraints. -/
private theorem satisfies_degreeReduce_inr {A : E × Bool → α} {p : E × Bool} {i : D} :
    (G.degreeReduce H).toConstraintGraph.Satisfies A (p, .inr i) ↔
      A p = A ((G.cloudGraph H).neighbor p i) := by
  obtain ⟨e, _ | _⟩ := p <;> rfl

/-- The labelling of the half-edges by the labels of their vertices satisfies the edge-links of an
edge exactly when the labelling of the vertices satisfies the edge. -/
private theorem satisfies_degreeReduce_comp_endpoint_inl {σ : V → α} {p : E × Bool} {i : Unit} :
    (G.degreeReduce H).toConstraintGraph.Satisfies (σ ∘ G.endpoint) (p, .inl i) ↔
      G.Satisfies σ p.1 :=
  satisfies_degreeReduce_inl H

/-- The labelling of the half-edges by the labels of their vertices satisfies the cloud-links. -/
private theorem satisfies_degreeReduce_comp_endpoint_inr (σ : V → α) (p : E × Bool) (i : D) :
    (G.degreeReduce H).toConstraintGraph.Satisfies (σ ∘ G.endpoint) (p, .inr i) := by
  rw [satisfies_degreeReduce_inr, Function.comp_apply, Function.comp_apply,
    endpoint_neighbor_cloudGraph]

/-- **Completeness of degree reduction**: labelling every half-edge by the label of its vertex
turns a labelling satisfying `G` into one satisfying `G.degreeReduce H`. -/
theorem satisfiable_degreeReduce (h : G.Satisfiable) :
    (G.degreeReduce H).toConstraintGraph.Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ ∘ G.endpoint, ?_⟩
  rintro ⟨p, i | i⟩
  · exact (satisfies_degreeReduce_comp_endpoint_inl H).2 (hσ p.1)
  · exact satisfies_degreeReduce_comp_endpoint_inr H σ p i

section Count

variable [Fintype E] [Fintype D]

/-- The degree-reduced constraint graph has `2 (1 + |D|) |E|` darts. -/
private theorem card_darts_degreeReduce :
    Fintype.card ((E × Bool) × (Unit ⊕ D)) = 2 * (1 + Fintype.card D) * Fintype.card E := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, Fintype.card_unit]
  ring

/-- The labelling of the half-edges by the labels of their vertices violates only the edge-links
of the edges violated by the labelling of the vertices. -/
theorem card_unsatEdges_degreeReduce_comp_endpoint_le (σ : V → α) :
    #((G.degreeReduce H).toConstraintGraph.unsatEdges (σ ∘ G.endpoint)) ≤
      2 * #(G.unsatEdges σ) := by
  classical
  rw [mul_comm, ← Fintype.card_bool, ← card_univ, ← card_product]
  refine card_le_card_of_injOn Prod.fst (fun q hq ↦ ?_) fun q hq q' hq' h ↦ ?_
  · obtain ⟨p, i | i⟩ := q
    · rw [mem_coe, mem_unsatEdges, satisfies_degreeReduce_comp_endpoint_inl] at hq
      simpa using hq
    · rw [mem_coe, mem_unsatEdges] at hq
      exact absurd (satisfies_degreeReduce_comp_endpoint_inr H σ p i) hq
  · obtain ⟨p, i | i⟩ := q
    · obtain ⟨p', i' | i'⟩ := q'
      · exact Prod.ext h rfl
      · rw [mem_coe, mem_unsatEdges] at hq'
        exact absurd (satisfies_degreeReduce_comp_endpoint_inr H σ p' i') hq'
    · rw [mem_coe, mem_unsatEdges] at hq
      exact absurd (satisfies_degreeReduce_comp_endpoint_inr H σ p i) hq

/-- **Degree reduction divides the value by at least `1 + |D|`** [Dinur, Section 3.1][Dinur2005]:
labelling the half-edges by the labels of their vertices violates the edge-links of the violated
edges only, which are a proportion `1 / (1 + |D|)` of the darts at their half-edges. -/
theorem one_add_card_mul_unsatVal_degreeReduce_le [Nonempty α] :
    (1 + Fintype.card D) * (G.degreeReduce H).toConstraintGraph.unsatVal ≤ G.unsatVal := by
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  rw [← hσ]
  refine (mul_le_mul_of_nonneg_left ((G.degreeReduce H).toConstraintGraph.unsatVal_le
    (σ ∘ G.endpoint)) (by positivity)).trans ?_
  have h := card_unsatEdges_degreeReduce_comp_endpoint_le H σ
  rcases (Fintype.card E).eq_zero_or_pos with hE | hE
  · have : IsEmpty E := Fintype.card_eq_zero_iff.1 hE
    simp [unsatFrac]
  rw [unsatFrac, unsatFrac, card_darts_degreeReduce, mul_div_assoc', div_le_div_iff₀
    (by positivity) (by positivity)]
  push_cast
  have h' : (#((G.degreeReduce H).toConstraintGraph.unsatEdges (σ ∘ G.endpoint)) : ℝ) ≤
      2 * #(G.unsatEdges σ) := by exact_mod_cast h
  have hE' : (0 : ℝ) < Fintype.card E := by exact_mod_cast hE
  nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ (1 + Fintype.card D) *
    Fintype.card E)]

/-- **The edge charge**: an edge violated by a labelling `σ` of the vertices either has a
half-edge whose label under `A` differs from that of its vertex, or its edge-links are violated by
`A`. -/
private theorem card_unsatEdges_le_card_filter_isLeft_add [DecidableEq α] (A : E × Bool → α)
    (σ : V → α) :
    #(G.unsatEdges σ) ≤ #{q ∈ (G.degreeReduce H).toConstraintGraph.unsatEdges A | q.2.isLeft} +
      #{p | A p ≠ σ (G.endpoint p)} := by
  classical
  refine (card_le_card fun e he ↦ ?_).trans ((card_union_le _ _).trans
    (add_le_add (card_image_le (f := fun q ↦ q.1.1)) (card_image_le (f := Prod.fst))))
  rw [mem_unsatEdges] at he
  rw [mem_union, mem_image, mem_image]
  by_cases h₀ : A (e, false) = σ (G.src e)
  · by_cases h₁ : A (e, true) = σ (G.dst e)
    · refine Or.inl ⟨((e, false), .inl ()), ?_, rfl⟩
      rw [mem_filter, mem_unsatEdges, satisfies_degreeReduce_inl]
      exact ⟨by rwa [h₀, h₁], rfl⟩
    · exact Or.inr ⟨(e, true), by simpa using h₁, rfl⟩
  · exact Or.inr ⟨(e, false), by simpa using h₀, rfl⟩

end Count

/-! ### Soundness -/

section Soundness

variable [Fintype E] [DecidableEq V] [Fintype D]

/-- **Plurality**: some label is taken by at least as many half-edges of a cloud as any other. -/
private theorem exists_forall_card_filter_le_card_filter [Nonempty α] [DecidableEq α]
    (A : E × Bool → α)
    (v : V) :
    ∃ a : α, ∀ b, #{x : G.Cloud v | A x.1 = b} ≤ #{x : G.Cloud v | A x.1 = a} :=
  Fintype.exists_forall_card_filter_le_card_filter fun x : G.Cloud v ↦ A x.1

variable {μ : ℝ}

omit [Fintype D] in
open Classical in
/-- The disagreeing half-edges are counted cloud by cloud over `univ.image G.endpoint`. -/
private theorem card_filter_ne_endpoint_eq_sum [DecidableEq α] (A : E × Bool → α) (σ : V → α) :
    (#{p | A p ≠ σ (G.endpoint p)} : ℝ) =
      ∑ v ∈ univ.image G.endpoint, (#{x : G.Cloud v | A x.1 ≠ σ v} : ℝ) := by
  rw [card_eq_sum_card_fiberwise (f := G.endpoint) (t := univ.image G.endpoint)
    fun p _ ↦ mem_image_of_mem _ (mem_univ p)]
  push_cast
  refine sum_congr rfl fun v _ ↦ ?_
  norm_cast
  refine (card_bij (fun x _ ↦ x.1) (fun x hx ↦ ?_) (fun x _ y _ h ↦ Subtype.ext h)
    fun p hp ↦ ?_).symm
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [x.2]
    exact ⟨hx, rfl⟩
  · simp only [mem_filter, mem_univ, true_and] at hp
    exact ⟨⟨p, hp.2⟩, by simpa [hp.2] using hp.1, rfl⟩

/-- **The cloud charge**: if the multigraphs on the clouds have spectral expansion at most `μ` and
`σ v` is a most frequent label of the cloud of every vertex `v`, then the cloud-links violated by
`A` number at least `(1 - μ) |D|` times the half-edges whose label differs from that of their
vertex. -/
private theorem mul_card_filter_ne_le_card_filter_isRight [DecidableEq α]
    (hH : ∀ v, (H v).spectralExpansion ≤ μ) (A : E × Bool → α) (σ : V → α)
    (hσ : ∀ v b, #{x : G.Cloud v | A x.1 = b} ≤ #{x : G.Cloud v | A x.1 = σ v}) :
    (1 - μ) * Fintype.card D * #{p | A p ≠ σ (G.endpoint p)} ≤
      #{q ∈ (G.degreeReduce H).toConstraintGraph.unsatEdges A | q.2.isRight} := by
  classical
  set T : Finset V := univ.image G.endpoint
  /- The darts of the multigraph on the cloud of `v` joining differently labelled half-edges, and
  their embedding into the cloud-links. -/
  set Dis : ∀ v, Finset (G.Cloud v × D) := fun v ↦ {r | A r.1.1 ≠ A ((H v).neighbor r.1 r.2).1}
  set f : ∀ v, G.Cloud v × D → (E × Bool) × (Unit ⊕ D) := fun _ r ↦ (r.1.1, .inr r.2)
  have hf (v : V) : Function.Injective (f v) := fun r r' h ↦ by
    simp only [f, Prod.mk.injEq, Sum.inr.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2
  /- In each cloud, the disagreeing darts are many. -/
  have hcloud (v : V) : (1 - μ) * Fintype.card D * #{x : G.Cloud v | A x.1 ≠ σ v} ≤ #(Dis v) := by
    refine le_trans ?_ ((H v).mul_card_filter_ne_le_card_filter_ne_neighbor (fun x ↦ A x.1) (hσ v))
    gcongr
    linarith [hH v]
  /- The disagreeing darts of different clouds give different violated cloud-links. -/
  have hdisj : (T : Set V).PairwiseDisjoint fun v ↦ (Dis v).image (f v) := by
    intro v _ w _ hvw
    refine disjoint_left.2 fun q hq hq' ↦ hvw ?_
    simp only [mem_image] at hq hq'
    obtain ⟨r, -, rfl⟩ := hq
    obtain ⟨r', -, h⟩ := hq'
    exact r.1.2.symm.trans ((congrArg (fun q ↦ G.endpoint q.1) h).symm.trans r'.1.2)
  have hsub : T.biUnion (fun v ↦ (Dis v).image (f v)) ⊆
      {q ∈ (G.degreeReduce H).toConstraintGraph.unsatEdges A | q.2.isRight} := by
    intro q hq
    simp only [mem_biUnion, mem_image] at hq
    obtain ⟨v, -, r, hr, rfl⟩ := hq
    rw [mem_filter, mem_unsatEdges, satisfies_degreeReduce_inr, neighbor_cloudGraph H r.1]
    exact ⟨by simpa [Dis] using hr, rfl⟩
  calc (1 - μ) * Fintype.card D * #{p | A p ≠ σ (G.endpoint p)}
      = ∑ v ∈ T, (1 - μ) * Fintype.card D * #{x : G.Cloud v | A x.1 ≠ σ v} := by
        rw [G.card_filter_ne_endpoint_eq_sum A σ, mul_sum]
    _ ≤ ∑ v ∈ T, (#((Dis v).image (f v)) : ℝ) := by
        refine sum_le_sum fun v _ ↦ ?_
        rw [card_image_of_injective _ (hf v)]
        exact hcloud v
    _ = #(T.biUnion fun v ↦ (Dis v).image (f v)) := by
        rw [card_biUnion hdisj]
        push_cast
        rfl
    _ ≤ _ := by exact_mod_cast card_le_card hsub

/-- **Soundness of degree reduction** [Dinur, Section 3.1][Dinur2005]: if the multigraphs on the
clouds have spectral expansion at most `μ`, every labelling of the half-edges violates a proportion
of the darts at least `min 1 ((1 - μ) |D|) / (2 (1 + |D|))` times the value of `G`, whatever the
alphabet. -/
theorem le_unsatFrac_degreeReduce [Nonempty α] (hH : ∀ v, (H v).spectralExpansion ≤ μ)
    (A : E × Bool → α) :
    min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) * G.unsatVal ≤
      (G.degreeReduce H).toConstraintGraph.unsatFrac A := by
  classical
  choose σ hσ using exists_forall_card_filter_le_card_filter (G := G) A
  set c := (1 - μ) * Fintype.card D
  set U := (G.degreeReduce H).toConstraintGraph.unsatEdges A
  have hcloud := mul_card_filter_ne_le_card_filter_isRight H hH A σ hσ
  have hedge := card_unsatEdges_le_card_filter_isLeft_add H A σ
  have hsplit : #{q ∈ U | q.2.isLeft} + #{q ∈ U | q.2.isRight} = #U := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun q _ h h' ↦ by
      rcases q with ⟨_, _ | _⟩ <;> simp_all), ← filter_or]
    congr 1
    exact filter_true_of_mem fun q _ ↦ by rcases q with ⟨_, _ | _⟩ <;> simp
  /- The number of edges violated by `σ` is at least `|E|` times the value. -/
  have hval : Fintype.card E * G.unsatVal ≤ #(G.unsatEdges σ) := by
    rw [← card_mul_unsatFrac]
    exact mul_le_mul_of_nonneg_left (G.unsatVal_le σ) (Nat.cast_nonneg _)
  /- Trading the two charges off. -/
  have hU : min 1 c * #(G.unsatEdges σ) ≤ #U := by
    have hedge' : (#(G.unsatEdges σ) : ℝ) ≤ #{q ∈ U | q.2.isLeft} +
        #{p | A p ≠ σ (G.endpoint p)} := by exact_mod_cast hedge
    rw [show (#U : ℝ) = #{q ∈ U | q.2.isLeft} + #{q ∈ U | q.2.isRight} by
      exact_mod_cast hsplit.symm]
    rcases le_total 1 c with hc | hc
    · rw [min_eq_left hc]
      nlinarith [Nat.cast_nonneg (α := ℝ) #{q ∈ U | q.2.isLeft}]
    rw [min_eq_right hc]
    rcases le_total c 0 with hc₀ | hc₀
    · exact (mul_nonpos_of_nonpos_of_nonneg hc₀ (Nat.cast_nonneg _)).trans (by positivity)
    · nlinarith [Nat.cast_nonneg (α := ℝ) #{q ∈ U | q.2.isLeft},
        Nat.cast_nonneg (α := ℝ) #{p | A p ≠ σ (G.endpoint p)}]
  have hA := (G.degreeReduce H).card_mul_card_mul_unsatFrac A
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, Fintype.card_unit] at hA
  push_cast at hA
  rcases isEmpty_or_nonempty E with hE | hE
  · rw [G.unsatVal_of_isEmpty, mul_zero]
    exact unsatFrac_nonneg _ _
  have hE' : (0 : ℝ) < Fintype.card E := Nat.cast_pos.2 Fintype.card_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rcases le_total (min 1 c) 0 with hm | hm
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hm G.unsatVal_nonneg,
      unsatFrac_nonneg (G.degreeReduce H).toConstraintGraph A]
  · nlinarith [mul_le_mul_of_nonneg_left hval hm]

/-- **Soundness of degree reduction** [Dinur, Section 3.1][Dinur2005]: if the multigraphs on the
clouds have spectral expansion at most `μ`, degree reduction divides the value by at most
`2 (1 + |D|) / min 1 ((1 - μ) |D|)`, whatever the alphabet. -/
theorem le_unsatVal_degreeReduce [Nonempty α] (hH : ∀ v, (H v).spectralExpansion ≤ μ) :
    min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) * G.unsatVal ≤
      (G.degreeReduce H).toConstraintGraph.unsatVal :=
  (le_unsatVal_iff _).2 (le_unsatFrac_degreeReduce H hH)

end Soundness

/-- **Degree reduction preserves satisfiability** when the multigraphs on the clouds are expanders:
their degree is positive and their spectral expansions are at most some `μ < 1`. -/
theorem satisfiable_degreeReduce_iff [Fintype E] [DecidableEq V] [Fintype D] [Nonempty D]
    [Nonempty α] {μ : ℝ} (hμ : μ < 1) (hH : ∀ v, (H v).spectralExpansion ≤ μ) :
    (G.degreeReduce H).toConstraintGraph.Satisfiable ↔ G.Satisfiable := by
  refine ⟨fun h ↦ ?_, satisfiable_degreeReduce H⟩
  rw [← unsatVal_eq_zero_iff] at h ⊢
  have hc : 0 < min 1 ((1 - μ) * Fintype.card D) / (2 * (1 + Fintype.card D)) := by
    have : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
    have : 0 < 1 - μ := by linarith
    exact div_pos (lt_min one_pos (by positivity)) (by positivity)
  have := le_unsatVal_degreeReduce H hH
  rw [h] at this
  exact le_antisymm (nonpos_of_mul_nonpos_right this hc) G.unsatVal_nonneg

end ConstraintGraph

end Cslib.PCP
