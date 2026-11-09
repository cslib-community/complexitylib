/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Constraint graphs and their unsatisfiability value

A **constraint graph** [Dinur, Section 2.1][Dinur2005] over an alphabet `α` is a multigraph with
finitely many edges, each of which carries a binary constraint on the labels of its two ends. A
labelling `σ : V → α` of the vertices violates the edges whose constraints its labels fail, and the
**unsatisfiability value** `unsatVal` is the least fraction of edges that a labelling violates. It
vanishes exactly on the satisfiable constraint graphs, and Dinur's proof of the PCP theorem
amplifies it: every step of the proof is a transformation of constraint graphs that keeps
satisfiable graphs satisfiable and multiplies the value of unsatisfiable ones by at least a constant
factor.

Vertices and edges are types rather than numbers: the constructions of the proof (degree
reduction, expanderization, powering) produce vertices and edges that are pairs, sums or tuples of
those of their inputs. Edges are indexed, so parallel edges and self-loops are allowed, and
directed, from `src e` to `dst e`, so that a constraint need not be symmetric; an undirected edge is
modelled by its two orientations when the construction needs it. The fractions are taken over the
edges only, so the vertex type need not be finite. A constraint graph without edges has value zero,
as is right: it is satisfied by every labelling.

## Main definitions

* `Cslib.PCP.ConstraintGraph`: a multigraph with a binary constraint on each edge.
* `Cslib.PCP.ConstraintGraph.Satisfies`, `Cslib.PCP.ConstraintGraph.Satisfiable`.
* `Cslib.PCP.ConstraintGraph.unsatEdges`, `Cslib.PCP.ConstraintGraph.unsatFrac`: the edges a
  labelling violates, and their proportion.
* `Cslib.PCP.ConstraintGraph.unsatVal`: the least proportion of violated edges.
* `Cslib.PCP.ConstraintGraph.map`: the vertices renamed, for instance to add isolated vertices.
* `Cslib.PCP.ConstraintGraph.comap`: the edges pulled back along a map, for instance renamed.
* `Cslib.PCP.ConstraintGraph.reindex`: the vertices and the edges renamed along equivalences.
* `Cslib.PCP.ConstraintGraph.union`: two constraint graphs on the same vertices, superposed.

## Main results

* `Cslib.PCP.ConstraintGraph.expect_mem_unsatEdges`: the proportion of violated edges is the
  probability that a uniformly random edge is violated.
* `Cslib.PCP.ConstraintGraph.exists_unsatFrac_eq_unsatVal`: the minimum is attained.
* `Cslib.PCP.ConstraintGraph.unsatVal_eq_zero_iff`: the value vanishes exactly on satisfiable
  constraint graphs.
* `Cslib.PCP.ConstraintGraph.inv_card_le_unsatVal`,
  `Cslib.PCP.ConstraintGraph.one_le_card_mul_unsatVal`: an unsatisfiable constraint graph has value
  at least one edge's worth.
* `Cslib.PCP.ConstraintGraph.unsatVal_map`: renaming the vertices injectively preserves the
  value.
* `Cslib.PCP.ConstraintGraph.satisfiable_comap_iff`,
  `Cslib.PCP.ConstraintGraph.unsatVal_comap_equiv`: pulling back along a surjection preserves
  satisfiability, and along an equivalence the value.
* `Cslib.PCP.ConstraintGraph.satisfiable_comap_map_iff`,
  `Cslib.PCP.ConstraintGraph.unsatVal_comap_map_of_injective`: renaming the vertices injectively
  and pulling back the edges preserves satisfiability and the value.
* `Cslib.PCP.ConstraintGraph.satisfiable_reindex_iff`, `Cslib.PCP.ConstraintGraph.unsatVal_reindex`:
  renaming the vertices and the edges preserves satisfiability and the value.
* `Cslib.PCP.ConstraintGraph.card_mul_unsatVal_add_le`,
  `Cslib.PCP.ConstraintGraph.card_mul_unsatVal_le_union`: adding edges can only increase the number
  of edges violated by the best labelling.
* `Cslib.PCP.ConstraintGraph.unsatVal_union_of_forall_rel`: adding edges whose constraints always
  hold scales the value by the proportion of the original edges.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP

open Finset
open scoped BigOperators

/-- A **constraint graph** [Dinur, Section 2.1][Dinur2005] on the vertices `V`, with edges indexed
by `E`, over the alphabet `α`: each edge `e` goes from `src e` to `dst e` and carries a binary
constraint `rel e` on the labels of its ends. Parallel edges and self-loops are allowed. -/
@[ext]
structure ConstraintGraph (V E α : Type*) where
  /-- The first end of an edge. -/
  src : E → V
  /-- The second end of an edge. -/
  dst : E → V
  /-- The constraint on an edge: a relation between the labels of its first and second ends. -/
  rel : E → α → α → Prop

namespace ConstraintGraph

variable {V E F α : Type*} (G : ConstraintGraph V E α)

/-- The labelling `σ` satisfies the edge `e` when the labels of its ends satisfy its constraint. -/
def Satisfies (σ : V → α) (e : E) : Prop :=
  G.rel e (σ (G.src e)) (σ (G.dst e))

/-- A constraint graph is satisfiable when some labelling satisfies all of its edges. -/
def Satisfiable : Prop :=
  ∃ σ : V → α, ∀ e, G.Satisfies σ e

section Value

variable [Fintype E]

open Classical in
/-- The edges that the labelling `σ` violates. -/
noncomputable def unsatEdges (σ : V → α) : Finset E :=
  {e | ¬ G.Satisfies σ e}

variable {G} in
@[simp]
theorem mem_unsatEdges {σ : V → α} {e : E} : e ∈ G.unsatEdges σ ↔ ¬ G.Satisfies σ e := by
  simp [unsatEdges]

/-- A labelling violates no edge exactly when it satisfies all of them. -/
theorem unsatEdges_eq_empty_iff {σ : V → α} : G.unsatEdges σ = ∅ ↔ ∀ e, G.Satisfies σ e := by
  simp [eq_empty_iff_forall_notMem]

/-- A labelling violates at most all the edges. -/
theorem card_unsatEdges_le (σ : V → α) : #(G.unsatEdges σ) ≤ Fintype.card E :=
  card_le_univ _

/-- The proportion of the edges that the labelling `σ` violates, `UNSAT_σ(G)` in
[Dinur, Section 2.1][Dinur2005]. It is zero when there are no edges. -/
noncomputable def unsatFrac (σ : V → α) : ℝ :=
  #(G.unsatEdges σ) / Fintype.card E

/-- The number of violated edges is the proportion of violated edges times the number of edges. -/
theorem card_mul_unsatFrac (σ : V → α) :
    Fintype.card E * G.unsatFrac σ = #(G.unsatEdges σ) := by
  rcases (Fintype.card E).eq_zero_or_pos with h | h
  · have : IsEmpty E := Fintype.card_eq_zero_iff.1 h
    simp [eq_empty_of_isEmpty (G.unsatEdges σ)]
  · rw [unsatFrac, mul_div_cancel₀ _ (by positivity)]

/-- The proportion of violated edges is nonnegative. -/
theorem unsatFrac_nonneg (σ : V → α) : 0 ≤ G.unsatFrac σ := by
  unfold unsatFrac
  positivity

/-- The proportion of violated edges is at most one. -/
theorem unsatFrac_le_one (σ : V → α) : G.unsatFrac σ ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast G.card_unsatEdges_le σ) (Nat.cast_nonneg _)

/-- A labelling violates no proportion of the edges exactly when it satisfies all of them. -/
theorem unsatFrac_eq_zero_iff {σ : V → α} : G.unsatFrac σ = 0 ↔ ∀ e, G.Satisfies σ e := by
  rw [unsatFrac, div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero, card_eq_zero,
    unsatEdges_eq_empty_iff, or_iff_left_of_imp]
  intro h e
  exact (Fintype.card_eq_zero_iff.1 h).elim e

/-- The proportion of the edges that a labelling violates is the average of the indicator of the
violated edges: the probability that it violates a uniformly random edge. -/
theorem expect_mem_unsatEdges [DecidableEq E] (σ : V → α) :
    𝔼 e, (if e ∈ G.unsatEdges σ then 1 else 0 : ℝ) = G.unsatFrac σ := by
  rw [Fintype.expect_eq_sum_div_card, sum_boole, filter_mem_eq_inter, univ_inter, unsatFrac]

/-- The **unsatisfiability value** `UNSAT(G)` [Dinur, Section 2.1][Dinur2005]: the least
proportion of the edges that a labelling violates. The minimum is attained when `α` is nonempty
(`exists_unsatFrac_eq_unsatVal`); when there is no labelling at all, the value is zero by
convention. -/
noncomputable def unsatVal : ℝ :=
  ⨅ σ : V → α, G.unsatFrac σ

/-- The proportions of violated edges are bounded below, by zero. -/
theorem bddBelow_range_unsatFrac : BddBelow (Set.range G.unsatFrac) :=
  ⟨0, Set.forall_mem_range.2 G.unsatFrac_nonneg⟩

/-- The value is at most the proportion of the edges that any labelling violates. -/
theorem unsatVal_le (σ : V → α) : G.unsatVal ≤ G.unsatFrac σ :=
  ciInf_le G.bddBelow_range_unsatFrac σ

/-- The value is nonnegative. -/
theorem unsatVal_nonneg : 0 ≤ G.unsatVal :=
  Real.iInf_nonneg G.unsatFrac_nonneg

/-- The value is at most one. -/
theorem unsatVal_le_one : G.unsatVal ≤ 1 := by
  rcases isEmpty_or_nonempty (V → α) with h | h
  · rw [unsatVal, Real.iInf_of_isEmpty]
    exact zero_le_one
  · obtain ⟨σ⟩ := h
    exact (G.unsatVal_le σ).trans (G.unsatFrac_le_one σ)

/-- A constraint graph without edges has value zero. -/
theorem unsatVal_of_isEmpty [IsEmpty E] : G.unsatVal = 0 := by
  have h (σ : V → α) : G.unsatFrac σ = 0 := by simp [unsatFrac]
  simp only [unsatVal, h, Real.iInf_const_zero]

/-- The proportion of violated edges takes finitely many values, multiples of `1 / |E|`. -/
theorem finite_range_unsatFrac : (Set.range G.unsatFrac).Finite := by
  refine (Set.finite_range fun k : Fin (Fintype.card E + 1) ↦ (k : ℝ) / Fintype.card E).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨⟨_, Nat.lt_succ_of_le (G.card_unsatEdges_le σ)⟩, rfl⟩

variable [Nonempty α]

/-- **The minimum is attained**: some labelling violates exactly the proportion `unsatVal` of the
edges. -/
theorem exists_unsatFrac_eq_unsatVal : ∃ σ : V → α, G.unsatFrac σ = G.unsatVal :=
  (Set.range_nonempty G.unsatFrac).csInf_mem G.finite_range_unsatFrac

/-- A lower bound on the value is a lower bound on the proportion of the edges violated by every
labelling. -/
theorem le_unsatVal_iff {c : ℝ} : c ≤ G.unsatVal ↔ ∀ σ : V → α, c ≤ G.unsatFrac σ :=
  le_ciInf_iff G.bddBelow_range_unsatFrac

/-- An upper bound on the value is an upper bound on the proportion of the edges violated by some
labelling. -/
theorem unsatVal_le_iff {c : ℝ} : G.unsatVal ≤ c ↔ ∃ σ : V → α, G.unsatFrac σ ≤ c := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, hσ⟩ ↦ (G.unsatVal_le σ).trans hσ⟩
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  exact ⟨σ, hσ.le.trans h⟩

/-- **The value vanishes exactly on satisfiable constraint graphs.** -/
theorem unsatVal_eq_zero_iff : G.unsatVal = 0 ↔ G.Satisfiable := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, hσ⟩ ↦ le_antisymm ?_ G.unsatVal_nonneg⟩
  · obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
    exact ⟨σ, G.unsatFrac_eq_zero_iff.1 (hσ.trans h)⟩
  · exact (G.unsatVal_le σ).trans (G.unsatFrac_eq_zero_iff.2 hσ).le

/-- The value is positive exactly on unsatisfiable constraint graphs. -/
theorem unsatVal_pos_iff : 0 < G.unsatVal ↔ ¬ G.Satisfiable := by
  rw [← unsatVal_eq_zero_iff, G.unsatVal_nonneg.lt_iff_ne']

/-- **An unsatisfiable constraint graph has value at least `1 / |E|`**: every labelling violates at
least one edge. -/
theorem inv_card_le_unsatVal (h : ¬ G.Satisfiable) : (Fintype.card E : ℝ)⁻¹ ≤ G.unsatVal := by
  refine G.le_unsatVal_iff.2 fun σ ↦ ?_
  have hne : (G.unsatEdges σ).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, unsatEdges_eq_empty_iff]
    exact fun hσ ↦ h ⟨σ, hσ⟩
  rw [unsatFrac, inv_eq_one_div]
  gcongr
  exact_mod_cast hne.card_pos

/-- An unsatisfiable constraint graph violates at least one edge at its minimum-value labelling. -/
theorem one_le_card_mul_unsatVal (h : ¬ G.Satisfiable) :
    1 ≤ (Fintype.card E : ℝ) * G.unsatVal := by
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  rw [← hσ, G.card_mul_unsatFrac]
  have hne : (G.unsatEdges σ).Nonempty :=
    nonempty_iff_ne_empty.2 fun he ↦ h ⟨σ, G.unsatEdges_eq_empty_iff.1 he⟩
  exact_mod_cast one_le_card.2 hne

end Value

section Map

variable {W : Type*} (f : V → W)

/-- The constraint graph `G` with its vertices renamed along `f : V → W`: the same edges and
constraints, between the images of their ends. The vertices outside the range of `f` are
isolated. -/
def map : ConstraintGraph W E α where
  src := f ∘ G.src
  dst := f ∘ G.dst
  rel := G.rel

variable {G f} in
/-- A labelling satisfies an edge of `G.map f` when its composite with `f` satisfies it in `G`. -/
@[simp]
theorem satisfies_map {τ : W → α} {e : E} : (G.map f).Satisfies τ e ↔ G.Satisfies (τ ∘ f) e :=
  Iff.rfl

/-- Renaming the vertices injectively preserves satisfiability. -/
theorem satisfiable_map [Nonempty α] {f : V → W} (hf : f.Injective) :
    (G.map f).Satisfiable ↔ G.Satisfiable := by
  refine ⟨fun ⟨τ, hτ⟩ ↦ ⟨τ ∘ f, hτ⟩, fun ⟨σ, hσ⟩ ↦ ⟨Function.extend f σ fun _ ↦
    Classical.arbitrary α, fun e ↦ ?_⟩⟩
  rw [satisfies_map, Function.extend_comp hf]
  exact hσ e

variable [Fintype E]

/-- A labelling violates the edges of `G.map f` that its composite with `f` violates in `G`. -/
theorem unsatEdges_map (τ : W → α) : (G.map f).unsatEdges τ = G.unsatEdges (τ ∘ f) := by
  ext e
  simp

/-- A labelling violates the same proportion of the edges of `G.map f` as its composite with `f`
does of the edges of `G`. -/
theorem unsatFrac_map (τ : W → α) : (G.map f).unsatFrac τ = G.unsatFrac (τ ∘ f) := by
  rw [unsatFrac, unsatFrac, unsatEdges_map]

/-- Renaming the vertices can only increase the value: the labellings of the renamed constraint
graph give labellings of the original one. -/
theorem unsatVal_le_unsatVal_map [Nonempty α] : G.unsatVal ≤ (G.map f).unsatVal :=
  (le_unsatVal_iff _).2 fun τ ↦ (G.unsatFrac_map f τ).symm ▸ G.unsatVal_le _

/-- **Renaming the vertices injectively preserves the value**: for instance, adding isolated
vertices does not change it. -/
theorem unsatVal_map [Nonempty α] {f : V → W} (hf : f.Injective) :
    (G.map f).unsatVal = G.unsatVal := by
  refine le_antisymm ?_ (G.unsatVal_le_unsatVal_map f)
  obtain ⟨σ, hσ⟩ := G.exists_unsatFrac_eq_unsatVal
  rw [← hσ, ← Function.extend_comp hf σ fun _ ↦ Classical.arbitrary α, ← unsatFrac_map]
  exact unsatVal_le _ _

end Map

section Comap

variable {F' : Type*} (g : F → E)

/-- The constraint graph `G` **pulled back** along a map `g : F → E` of edges: its edge `f` is a
copy of the edge `g f` of `G`, with the same ends and the same constraint. Renaming the edges along
an equivalence, repeating them or keeping only some of them are pullbacks. -/
def comap : ConstraintGraph V F α where
  src := G.src ∘ g
  dst := G.dst ∘ g
  rel := G.rel ∘ g

variable {G g} in
/-- A labelling satisfies an edge of `G.comap g` when it satisfies its image in `G`. -/
@[simp]
theorem satisfies_comap {σ : V → α} {f : F} : (G.comap g).Satisfies σ f ↔ G.Satisfies σ (g f) :=
  Iff.rfl

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem comap_id : G.comap id = G :=
  rfl

/-- Pulling back twice is pulling back along the composite. -/
theorem comap_comap (h : F' → F) : (G.comap g).comap h = G.comap (g ∘ h) :=
  rfl

/-- A labelling satisfying `G` satisfies its pullbacks. -/
theorem Satisfiable.comap {G : ConstraintGraph V E α} (h : G.Satisfiable) (g : F → E) :
    (G.comap g).Satisfiable :=
  let ⟨σ, hσ⟩ := h
  ⟨σ, fun f ↦ hσ (g f)⟩

/-- Pulling back along a surjective map of edges preserves satisfiability. -/
theorem satisfiable_comap_iff {g : F → E} (hg : g.Surjective) :
    (G.comap g).Satisfiable ↔ G.Satisfiable := by
  refine ⟨fun ⟨σ, hσ⟩ ↦ ⟨σ, fun e ↦ ?_⟩, fun h ↦ h.comap g⟩
  obtain ⟨f, rfl⟩ := hg e
  exact hσ f

/-- Renaming the vertices injectively and pulling back the edges along a surjection preserves
satisfiability. -/
theorem satisfiable_comap_map_iff [Nonempty α] {W : Type*} {f : V → W} (hf : f.Injective)
    {g : F → E} (hg : g.Surjective) :
    ((G.map f).comap g).Satisfiable ↔ G.Satisfiable :=
  (satisfiable_comap_iff _ hg).trans (G.satisfiable_map hf)

variable [Fintype E] [Fintype F]

/-- A labelling violates the edges of `G.comap g` whose images it violates in `G`. -/
theorem mem_unsatEdges_comap {σ : V → α} {f : F} :
    f ∈ (G.comap g).unsatEdges σ ↔ g f ∈ G.unsatEdges σ := by
  simp

/-- Renaming the edges along an equivalence renames the violated edges. -/
theorem unsatEdges_comap_equiv (e : F ≃ E) (σ : V → α) :
    (G.comap e).unsatEdges σ = (G.unsatEdges σ).map e.symm.toEmbedding := by
  ext f
  simp

/-- Renaming the edges along an equivalence preserves the number of violated edges. -/
theorem card_unsatEdges_comap_equiv (e : F ≃ E) (σ : V → α) :
    #((G.comap e).unsatEdges σ) = #(G.unsatEdges σ) := by
  rw [unsatEdges_comap_equiv, card_map]

/-- Renaming the edges along an equivalence preserves the proportion of violated edges. -/
theorem unsatFrac_comap_equiv (e : F ≃ E) (σ : V → α) :
    (G.comap e).unsatFrac σ = G.unsatFrac σ := by
  rw [unsatFrac, unsatFrac, card_unsatEdges_comap_equiv, Fintype.card_congr e]

/-- **Renaming the edges along an equivalence preserves the value.** -/
theorem unsatVal_comap_equiv (e : F ≃ E) : (G.comap e).unsatVal = G.unsatVal :=
  iInf_congr (G.unsatFrac_comap_equiv e)

/-- **Renaming the vertices injectively and the edges along an equivalence preserves the value.** -/
theorem unsatVal_comap_map_of_injective [Nonempty α] {W : Type*} {f : V → W} (hf : f.Injective)
    (e : F ≃ E) : ((G.map f).comap e).unsatVal = G.unsatVal :=
  (unsatVal_comap_equiv _ e).trans (G.unsatVal_map hf)

end Comap

section Reindex

variable {W : Type*}

/-- The constraint graph `G` with its vertices and its edges renamed along equivalences: for
instance numbered by `Fin` (`Fintype.equivFin`). -/
def reindex (eV : V ≃ W) (eE : E ≃ F) : ConstraintGraph W F α :=
  (G.map eV).comap eE.symm

variable {G} in
/-- A labelling satisfies an edge of the renamed constraint graph when its composite with the
renaming of the vertices satisfies the corresponding edge of `G`. -/
@[simp]
theorem satisfies_reindex {eV : V ≃ W} {eE : E ≃ F} {τ : W → α} {f : F} :
    (G.reindex eV eE).Satisfies τ f ↔ G.Satisfies (τ ∘ eV) (eE.symm f) :=
  Iff.rfl

/-- **Renaming the vertices and the edges preserves satisfiability.** -/
theorem satisfiable_reindex_iff (eV : V ≃ W) (eE : E ≃ F) :
    (G.reindex eV eE).Satisfiable ↔ G.Satisfiable := by
  rw [reindex, satisfiable_comap_iff _ eE.symm.surjective]
  refine ⟨fun ⟨τ, hτ⟩ ↦ ⟨τ ∘ eV, hτ⟩, fun ⟨σ, hσ⟩ ↦ ⟨σ ∘ eV.symm, fun e ↦ ?_⟩⟩
  simpa [Function.comp_def] using hσ e

/-- **Renaming the vertices and the edges preserves the value.** -/
theorem unsatVal_reindex [Fintype E] [Fintype F] (eV : V ≃ W) (eE : E ≃ F) :
    (G.reindex eV eE).unsatVal = G.unsatVal := by
  rw [reindex, unsatVal_comap_equiv, unsatVal, unsatVal]
  simp only [unsatFrac_map]
  exact Function.Surjective.iInf_comp (fun σ ↦ ⟨σ ∘ eV.symm, by simp [Function.comp_def]⟩)
    G.unsatFrac

end Reindex

section Union

variable (H : ConstraintGraph V F α)

/-- The **union** of two constraint graphs on the same vertices: its edges are those of `G`,
labelled by `Sum.inl`, and those of `H`, labelled by `Sum.inr`, with their constraints. -/
def union : ConstraintGraph V (E ⊕ F) α where
  src := Sum.elim G.src H.src
  dst := Sum.elim G.dst H.dst
  rel := Sum.elim G.rel H.rel

variable {G H}

@[simp]
theorem satisfies_union_inl {σ : V → α} {e : E} :
    (G.union H).Satisfies σ (.inl e) ↔ G.Satisfies σ e :=
  Iff.rfl

@[simp]
theorem satisfies_union_inr {σ : V → α} {f : F} :
    (G.union H).Satisfies σ (.inr f) ↔ H.Satisfies σ f :=
  Iff.rfl

variable (G H)

/-- The union is satisfied by the labellings that satisfy both constraint graphs. -/
theorem satisfiable_union_iff :
    (G.union H).Satisfiable ↔ ∃ σ : V → α, (∀ e, G.Satisfies σ e) ∧ ∀ f, H.Satisfies σ f := by
  simp [Satisfiable, Sum.forall]

variable [Fintype E] [Fintype F]

/-- A labelling violates the edges of the union that it violates in either constraint graph. -/
theorem card_unsatEdges_union (σ : V → α) :
    #((G.union H).unsatEdges σ) = #(G.unsatEdges σ) + #(H.unsatEdges σ) := by
  rw [← card_disjSum]
  congr 1
  ext (e | f) <;> simp

/-- The proportion of the edges of the union that a labelling violates is the average of those in
the two constraint graphs, weighted by their numbers of edges. -/
theorem card_add_card_mul_unsatFrac_union (σ : V → α) :
    (Fintype.card E + Fintype.card F) * (G.union H).unsatFrac σ =
      Fintype.card E * G.unsatFrac σ + Fintype.card F * H.unsatFrac σ := by
  rw [card_mul_unsatFrac, card_mul_unsatFrac, ← Nat.cast_add, ← Nat.cast_add, ← Fintype.card_sum,
    card_mul_unsatFrac, card_unsatEdges_union]

/-- **The value of a union**: the best labelling of the union violates at least as many edges as
the best labellings of the two constraint graphs together. -/
theorem card_mul_unsatVal_add_le [Nonempty α] :
    Fintype.card E * G.unsatVal + Fintype.card F * H.unsatVal ≤
      (Fintype.card E + Fintype.card F) * (G.union H).unsatVal := by
  obtain ⟨σ, hσ⟩ := (G.union H).exists_unsatFrac_eq_unsatVal
  rw [← hσ, card_add_card_mul_unsatFrac_union]
  gcongr <;> apply unsatVal_le

/-- **Adding edges** to a constraint graph can only increase the number of edges violated by the
best labelling. -/
theorem card_mul_unsatVal_le_union [Nonempty α] :
    Fintype.card E * G.unsatVal ≤ (Fintype.card E + Fintype.card F) * (G.union H).unsatVal :=
  (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) H.unsatVal_nonneg)).trans
    (G.card_mul_unsatVal_add_le H)

/-- Adding edges whose constraints always hold scales the proportion of violated edges by the
proportion of the original edges. -/
theorem unsatFrac_union_of_forall_rel (hH : ∀ f a b, H.rel f a b) (σ : V → α) :
    (G.union H).unsatFrac σ =
      Fintype.card E / (Fintype.card E + Fintype.card F) * G.unsatFrac σ := by
  have h := G.card_add_card_mul_unsatFrac_union H σ
  rw [(H.unsatFrac_eq_zero_iff).2 fun f ↦ hH f _ _, mul_zero, add_zero] at h
  rcases (Fintype.card (E ⊕ F)).eq_zero_or_pos with h0 | h0
  · rw [Fintype.card_sum, Nat.add_eq_zero_iff] at h0
    simp [unsatFrac, Fintype.card_sum, h0.1, h0.2]
  · rw [Fintype.card_sum] at h0
    have h0' : (0 : ℝ) < Fintype.card E + Fintype.card F := by exact_mod_cast h0
    rw [div_mul_eq_mul_div, eq_div_iff h0'.ne', mul_comm, h]

/-- **Adding edges whose constraints always hold** scales the value by the proportion of the
original edges. -/
theorem unsatVal_union_of_forall_rel (hH : ∀ f a b, H.rel f a b) :
    (G.union H).unsatVal = Fintype.card E / (Fintype.card E + Fintype.card F) * G.unsatVal := by
  rw [unsatVal, unsatVal, Real.mul_iInf_of_nonneg (by positivity)]
  exact iInf_congr (G.unsatFrac_union_of_forall_rel H hH)

end Union

end ConstraintGraph

end Cslib.PCP
