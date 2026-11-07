/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Basic
public import Mathlib.ModelTheory.Graph
public import Mathlib.ModelTheory.PartialEquiv
public import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.FinitelyGenerated
import Mathlib.Tactic.FinCases

/-!
# Extension axioms and the theory of the random graph

The `k`-variable **extension axiom** with adjacency pattern `s : Fin k → Bool` says that for all
pairwise distinct `x₀, …, x_{k-1}` there is a vertex `z`, distinct from every `xᵢ`, adjacent to
`xᵢ` exactly when `s i = true`. The **theory of the random graph** consists of the axioms of
simple graphs and all extension axioms [Fagin1976] [Libkin2004, Section 12.2].

Its models are infinite, and between any two of them the finite partial isomorphisms have the
back-and-forth property: a finite partial isomorphism extends to any new element of the domain by
choosing a witness of the extension axiom given by the adjacency pattern of the new element.
Two countable models are therefore isomorphic
(`Cslib.Logic.FO.graph.aleph0_categorical_randomGraphTheory`).
Completeness of the theory, which also needs its satisfiability, is in
`Complexity.Logics.FirstOrder.ZeroOneLaw`.

## Main definitions

* `Cslib.Logic.FO.graph.IsExtensionWitness`: a witness of the extension of a tuple by a pattern.
* `Cslib.Logic.FO.graph.HasExtension`: the extension property for a fixed pattern.
* `Cslib.Logic.FO.graph.extensionAxiom`: the extension axiom as a first-order sentence.
* `Cslib.Logic.FO.graph.extensionAxioms`: the set of all extension axioms.
* `Cslib.Logic.FO.graph.randomGraphTheory`: the simple-graph axioms together with all extension
  axioms.
* `Cslib.Logic.FO.graph.Satisfies`: satisfaction of a sentence of the graph language by a simple
  graph.

## Main results

* `Cslib.Logic.FO.graph.realize_extensionAxiom`: an extension axiom holds exactly when the
  extension property does.
* `Cslib.Logic.FO.graph.satisfies_extensionAxiom_iff`: the same statement for simple graphs.
* `Cslib.Logic.FO.graph.model_randomGraphTheory_iff`: models of the theory are simple graphs with
  all extension properties.
* `Cslib.Logic.FO.graph.infinite_of_model_randomGraphTheory`: such models are infinite.
* `Cslib.Logic.FO.graph.isExtensionPair_of_hasExtension`: the forth step of the back-and-forth
  argument.
* `Cslib.Logic.FO.graph.aleph0_categorical_randomGraphTheory`: the theory is `ℵ₀`-categorical.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Sections 12.2 and 12.3.
-/

public section

open FirstOrder Language Structure BoundedFormula Cardinal

namespace Cslib.Logic.FO.graph

/-- The graph language has no nullary relation symbols. Mathlib has the analogous instance for
`Language.order` in `Mathlib/ModelTheory/Order.lean` but not this one, so this instance is an
upstream candidate for `Mathlib/ModelTheory/Graph.lean`. -/
instance isEmpty_relations_zero : IsEmpty (Language.graph.Relations 0) :=
  ⟨fun r => nomatch r⟩

variable {M : Type*} [Language.graph.Structure M]

/-- `z` witnesses the extension of the tuple `x` by the adjacency pattern `s`: it differs from
every `x i` and is adjacent to `x i` exactly when `s i = true`. -/
@[expose]
def IsExtensionWitness {k : ℕ} (x : Fin k → M) (s : Fin k → Bool) (z : M) : Prop :=
  (∀ i, z ≠ x i) ∧ ∀ i, (RelMap adj ![z, x i] ↔ s i = true)

/-- The extension property for the pattern `s : Fin k → Bool`: every tuple of `k` distinct
elements has a witness of the extension by `s`. -/
@[expose]
def HasExtension (M : Type*) [Language.graph.Structure M] (k : ℕ) (s : Fin k → Bool) : Prop :=
  ∀ x : Fin k → M, Function.Injective x → ∃ z, IsExtensionWitness x s z

/-- The matrix of the extension axiom: if the free variables are distinct, then some vertex
witnesses the extension by `s`. -/
private noncomputable def extensionBody {k : ℕ} (s : Fin k → Bool) :
    Language.graph.Formula (Fin k) :=
  (Formula.iInf fun p : {p : Fin k × Fin k // p.1 ≠ p.2} => ∼(varEq p.1.1 p.1.2)) ⟹
    Formula.iExs (Fin 1)
      (Formula.iInf fun i : Fin k =>
        ∼(varEq (Sum.inr 0) (Sum.inl i)) ⊓
          (if s i then rel₂ adj (Sum.inr 0) (Sum.inl i)
            else ∼(rel₂ adj (Sum.inr 0) (Sum.inl i))))

/-- The **extension axiom** for the pattern `s : Fin k → Bool`, as a sentence of the graph
language [Fagin1976] [Libkin2004, Section 12.2]. -/
noncomputable def extensionAxiom (k : ℕ) (s : Fin k → Bool) : Language.graph.Sentence :=
  closeAll (Fin k) (extensionBody s)

/-- An extension axiom holds exactly when the corresponding extension property does. -/
theorem realize_extensionAxiom {k : ℕ} (s : Fin k → Bool) :
    M ⊨ extensionAxiom k s ↔ HasExtension M k s := by
  rw [extensionAxiom, realize_closeAll]
  refine forall_congr' fun x => ?_
  simp only [extensionBody, Formula.realize_imp, Formula.realize_iInf, Formula.realize_not,
    realize_varEq, Formula.realize_iExs, Formula.realize_inf]
  constructor
  · intro h hx
    obtain ⟨z, hz⟩ := h fun p hp => p.2 (hx hp)
    refine ⟨z 0, fun i => (hz i).1, fun i => ?_⟩
    have := (hz i).2
    cases hs : s i <;> simp only [hs, Bool.false_eq_true, iff_false, ↓reduceIte,
      Formula.realize_not, realize_rel₂, iff_true] at this ⊢ <;> exact this
  · intro h hx
    obtain ⟨z, hz⟩ := h fun i j hij => by
      by_contra hne
      exact hx ⟨(i, j), hne⟩ hij
    refine ⟨fun _ => z, fun i => ⟨hz.1 i, ?_⟩⟩
    have := hz.2 i
    cases hs : s i <;> simp only [hs, Bool.false_eq_true, iff_false, ↓reduceIte,
      Formula.realize_not, realize_rel₂, iff_true] at this ⊢ <;> exact this

/-- The set of all extension axioms. -/
noncomputable def extensionAxioms : Language.graph.Theory :=
  Set.range fun p : (k : ℕ) × (Fin k → Bool) => extensionAxiom p.1 p.2

/-- The **theory of the random graph**: the axioms of simple graphs together with all extension
axioms [Fagin1976] [Libkin2004, Section 12.2]. Its countable model is the Rado graph. -/
noncomputable def randomGraphTheory : Language.graph.Theory :=
  Theory.simpleGraph ∪ extensionAxioms

/-- The sentences of the theory of the random graph are the simple-graph axioms and the extension
axioms. -/
theorem mem_randomGraphTheory {φ : Language.graph.Sentence} :
    φ ∈ randomGraphTheory ↔ φ ∈ Theory.simpleGraph ∨ ∃ k s, extensionAxiom k s = φ := by
  simp only [randomGraphTheory, extensionAxioms, Set.mem_union, Set.mem_range, Sigma.exists]

/-- A structure models all extension axioms exactly when it has every extension property. -/
theorem model_extensionAxioms_iff : M ⊨ extensionAxioms ↔ ∀ k s, HasExtension M k s := by
  simp only [extensionAxioms, Theory.model_iff, Set.mem_range, forall_exists_index, Sigma.forall]
  refine ⟨fun h k s => (realize_extensionAxiom s).1 (h _ k s rfl), ?_⟩
  rintro h _ k s rfl
  exact (realize_extensionAxiom s).2 (h k s)

/-- The models of the theory of the random graph are the simple graphs with every extension
property. -/
theorem model_randomGraphTheory_iff :
    M ⊨ randomGraphTheory ↔ M ⊨ Theory.simpleGraph ∧ ∀ k s, HasExtension M k s := by
  rw [randomGraphTheory, Theory.model_union_iff, model_extensionAxioms_iff]

/-- A structure with every extension property is infinite: in a finite structure, the tuple
listing all elements has no witness. -/
theorem infinite_of_hasExtension (h : ∀ k s, HasExtension M k s) : Infinite M := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite M
  let e := (Fintype.equivFin M).symm
  obtain ⟨z, hz, -⟩ := h _ (fun _ => false) e e.injective
  exact hz (e.symm z) (e.apply_symm_apply z).symm

/-- Models of the theory of the random graph are infinite. -/
theorem infinite_of_model_randomGraphTheory [M ⊨ randomGraphTheory] : Infinite M :=
  infinite_of_hasExtension (model_randomGraphTheory_iff.1 ‹_›).2

private theorem relMap_adj_irrefl [M ⊨ Theory.simpleGraph] (a : M) : ¬RelMap adj ![a, a] :=
  (Theory.simpleGraph_model_iff.1 ‹_›).1.irrefl a

private theorem relMap_adj_symm [M ⊨ Theory.simpleGraph] {a b : M} (h : RelMap adj ![a, b]) :
    RelMap adj ![b, a] :=
  (Theory.simpleGraph_model_iff.1 ‹_›).2.symm a b h

/-- An injective map preserving and reflecting adjacency is an embedding. -/
private def embeddingOfAdj {N : Type*} [Language.graph.Structure N] (f : M → N)
    (hf : Function.Injective f) (hadj : ∀ a b, RelMap adj ![f a, f b] ↔ RelMap adj ![a, b]) :
    M ↪[Language.graph] N where
  toFun := f
  inj' := hf
  map_fun' := fun g => isEmptyElim g
  map_rel' := fun {n} r x => by
    match n, r with
    | 2, .adj =>
      have hx : x = ![x 0, x 1] := by
        funext i; fin_cases i <;> rfl
      have hfx : f ∘ x = ![f (x 0), f (x 1)] := by
        funext i; fin_cases i <;> rfl
      rw [hfx, hx]
      exact hadj (x 0) (x 1)

private theorem substructure_relMap_adj {S : Language.graph.Substructure M} (a b : S) :
    RelMap adj ![a, b] ↔ RelMap adj ![(a : M), (b : M)] := by
  change RelMap adj (Subtype.val ∘ ![a, b]) ↔ _
  refine iff_of_eq (congrArg _ ?_)
  funext i; fin_cases i <;> rfl

private theorem embedding_relMap_adj {N P : Type*} [Language.graph.Structure N]
    [Language.graph.Structure P] (f : P ↪[Language.graph] N) (a b : P) :
    RelMap adj ![f a, f b] ↔ RelMap adj ![a, b] := by
  rw [← f.map_rel adj ![a, b] ]
  refine iff_of_eq (congrArg _ ?_)
  funext i; fin_cases i <;> rfl

/-- **Forth step.** If `N` is a simple graph with every extension property, then every embedding
of a finitely generated (that is, finite) substructure of a simple graph `M` into `N` extends to
any further element of `M`. -/
theorem isExtensionPair_of_hasExtension {N : Type*} [Language.graph.Structure N]
    [M ⊨ Theory.simpleGraph] [N ⊨ Theory.simpleGraph] (hN : ∀ k s, HasExtension N k s) :
    Language.graph.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  have hU : ∀ u : M, u ∈ (Substructure.closure Language.graph {m} ⊔ S) ↔ u = m ∨ u ∈ S := by
    intro u
    rw [← Substructure.closure_eq S, ← Substructure.closure_union,
      Substructure.mem_closure_iff_of_isRelational, Substructure.closure_eq]
    simp only [Set.mem_union, Set.mem_singleton_iff, SetLike.mem_coe]
  have : Finite S := Substructure.fg_iff_finite.1 S_fg
  have := Fintype.ofFinite S
  -- Enumerate the finite domain `S` and ask for a witness of the adjacency pattern of `m`.
  let e := (Fintype.equivFin S).symm
  let x : Fin (Fintype.card S) → N := fun i => f (e i)
  have hx : Function.Injective x := f.injective.comp e.injective
  let s : Fin (Fintype.card S) → Bool := fun i => decide (RelMap adj ![m, ((e i : S) : M)])
  obtain ⟨z, hzne, hzadj⟩ := hN _ s x hx
  have hzf : ∀ a : S, f a ≠ z := fun a h => hzne (e.symm a) (by simp [x, ← h])
  have hzadj' : ∀ a : S, RelMap adj ![z, f a] ↔ RelMap adj ![m, (a : M)] := by
    intro a
    have := hzadj (e.symm a)
    simpa [x, s] using this
  -- Send `m` to `z` and every element of `S` to its image under `f`.
  let g : (Substructure.closure Language.graph {m} ⊔ S : Language.graph.Substructure M) → N :=
    fun u => if h : (u : M) ∈ S then f ⟨u, h⟩ else z
  have hg_of_mem : ∀ u : (Substructure.closure Language.graph {m} ⊔ S :
      Language.graph.Substructure M), ∀ h : (u : M) ∈ S, g u = f ⟨u, h⟩ :=
    fun u h => dite_eq_left h
  have hg_of_not_mem : ∀ u : (Substructure.closure Language.graph {m} ⊔ S :
      Language.graph.Substructure M), (u : M) ∉ S → g u = z := fun u h => dite_eq_right h
  have hm_of_not_mem : ∀ u : (Substructure.closure Language.graph {m} ⊔ S :
      Language.graph.Substructure M), (u : M) ∉ S → (u : M) = m := fun u h =>
    ((hU u).1 u.2).resolve_right h
  refine ⟨embeddingOfAdj g ?_ ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    by_cases hu : (u : M) ∈ S <;> by_cases hv : (v : M) ∈ S
    · rw [hg_of_mem u hu, hg_of_mem v hv] at huv
      exact Subtype.mk.inj (f.injective huv)
    · rw [hg_of_mem u hu, hg_of_not_mem v hv] at huv
      exact absurd huv (hzf _)
    · rw [hg_of_not_mem u hu, hg_of_mem v hv] at huv
      exact absurd huv.symm (hzf _)
    · rw [hm_of_not_mem u hu, hm_of_not_mem v hv]
  · intro u v
    rw [substructure_relMap_adj]
    by_cases hu : (u : M) ∈ S <;> by_cases hv : (v : M) ∈ S
    · rw [hg_of_mem u hu, hg_of_mem v hv, embedding_relMap_adj, substructure_relMap_adj]
    · rw [hg_of_mem u hu, hg_of_not_mem v hv, hm_of_not_mem v hv]
      exact ⟨fun h => relMap_adj_symm ((hzadj' _).1 (relMap_adj_symm h)),
        fun h => relMap_adj_symm ((hzadj' ⟨u, hu⟩).2 (relMap_adj_symm h))⟩
    · rw [hg_of_not_mem u hu, hg_of_mem v hv, hm_of_not_mem u hu]
      exact hzadj' _
    · rw [hg_of_not_mem u hu, hg_of_not_mem v hv, hm_of_not_mem u hu, hm_of_not_mem v hv]
      exact iff_of_false (relMap_adj_irrefl z) (relMap_adj_irrefl m)
  · ext a
    simp only [Embedding.comp_apply, Substructure.coe_inclusion]
    change f a = g _
    rw [hg_of_mem _ a.2]

/-- The theory of the random graph is `ℵ₀`-categorical: any two countable models are isomorphic,
by a back-and-forth argument [Libkin2004, Chapter 12]. -/
theorem aleph0_categorical_randomGraphTheory : (ℵ₀).Categorical randomGraphTheory := by
  intro M N hM hN
  have : Countable M := Cardinal.mk_le_aleph0_iff.1 hM.le
  have : Countable N := Cardinal.mk_le_aleph0_iff.1 hN.le
  obtain ⟨hMg, hMe⟩ := model_randomGraphTheory_iff.1 M.is_model
  obtain ⟨hNg, hNe⟩ := model_randomGraphTheory_iff.1 N.is_model
  obtain ⟨f, -⟩ := equiv_between_cg cg_of_countable cg_of_countable default
    (isExtensionPair_of_hasExtension hNe) (isExtensionPair_of_hasExtension hMe)
  exact ⟨f⟩

/-! ### Simple graphs -/

/-- A simple graph `G` satisfies a sentence `φ` of the graph language when `φ` holds in the
structure `G.structure` (Mathlib's interpretation of adjacency by `G.Adj`). -/
@[expose]
def Satisfies {V : Type*} (G : SimpleGraph V) (φ : Language.graph.Sentence) : Prop :=
  @Sentence.Realize _ V G.structure φ

/-- A simple graph satisfies the negation of a sentence exactly when it does not satisfy the
sentence. -/
@[simp]
theorem satisfies_not {V : Type*} (G : SimpleGraph V) (φ : Language.graph.Sentence) :
    Satisfies G φ.not ↔ ¬Satisfies G φ := by
  let := G.structure
  exact Sentence.realize_not V

/-- Every simple graph satisfies the axioms of simple graphs. -/
theorem satisfies_of_mem_simpleGraph {V : Type*} (G : SimpleGraph V)
    {φ : Language.graph.Sentence} (h : φ ∈ Theory.simpleGraph) : Satisfies G φ := by
  let := G.structure
  exact Theory.realize_sentence_of_mem Theory.simpleGraph h

/-- A simple graph satisfies the extension axiom for `s` exactly when every tuple of `k` distinct
vertices has a vertex outside it adjacent to `x i` exactly when `s i = true`. -/
theorem satisfies_extensionAxiom_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) (s : Fin k → Bool) :
    Satisfies G (extensionAxiom k s) ↔
      ∀ x : Fin k → V, Function.Injective x →
        ∃ z, (∀ i, z ≠ x i) ∧ ∀ i, (G.Adj z (x i) ↔ s i = true) := by
  let := G.structure
  exact realize_extensionAxiom s

end Cslib.Logic.FO.graph
