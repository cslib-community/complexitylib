/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Sort

/-!
# Bipartiteness and acyclicity are not first-order definable

A finite simple graph `G` on `V` is a structure in Mathlib's language of graphs
`FirstOrder.Language.graph` through `SimpleGraph.structure`. No first-order sentence of this
language holds in exactly the bipartite (2-colorable) finite graphs
(`not_exists_sentence_isBipartite`), nor in exactly the acyclic ones
(`not_exists_sentence_isAcyclic`), even when only graphs with at least `t` vertices are considered.

Both proofs follow the reduction used for connectivity
(`Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity`), packaged here once for all graph
properties. A formula `δ` with two free variables defines a graph in every structure
(`definedGraph`): distinct elements are adjacent when `δ` holds of them in some order. This graph
is the one interpreted by the one-dimensional first-order interpretation `graphInterp δ`
(`graphInterpEquiv`), so a graph sentence pulls back to a sentence of the original language
(`realize_onSentence_graphInterp`). Isomorphic structures define isomorphic graphs
(`definedGraphIso`). **Parity transfer** (`not_exists_sentence_of_even`): if, in every large enough
finite linear order, the graph defined by `δ` has a property exactly when the order has an even
number of elements, then the property is not first-order definable on finite graphs, because a
defining sentence would pull back to a sentence of the language of orders expressing EVEN, which
the Ehrenfeucht–Fraïssé theorem for finite linear orders rules out
(`FiniteLinearOrder.realize_iff_of_two_pow_le_card`).

The two order-definable graphs, on a linear order `0 < 1 < ⋯ < m - 1`:
* `cycleArcFormula`: each element is joined to its successor and `m - 1` to `0`. For `m ≥ 2` this
  is the cycle on `m` vertices, bipartite iff `m` is even
  (`definedGraph_cycleArcFormula_isBipartite_fin`).
* `stepTwoTopBotArcFormula`: each element is joined to the element two steps above it and `m - 1`
  to `0`. For even `m` this is a single path `m - 2, …, 2, 0, m - 1, m - 3, …, 1`; for odd `m ≥ 5`
  the even positions `0, 2, …, m - 1` form a cycle. For `m ≥ 4` it is acyclic iff `m` is even
  (`definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin`). The bound `4` is needed: for `m = 3` the
  graph has the single edge `0 — 2` and is acyclic.

The graph properties are those of Mathlib, `SimpleGraph.IsBipartite` (`Colorable 2`) and
`SimpleGraph.IsAcyclic`, and the sentences range over the pure graph vocabulary, with no built-in
order or arithmetic.

## Main definitions

* `Cslib.Logic.FO.GraphProperties.definedGraph`: the graph defined by a formula with two free
  variables.
* `Cslib.Logic.FO.GraphProperties.graphInterp`: the first-order interpretation of the language of
  graphs that interprets it.

## Main results

* `Cslib.Logic.FO.GraphProperties.realize_onSentence_graphInterp`: pulling back graph sentences.
* `Cslib.Logic.FO.GraphProperties.not_exists_sentence_of_even`: parity transfer.
* `Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite`: bipartiteness is not
  first-order definable on finite graphs.
* `Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic`: acyclicity is not first-order
  definable on finite graphs.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3 (nondefinability of graph
  properties by reduction from EVEN on linear orders).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.GraphProperties

open Connectivity

universe u

/-! ### Graphs defined by a formula -/

section Defined

variable {L : Language} {M : Type*} [L.Structure M]

variable (M) in
/-- The graph defined in an `L`-structure by a formula `δ` with two free variables: distinct
elements are adjacent when `δ` holds of them in some order. -/
def definedGraph (δ : L.Formula (Fin 2)) : SimpleGraph M :=
  SimpleGraph.fromRel fun x y => δ.Realize ![x, y]

/-- Adjacency in `definedGraph`. -/
theorem definedGraph_adj {δ : L.Formula (Fin 2)} {x y : M} :
    (definedGraph M δ).Adj x y ↔ x ≠ y ∧ (δ.Realize ![x, y] ∨ δ.Realize ![y, x]) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The formula with free variables `Fin 2 × Unit` defining adjacency in `definedGraph`. -/
noncomputable def definedAdjFormula (δ : L.Formula (Fin 2)) : L.Formula (Fin 2 × Unit) :=
  ∼(Term.equal (Term.var (0, ())) (Term.var (1, ()))) ⊓
    (δ.relabel (fun i => (i, ())) ⊔ δ.relabel (fun i => (Fin.rev i, ())))

/-- `definedAdjFormula δ` defines adjacency in `definedGraph`. -/
theorem realize_definedAdjFormula (δ : L.Formula (Fin 2)) (v : Fin 2 × Unit → M) :
    (definedAdjFormula δ).Realize v ↔ (definedGraph M δ).Adj (v (0, ())) (v (1, ())) := by
  have h₁ : (v ∘ fun i : Fin 2 => (i, ())) = ![v (0, ()), v (1, ())] := by
    funext i; fin_cases i <;> rfl
  have h₂ : (v ∘ fun i : Fin 2 => (Fin.rev i, ())) = ![v (1, ()), v (0, ())] := by
    funext i; fin_cases i <;> rfl
  simp only [definedAdjFormula, Formula.realize_inf, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, Formula.realize_sup, Formula.realize_relabel, h₁, h₂, definedGraph_adj]

/-- The one-dimensional interpretation of the language of graphs in `L` defined by `δ`. -/
noncomputable def graphInterp (δ : L.Formula (Fin 2)) :
    Interpretation L Language.graph Unit where
  domain := ⊤
  rel := fun {n} R => match n, R with
    | 2, .adj => definedAdjFormula δ

variable (M) in
/-- The graph interpreted by `graphInterp δ` is `definedGraph M δ`. -/
noncomputable def graphInterpEquiv (δ : L.Formula (Fin 2)) :
    letI := (definedGraph M δ).structure
    (graphInterp δ).Model M ≃[Language.graph] M :=
  letI := (definedGraph M δ).structure
  { toFun x := x.1 ()
    invFun y := Interpretation.Model.mk (fun _ => y) (Formula.realize_top.2 trivial)
    left_inv _ := Interpretation.Model.ext rfl
    right_inv _ := rfl
    map_fun' f := isEmptyElim f
    map_rel' {n} R x := by
      match n, R with
      | 2, .adj => exact (realize_definedAdjFormula δ (fun p => (x p.1).1 p.2)).symm }

variable (M) in
/-- An `L`-structure satisfies the pullback along `graphInterp δ` of a graph sentence exactly when
the graph defined by `δ` satisfies it. -/
theorem realize_onSentence_graphInterp (δ : L.Formula (Fin 2)) (φ : Language.graph.Sentence) :
    M ⊨ (graphInterp δ).onSentence φ ↔ (letI := (definedGraph M δ).structure; M ⊨ φ) := by
  let := (definedGraph M δ).structure
  rw [Interpretation.realize_onSentence]
  exact StrongHomClass.realize_sentence (graphInterpEquiv M δ) φ

/-- An isomorphism of `L`-structures is an isomorphism of the graphs defined by `δ`. -/
def definedGraphIso {N : Type*} [L.Structure N] {F : Type*} [EquivLike F M N]
    [L.StrongHomClass F M N] (e : F) (δ : L.Formula (Fin 2)) :
    definedGraph M δ ≃g definedGraph N δ where
  toEquiv := EquivLike.toEquiv e
  map_rel_iff' {x y} := by
    have h : ∀ a b : M, (e ∘ ![a, b]) = ![e a, e b] := fun a b => by
      funext i; fin_cases i <;> rfl
    simp only [definedGraph_adj, EquivLike.coe_coe, ne_eq, EmbeddingLike.apply_eq_iff_eq, ← h,
      StrongHomClass.realize_formula]

end Defined

/-! ### Transfer from parity of finite linear orders -/

/-- **Parity transfer.** Let `δ` define, in every finite linear order, a graph that has the property
`P` exactly when the order has an even number of elements, once it has at least `t₀` elements.
Then no sentence of the language of graphs defines `P` among the finite simple graphs with at least
`t` vertices. -/
theorem not_exists_sentence_of_even (P : ∀ V : Type u, SimpleGraph V → Prop)
    (δ : Language.order.Formula (Fin 2)) (t₀ : ℕ)
    (hP : ∀ (M : Type u) [LinearOrder M] [Finite M] [Language.order.Structure M]
      [Language.order.OrderedStructure M], t₀ ≤ Nat.card M →
      (P M (definedGraph M δ) ↔ Even (Nat.card M)))
    (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ P V G) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨n, hn, htn⟩ : ∃ n, quantifierRank ((graphInterp δ).onSentence φ) ≤ n ∧ max t t₀ ≤ n :=
    ⟨max (quantifierRank ((graphInterp δ).onSentence φ)) (max t t₀), le_max_left _ _,
      le_max_right _ _⟩
  have ht : max t t₀ ≤ 2 ^ n := htn.trans Nat.lt_two_pow_self.le
  have key : ∀ (M : Type u) [LinearOrder M] [Finite M] [Language.order.Structure M]
      [Language.order.OrderedStructure M], max t t₀ ≤ Nat.card M →
      (M ⊨ (graphInterp δ).onSentence φ ↔ Even (Nat.card M)) := by
    intro M _ _ _ _ hM
    rw [realize_onSentence_graphInterp, hφ _ _ (le_of_max_le_left hM),
      hP M (le_of_max_le_right hM)]
  let := orderStructure (ULift.{u} (Fin (2 ^ n)))
  let := orderStructure (ULift.{u} (Fin (2 ^ n + 1)))
  have : Language.order.OrderedStructure (ULift.{u} (Fin (2 ^ n))) := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure (ULift.{u} (Fin (2 ^ n + 1))) := ⟨fun _ => Iff.rfl⟩
  have h := FiniteLinearOrder.realize_iff_of_two_pow_le_card (M := ULift.{u} (Fin (2 ^ n)))
    (N := ULift.{u} (Fin (2 ^ n + 1))) (by rw [Nat.card_ulift, Nat.card_fin]; omega)
    (by rw [Nat.card_ulift, Nat.card_fin]; omega) hn
  rw [key _ (by rw [Nat.card_ulift, Nat.card_fin]; omega),
    key _ (by rw [Nat.card_ulift, Nat.card_fin]; omega), Nat.card_ulift, Nat.card_ulift,
    Nat.card_fin, Nat.card_fin, Nat.even_add_one] at h
  exact iff_not_self h

/-- A finite linear order `M` and `Fin (Nat.card M)` define isomorphic graphs. -/
noncomputable def definedGraphIsoFin (δ : Language.order.Formula (Fin 2)) (M : Type*)
    [LinearOrder M] [Finite M] [Language.order.Structure M] [Language.order.OrderedStructure M]
    [Language.order.Structure (Fin (Nat.card M))]
    [Language.order.OrderedStructure (Fin (Nat.card M))] :
    definedGraph M δ ≃g definedGraph (Fin (Nat.card M)) δ :=
  have := Fintype.ofFinite M
  definedGraphIso (Fintype.orderIsoFinOfCardEq M Nat.card_eq_fintype_card.symm).symm δ

/-! ### Order formulas on `Fin m` -/

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- `covByFormula` on `Fin m`, in terms of values. -/
theorem realize_covByFormula_fin (v : Fin 2 → Fin m) (i j : Fin 2) :
    (covByFormula i j).Realize v ↔ (v i : ℕ) + 1 = v j := by
  rw [realize_covByFormula, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]

/-- `isTopFormula` on `Fin m`, in terms of values. -/
theorem realize_isTopFormula_fin (v : Fin 2 → Fin m) (i : Fin 2) :
    (isTopFormula i).Realize v ↔ (v i : ℕ) + 1 = m := by
  have := (v i).2
  rw [realize_isTopFormula]
  constructor
  · intro h
    have := h ⟨m - 1, by omega⟩
    rw [Fin.le_def] at this
    simp only at this
    omega
  · intro h t
    rw [Fin.le_def]
    omega

/-- `isBotFormula` on `Fin m`, in terms of values. -/
theorem realize_isBotFormula_fin (v : Fin 2 → Fin m) (i : Fin 2) :
    (isBotFormula i).Realize v ↔ (v i : ℕ) = 0 := by
  have := (v i).2
  rw [realize_isBotFormula]
  constructor
  · intro h
    have := h ⟨0, by omega⟩
    rw [Fin.le_def] at this
    simp only at this
    omega
  · intro h t
    rw [Fin.le_def]
    omega

/-- `twoAboveFormula` on `Fin m`, in terms of values. -/
theorem realize_twoAboveFormula_fin (v : Fin 2 → Fin m) (i j : Fin 2) :
    (twoAboveFormula i j).Realize v ↔ (v i : ℕ) + 2 = v j := by
  rw [realize_twoAboveFormula]
  simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
  have := (v j).2
  exact ⟨fun ⟨z, h₁, h₂⟩ => by omega, fun h => ⟨⟨v i + 1, by omega⟩, rfl, by simp only; omega⟩⟩

end Fin

/-! ### Bipartiteness -/

/-- The arcs of the cycle graph of a linear order: from each element to its successor, and from
the greatest element to the least one. -/
noncomputable def cycleArcFormula : Language.order.Formula (Fin 2) :=
  covByFormula 0 1 ⊔ (isTopFormula 0 ⊓ isBotFormula 1)

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- Adjacency in the cycle graph on `Fin m`, in terms of values. -/
theorem definedGraph_cycleArcFormula_adj_fin (x y : Fin m) :
    (definedGraph (Fin m) cycleArcFormula).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 1 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 0) ∨
        (y : ℕ) + 1 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 0)) := by
  simp only [definedGraph_adj, cycleArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_covByFormula_fin, realize_isTopFormula_fin, realize_isBotFormula_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.val_inj, or_assoc]

/-- The cycle graph on `Fin m`, for `m ≥ 2`, is bipartite iff `m` is even. -/
theorem definedGraph_cycleArcFormula_isBipartite_fin (hm : 2 ≤ m) :
    (definedGraph (Fin m) cycleArcFormula).IsBipartite ↔ Even m := by
  constructor
  · intro ⟨C⟩
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, rfl⟩ := hodd
    have hk : 1 ≤ k := by omega
    have key : ∀ a b c : Fin 2, a ≠ b → (a = c ↔ ¬ b = c) := by decide
    have par : ∀ i (h : i < 2 * k + 1), (C ⟨i, h⟩ = C ⟨0, by omega⟩ ↔ i % 2 = 0) := by
      intro i
      induction i with
      | zero => intro h; simp
      | succ i ih =>
        intro h
        have h1 := C.valid ((definedGraph_cycleArcFormula_adj_fin ⟨i + 1, h⟩ ⟨i, by omega⟩).2
          ⟨by simp only; omega, .inr (.inr (.inl rfl))⟩)
        rw [key _ _ _ h1, ih (by omega)]
        omega
    have hadj := C.valid ((definedGraph_cycleArcFormula_adj_fin ⟨2 * k, by omega⟩
      ⟨0, by omega⟩).2 ⟨by simp only; omega, .inr (.inl ⟨rfl, rfl⟩)⟩)
    exact hadj ((par (2 * k) (by omega)).2 (by omega))
  · rintro ⟨k, rfl⟩
    refine ⟨SimpleGraph.Coloring.mk (fun x => ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩) ?_⟩
    intro x y h
    rw [definedGraph_cycleArcFormula_adj_fin] at h
    intro he
    have := congrArg Fin.val he
    simp only at this
    omega

end Fin

/-- **Bipartiteness (2-colorability) is not first-order definable** on finite graphs, even on graphs
with at least `t` vertices [Libkin, Chapter 3][Libkin2004]. -/
theorem not_exists_sentence_isBipartite_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.IsBipartite) :=
  not_exists_sentence_of_even (fun _ G => G.IsBipartite) cycleArcFormula 2
    (fun M _ _ _ _ hM => by
      let := orderStructure (Fin (Nat.card M))
      have : Language.order.OrderedStructure (Fin (Nat.card M)) := ⟨fun _ => Iff.rfl⟩
      let e := definedGraphIsoFin cycleArcFormula M
      change (definedGraph M cycleArcFormula).IsBipartite ↔ _
      rw [← definedGraph_cycleArcFormula_isBipartite_fin hM]
      exact ⟨fun h => h.of_hom e.symm.toEmbedding.toHom, fun h => h.of_hom e.toEmbedding.toHom⟩)
    t

/-- **Bipartiteness (2-colorability) is not first-order definable** on finite graphs. -/
theorem not_exists_sentence_isBipartite :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsBipartite := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isBipartite_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

/-! ### Acyclicity -/

/-- The arcs of the step-two graph of a linear order closed by one edge: from each element to the
element two steps above it, and from the greatest element to the least one. -/
noncomputable def stepTwoTopBotArcFormula : Language.order.Formula (Fin 2) :=
  twoAboveFormula 0 1 ⊔ (isTopFormula 0 ⊓ isBotFormula 1)

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- Adjacency in the closed step-two graph on `Fin m`, in terms of values. -/
theorem definedGraph_stepTwoTopBotArcFormula_adj_fin (x y : Fin m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 0) ∨
        (y : ℕ) + 2 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 0)) := by
  simp only [definedGraph_adj, stepTwoTopBotArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_twoAboveFormula_fin, realize_isTopFormula_fin, realize_isBotFormula_fin,
    Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.val_inj, or_assoc]

private theorem isAcyclic_stepTwoTopBot_fin_of_even (hm : Even m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic := by
  obtain ⟨k, rfl⟩ := hm
  let f : Fin (k + k) → Fin (k + k) := fun x =>
    ⟨if x.1 % 2 = 0 then k - 1 - x.1 / 2 else 2 * k - 1 - x.1 / 2, by
      have := x.2; split <;> omega⟩
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg Fin.val h
    simp only [f] at h'
    ext
    have := x.2
    have := y.2
    split at h' <;> split at h' <;> omega
  let F : definedGraph (Fin (k + k)) stepTwoTopBotArcFormula →g SimpleGraph.pathGraph (k + k) :=
    ⟨f, fun {x y} h => by
      rw [definedGraph_stepTwoTopBotArcFormula_adj_fin] at h
      rw [SimpleGraph.pathGraph_adj]
      simp only [f]
      have := x.2
      have := y.2
      split <;> split <;> omega⟩
  exact (SimpleGraph.isAcyclic_pathGraph _).comap F hf

private theorem not_isAcyclic_stepTwoTopBot_fin_of_odd (hm : Odd m) (h5 : 5 ≤ m) :
    ¬ (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic := by
  obtain ⟨k, rfl⟩ := hm
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro h
  have h02 : (definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).Adj ⟨0, by omega⟩
      ⟨2, by omega⟩ :=
    (definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2 ⟨by simp only; omega, .inl rfl⟩
  apply SimpleGraph.isBridge_iff.1 (h h02)
  have reach : ∀ j (hj : 1 ≤ j) (hjk : j ≤ k),
      ((definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).deleteEdges
        {s(⟨0, by omega⟩, ⟨2, by omega⟩)}).Reachable ⟨2, by omega⟩ ⟨2 * j, by omega⟩ := by
    intro j hj hjk
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact .rfl
      · refine (ih hj0 (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨(definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2
          ⟨by simp only; omega, .inl (by simp only; omega)⟩, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff, Fin.ext_iff]
        omega
  have r1 : ((definedGraph (Fin (2 * k + 1)) stepTwoTopBotArcFormula).deleteEdges
      {s(⟨0, by omega⟩, ⟨2, by omega⟩)}).Reachable ⟨0, by omega⟩ ⟨2 * k, by omega⟩ := by
    refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨(definedGraph_stepTwoTopBotArcFormula_adj_fin _ _).2
      ⟨by simp only; omega, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, Fin.ext_iff]
    omega
  exact r1.trans (reach k (by omega) le_rfl).symm

/-- The step-two graph on `Fin m` closed by the edge `m - 1 — 0` is acyclic iff `m` is even, for
`m ≥ 4`. -/
theorem definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin (hm : 4 ≤ m) :
    (definedGraph (Fin m) stepTwoTopBotArcFormula).IsAcyclic ↔ Even m := by
  refine ⟨fun h => ?_, isAcyclic_stepTwoTopBot_fin_of_even⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  exact not_isAcyclic_stepTwoTopBot_fin_of_odd hodd (by obtain ⟨k, rfl⟩ := hodd; omega) h

end Fin

/-- **Acyclicity is not first-order definable** on finite graphs, even on graphs with at least `t`
vertices [Libkin, Chapter 3][Libkin2004]. -/
theorem not_exists_sentence_isAcyclic_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic) :=
  not_exists_sentence_of_even (fun _ G => G.IsAcyclic) stepTwoTopBotArcFormula 4
    (fun M _ _ _ _ hM => by
      let := orderStructure (Fin (Nat.card M))
      have : Language.order.OrderedStructure (Fin (Nat.card M)) := ⟨fun _ => Iff.rfl⟩
      change (definedGraph M stepTwoTopBotArcFormula).IsAcyclic ↔ _
      rw [(definedGraphIsoFin stepTwoTopBotArcFormula M).isAcyclic_iff,
        definedGraph_stepTwoTopBotArcFormula_isAcyclic_fin hM])
    t

/-- **Acyclicity is not first-order definable** on finite graphs. -/
theorem not_exists_sentence_isAcyclic :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.IsAcyclic := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_isAcyclic_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

end Cslib.Logic.FO.GraphProperties
