/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
public import CslibFrontier.Logics.FirstOrder.Interpretation
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.ModelTheory.Graph
import CslibFrontier.Tactic.FirstOrder.Simp
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases

/-!
# Graphs defined by a formula, and parity transfer from linear orders

A formula `δ` with two free variables defines a graph in every `L`-structure `M`
(`definedGraph M δ`): distinct elements are adjacent when `δ` holds of them in some order. This is
the graph interpreted in `M` by a one-dimensional first-order interpretation `graphInterp δ` of
Mathlib's language of graphs `FirstOrder.Language.graph` (`graphInterpEquiv`), so a sentence about
graphs pulls back to a sentence of `L` (`realize_onSentence_graphInterp`). Isomorphic structures
define isomorphic graphs (`definedGraphIso`).

**Parity transfer.** Suppose that, in every large enough finite linear order, the graph defined by
`δ` has a property exactly when the order has an even number of elements
(`not_exists_sentence_of_even`), or exactly when it has an odd number
(`not_exists_sentence_of_odd`). Then the property is not first-order definable on finite graphs.
A defining sentence would pull back to a sentence of the language of orders that expresses the
parity of the size, which the Ehrenfeucht–Fraïssé theorem for finite linear orders rules out
(`FiniteLinearOrder.realize_iff_of_two_pow_le_card`). This is the reduction used for connectivity
in [Libkin, Corollary 3.19][Libkin2004], packaged for an arbitrary graph property.

The file also provides the order formulas used to define such graphs (`covByFormula`,
`isBotFormula`, `isTopFormula`, `twoAboveFormula`, `isSecondFormula`, `isPenultimateFormula`),
together with their meaning in any linear order and, in terms of values, in `Fin m`.

Sentences about graphs range over the pure graph vocabulary, with no built-in order or arithmetic.

## Main definitions

* `Cslib.Logic.FO.DefinedGraph.definedGraph`: the graph defined by a formula with two free
  variables.
* `Cslib.Logic.FO.DefinedGraph.graphInterp`: the first-order interpretation of the language of
  graphs that interprets it.

## Main results

* `Cslib.Logic.FO.DefinedGraph.realize_onSentence_graphInterp`: pulling back graph sentences.
* `Cslib.Logic.FO.DefinedGraph.not_exists_sentence_of_even`,
  `Cslib.Logic.FO.DefinedGraph.not_exists_sentence_of_odd`: parity transfer.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Corollary 3.19 (connectivity, by
  reduction from EVEN on linear orders; the method packaged here).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.DefinedGraph

universe u

/-! ### Order formulas -/

variable {α : Type*}

/-- The formula `x ⋖ y` of the language of orders: `y` covers `x`. -/
noncomputable def covByFormula (x y : α) : Language.order.Formula α :=
  (Term.var (Sum.inl x)).lt (Term.var (Sum.inl y)) ⊓
    ∀' ∼(((Term.var (Sum.inl x)).lt (&0)) ⊓ ((&0).lt (Term.var (Sum.inl y))))

/-- The formula of the language of orders saying that `x` is the least element. -/
noncomputable def isBotFormula (x : α) : Language.order.Formula α :=
  ∀' ((Term.var (Sum.inl x)).le (&0))

/-- The formula of the language of orders saying that `x` is the greatest element. -/
noncomputable def isTopFormula (x : α) : Language.order.Formula α :=
  ∀' ((&0).le (Term.var (Sum.inl x)))

/-- The formula of the language of orders saying that `y` is two steps above `x`. -/
noncomputable def twoAboveFormula (x y : α) : Language.order.Formula α :=
  Formula.iExs (Fin 1)
    (covByFormula (α := α ⊕ Fin 1) (.inl x) (.inr 0) ⊓
      covByFormula (α := α ⊕ Fin 1) (.inr 0) (.inl y))

/-- The formula of the language of orders saying that `x` is the second least element. -/
noncomputable def isSecondFormula (x : α) : Language.order.Formula α :=
  Formula.iExs (Fin 1)
    (isBotFormula (α := α ⊕ Fin 1) (.inr 0) ⊓ covByFormula (α := α ⊕ Fin 1) (.inr 0) (.inl x))

/-- The formula of the language of orders saying that `x` is the second greatest element. -/
noncomputable def isPenultimateFormula (x : α) : Language.order.Formula α :=
  Formula.iExs (Fin 1)
    (isTopFormula (α := α ⊕ Fin 1) (.inr 0) ⊓ covByFormula (α := α ⊕ Fin 1) (.inl x) (.inr 0))

section Realize

variable {M : Type*} [LinearOrder M] [Language.order.Structure M]
  [Language.order.OrderedStructure M]

/-- `covByFormula x y` holds iff the value of `y` covers the value of `x`. -/
@[simp]
theorem realize_covByFormula (v : α → M) (x y : α) :
    (covByFormula x y).Realize v ↔ v x ⋖ v y := by
  simp [covByFormula, Formula.Realize, Fin.snoc, CovBy]

/-- `isBotFormula x` holds iff the value of `x` is the least element. -/
@[simp]
theorem realize_isBotFormula (v : α → M) (x : α) :
    (isBotFormula x).Realize v ↔ ∀ t, v x ≤ t := by
  simp [isBotFormula, Formula.Realize, Fin.snoc]

/-- `isTopFormula x` holds iff the value of `x` is the greatest element. -/
@[simp]
theorem realize_isTopFormula (v : α → M) (x : α) :
    (isTopFormula x).Realize v ↔ ∀ t, t ≤ v x := by
  simp [isTopFormula, Formula.Realize, Fin.snoc]

omit [LinearOrder M] [Language.order.Structure M] [Language.order.OrderedStructure M] in
private theorem exists_fin_one {p : M → Prop} : (∃ i : Fin 1 → M, p (i 0)) ↔ ∃ z, p z :=
  ⟨fun ⟨i, h⟩ => ⟨i 0, h⟩, fun ⟨z, h⟩ => ⟨fun _ => z, h⟩⟩

/-- `twoAboveFormula x y` holds iff the value of `y` is two steps above the value of `x`. -/
@[simp]
theorem realize_twoAboveFormula (v : α → M) (x y : α) :
    (twoAboveFormula x y).Realize v ↔ ∃ z, v x ⋖ z ∧ z ⋖ v y := by
  rw [twoAboveFormula, Formula.realize_iExs]
  simp only [Formula.realize_inf, realize_covByFormula, Sum.elim_inl, Sum.elim_inr]
  exact exists_fin_one (p := fun z => v x ⋖ z ∧ z ⋖ v y)

/-- `isSecondFormula x` holds iff the value of `x` covers the least element. -/
@[simp]
theorem realize_isSecondFormula (v : α → M) (x : α) :
    (isSecondFormula x).Realize v ↔ ∃ z, (∀ t, z ≤ t) ∧ z ⋖ v x := by
  rw [isSecondFormula, Formula.realize_iExs]
  simp only [Formula.realize_inf, realize_covByFormula, realize_isBotFormula, Sum.elim_inl,
    Sum.elim_inr]
  exact exists_fin_one (p := fun z => (∀ t, z ≤ t) ∧ z ⋖ v x)

/-- `isPenultimateFormula x` holds iff the greatest element covers the value of `x`. -/
@[simp]
theorem realize_isPenultimateFormula (v : α → M) (x : α) :
    (isPenultimateFormula x).Realize v ↔ ∃ z, (∀ t, t ≤ z) ∧ v x ⋖ z := by
  rw [isPenultimateFormula, Formula.realize_iExs]
  simp only [Formula.realize_inf, realize_covByFormula, realize_isTopFormula, Sum.elim_inl,
    Sum.elim_inr]
  exact exists_fin_one (p := fun z => (∀ t, t ≤ z) ∧ v x ⋖ z)

end Realize

/-! ### Order formulas on `Fin m` -/

section Fin

variable {m : ℕ} [Language.order.Structure (Fin m)] [Language.order.OrderedStructure (Fin m)]

/-- `covByFormula` on `Fin m`, in terms of values. -/
theorem realize_covByFormula_fin (v : α → Fin m) (x y : α) :
    (covByFormula x y).Realize v ↔ (v x : ℕ) + 1 = v y := by
  rw [realize_covByFormula, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]

/-- `isTopFormula` on `Fin m`, in terms of values. -/
theorem realize_isTopFormula_fin (v : α → Fin m) (x : α) :
    (isTopFormula x).Realize v ↔ (v x : ℕ) + 1 = m := by
  have := (v x).2
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
theorem realize_isBotFormula_fin (v : α → Fin m) (x : α) :
    (isBotFormula x).Realize v ↔ (v x : ℕ) = 0 := by
  have := (v x).2
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
theorem realize_twoAboveFormula_fin (v : α → Fin m) (x y : α) :
    (twoAboveFormula x y).Realize v ↔ (v x : ℕ) + 2 = v y := by
  rw [realize_twoAboveFormula]
  simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
  have := (v y).2
  exact ⟨fun ⟨z, h₁, h₂⟩ => by omega, fun h => ⟨⟨v x + 1, by omega⟩, rfl, by simp only; omega⟩⟩

end Fin

/-! ### Graphs defined by a formula -/

section Defined

variable {L : Language} {M : Type*} [L.Structure M]

variable (M) in
/-- The graph defined in an `L`-structure by a formula `δ` with two free variables: distinct
elements are adjacent when `δ` holds of them in some order. -/
def definedGraph (δ : L.Formula (Fin 2)) : SimpleGraph M :=
  SimpleGraph.fromRel fun x y => δ.Realize ![x, y]

/-- Adjacency in `definedGraph`. -/
@[simp]
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
  fo_simp [definedAdjFormula, h₁, h₂, definedGraph_adj]

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

/-- A finite linear order `M` and `Fin (Nat.card M)` define isomorphic graphs. -/
noncomputable def definedGraphIsoFin (δ : Language.order.Formula (Fin 2)) (M : Type*)
    [LinearOrder M] [Finite M] [Language.order.Structure M] [Language.order.OrderedStructure M]
    [Language.order.Structure (Fin (Nat.card M))]
    [Language.order.OrderedStructure (Fin (Nat.card M))] :
    definedGraph M δ ≃g definedGraph (Fin (Nat.card M)) δ :=
  have := Fintype.ofFinite M
  definedGraphIso (Fintype.orderIsoFinOfCardEq M Nat.card_eq_fintype_card.symm).symm δ

/-! ### Transfer from parity of finite linear orders -/

/-- **Parity transfer, even sizes.** Let `δ` define, in every finite linear order with at least
`t₀` elements, a graph that has the property `P` exactly when the order has an even number of
elements. Then no sentence of the language of graphs defines `P` among the finite simple graphs
with at least `t` vertices. -/
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

/-- **Parity transfer, odd sizes.** Let `δ` define, in every finite linear order with at least `t₀`
elements, a graph that has the property `P` exactly when the order has an odd number of elements.
Then no sentence of the language of graphs defines `P` among the finite simple graphs with at least
`t` vertices. -/
theorem not_exists_sentence_of_odd (P : ∀ V : Type u, SimpleGraph V → Prop)
    (δ : Language.order.Formula (Fin 2)) (t₀ : ℕ)
    (hP : ∀ (M : Type u) [LinearOrder M] [Finite M] [Language.order.Structure M]
      [Language.order.OrderedStructure M], t₀ ≤ Nat.card M →
      (P M (definedGraph M δ) ↔ Odd (Nat.card M)))
    (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ P V G) := by
  rintro ⟨φ, hφ⟩
  refine not_exists_sentence_of_even (fun V G => ¬ P V G) δ t₀ (fun M _ _ _ _ hM => ?_) t
    ⟨∼φ, fun V _ G hV => ?_⟩
  · rw [hP M hM, Nat.not_odd_iff_even]
  · let := G.structure
    exact (Sentence.realize_not _).trans (not_congr (hφ V G hV))

end Cslib.Logic.FO.DefinedGraph
