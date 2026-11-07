/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
public import Complexity.Logics.FirstOrder.Interpretation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.ModelTheory.Graph
import Mathlib.Data.Finset.Sort

/-!
# Connectivity is not first-order definable

A finite simple graph `G` on `V` is a structure in Mathlib's language of graphs
`FirstOrder.Language.graph` through `SimpleGraph.structure`. **No first-order sentence in this
language holds in exactly the connected finite graphs** (`not_exists_sentence_connected`), and this
remains true when only graphs with at least `t` vertices are considered
(`not_exists_sentence_connected_of_le_card`).

The proof reduces EVEN on finite linear orders to connectivity. The *step-two graph* of a linear
order joins each element to the element two steps above it, and closes the ends: the last element
is joined to the second one and the penultimate element to the first one (`stepTwoGraph`). On an
order with an odd number of elements this graph is a single cycle through all elements; on an order
with an even number of elements it is the disjoint union of the even and the odd positions
(`stepTwoGraph_connected_iff_odd`). Its adjacency relation is first-order definable from `≤`, so it
is the graph interpreted in the order by a one-dimensional first-order interpretation
(`stepTwoInterp`, `stepTwoModelEquiv`). A sentence `φ` defining connectivity would pull back to a
sentence of the language of orders (`realize_onSentence_stepTwoInterp`) that holds in a finite
linear order exactly when it has an odd number of elements. By the Ehrenfeucht–Fraïssé theorem for
finite linear orders (`FiniteLinearOrder.realize_iff_of_two_pow_le_card`), no such sentence exists.

The sentences range over the pure graph vocabulary, with no built-in order or arithmetic. In
ordered descriptive complexity (Immerman's conventions, with numeric predicates `≤` and `BIT`),
connectivity is still not first-order definable, but that follows from circuit lower bounds for
parity, not from this argument. Connectivity of undirected graphs is decidable in logarithmic space
(`USTCON_mem_L`), so this gives a concrete logspace graph property that first-order logic without
order cannot express.

## Main definitions

* `Cslib.Logic.FO.Connectivity.stepTwoGraph`: the step-two graph of a linear order.
* `Cslib.Logic.FO.Connectivity.stepTwoInterp`: the first-order interpretation of the language of
  graphs in the language of orders that defines the step-two graph.

## Main results

* `Cslib.Logic.FO.Connectivity.stepTwoGraph_connected_iff_odd`: the step-two graph of a finite
  linear order is connected iff the order has an odd number of elements.
* `Cslib.Logic.FO.Connectivity.realize_onSentence_stepTwoInterp`: a linear order satisfies the
  pullback of a graph sentence iff its step-two graph satisfies the sentence.
* `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected`: connectivity of finite graphs is
  not first-order definable.
* `Cslib.Logic.FO.Connectivity.not_exists_sentence_connected_of_le_card`: the same for graphs with
  at least `t` vertices.

## References

* [H.-D. Ebbinghaus and J. Flum, *Finite Model Theory*][EbbinghausFlum1999], Chapter 2
  (Ehrenfeucht–Fraïssé games and nondefinability of connectivity).
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 3 (connectivity is not
  definable, by a reduction from EVEN on linear orders).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Connectivity

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

/-- The formula of the language of orders defining `StepTwoArc`. -/
noncomputable def stepTwoArcFormula (x y : α) : Language.order.Formula α :=
  twoAboveFormula x y ⊔ (isTopFormula x ⊓ isSecondFormula y) ⊔
    (isPenultimateFormula x ⊓ isBotFormula y)

/-- The formula of the language of orders defining adjacency in `stepTwoGraph`. -/
noncomputable def stepTwoAdjFormula (x y : α) : Language.order.Formula α :=
  ∼(Term.equal (Term.var x) (Term.var y)) ⊓ (stepTwoArcFormula x y ⊔ stepTwoArcFormula y x)

/-! ### The step-two graph -/

variable {M : Type*} [LinearOrder M]

variable (M) in
/-- The arcs of the step-two graph of a linear order: from `x` to the element two steps above it,
from the greatest element to the second least element, and from the second greatest element to the
least element. -/
def StepTwoArc (x y : M) : Prop :=
  (∃ z, x ⋖ z ∧ z ⋖ y) ∨ ((∀ t, t ≤ x) ∧ ∃ z, (∀ t, z ≤ t) ∧ z ⋖ y) ∨
    ((∃ z, (∀ t, t ≤ z) ∧ x ⋖ z) ∧ ∀ t, y ≤ t)

/-- Unfolding `StepTwoArc`. -/
theorem stepTwoArc_iff {x y : M} :
    StepTwoArc M x y ↔ (∃ z, x ⋖ z ∧ z ⋖ y) ∨ ((∀ t, t ≤ x) ∧ ∃ z, (∀ t, z ≤ t) ∧ z ⋖ y) ∨
      ((∃ z, (∀ t, t ≤ z) ∧ x ⋖ z) ∧ ∀ t, y ≤ t) :=
  Iff.rfl

variable (M) in
/-- The **step-two graph** of a linear order: distinct elements are adjacent when there is a
`StepTwoArc` between them in either direction. On a finite linear order with `m` elements
`0 < 1 < ⋯ < m - 1`, this joins `i` and `i + 2`, `m - 1` and `1`, and `m - 2` and `0`. -/
def stepTwoGraph : SimpleGraph M where
  Adj x y := x ≠ y ∧ (StepTwoArc M x y ∨ StepTwoArc M y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Unfolding adjacency in `stepTwoGraph`. -/
theorem stepTwoGraph_adj {x y : M} :
    (stepTwoGraph M).Adj x y ↔ x ≠ y ∧ (StepTwoArc M x y ∨ StepTwoArc M y x) :=
  Iff.rfl

/-! ### Realizing the order formulas -/

section Realize

variable [Language.order.Structure M] [Language.order.OrderedStructure M]

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

/-- `stepTwoArcFormula` defines `StepTwoArc`. -/
@[simp]
theorem realize_stepTwoArcFormula (v : α → M) (x y : α) :
    (stepTwoArcFormula x y).Realize v ↔ StepTwoArc M (v x) (v y) := by
  simp only [stepTwoArcFormula, Formula.realize_sup, Formula.realize_inf,
    realize_twoAboveFormula, realize_isTopFormula, realize_isSecondFormula,
    realize_isPenultimateFormula, realize_isBotFormula, stepTwoArc_iff, or_assoc]

/-- `stepTwoAdjFormula` defines adjacency in `stepTwoGraph`. -/
@[simp]
theorem realize_stepTwoAdjFormula (v : α → M) (x y : α) :
    (stepTwoAdjFormula x y).Realize v ↔ (stepTwoGraph M).Adj (v x) (v y) := by
  simp only [stepTwoAdjFormula, Formula.realize_inf, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, Formula.realize_sup, realize_stepTwoArcFormula, stepTwoGraph_adj]

end Realize

/-! ### The step-two graph on `Fin m` -/

/-- The arcs of the step-two graph on `Fin m`, in terms of values. -/
theorem stepTwoArc_fin_iff {m : ℕ} (x y : Fin m) :
    StepTwoArc (Fin m) x y ↔ (x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 1) ∨
      ((x : ℕ) + 2 = m ∧ (y : ℕ) = 0) := by
  have hx := x.2
  have hy := y.2
  simp only [stepTwoArc_iff, Fin.covBy_iff, Nat.covBy_iff_add_one_eq, Fin.le_def]
  refine or_congr ⟨?_, ?_⟩ (or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩)
  · rintro ⟨z, h₁, h₂⟩
    omega
  · intro h
    exact ⟨⟨x + 1, by omega⟩, rfl, by simp only; omega⟩
  · rintro ⟨h₁, z, h₂, h₃⟩
    have := h₁ ⟨m - 1, by omega⟩
    have := h₂ ⟨0, by omega⟩
    simp only at *
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun t => by have := t.2; omega, ⟨0, by omega⟩, fun t => Nat.zero_le _,
      by simp only; omega⟩
  · rintro ⟨⟨z, h₁, h₂⟩, h₃⟩
    have := h₁ ⟨m - 1, by omega⟩
    have := h₃ ⟨0, by omega⟩
    have := z.2
    simp only at *
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨⟨m - 1, by omega⟩, fun t => by have := t.2; simp only; omega, by simp only; omega⟩,
      fun t => by omega⟩

/-- Adjacency in the step-two graph on `Fin m`, in terms of values. -/
theorem stepTwoGraph_adj_fin_iff {m : ℕ} (x y : Fin m) :
    (stepTwoGraph (Fin m)).Adj x y ↔ (x : ℕ) ≠ y ∧
      ((x : ℕ) + 2 = y ∨ ((x : ℕ) + 1 = m ∧ (y : ℕ) = 1) ∨ ((x : ℕ) + 2 = m ∧ (y : ℕ) = 0) ∨
        ((y : ℕ) + 2 = x ∨ ((y : ℕ) + 1 = m ∧ (x : ℕ) = 1) ∨
          ((y : ℕ) + 2 = m ∧ (x : ℕ) = 0))) := by
  simp only [stepTwoGraph_adj, stepTwoArc_fin_iff, ne_eq, Fin.val_inj, or_assoc]

private theorem reachable_even {m : ℕ} (hm : 0 < m) :
    ∀ j (h : 2 * j < m), (stepTwoGraph (Fin m)).Reachable ⟨0, hm⟩ ⟨2 * j, h⟩
  | 0, _ => .rfl
  | j + 1, h => (reachable_even hm j (by omega)).trans (SimpleGraph.Adj.reachable
      ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inl (by simp only; omega)⟩))

private theorem reachable_odd {m : ℕ} (hm : 1 < m) :
    ∀ j (h : 2 * j + 1 < m), (stepTwoGraph (Fin m)).Reachable ⟨1, hm⟩ ⟨2 * j + 1, h⟩
  | 0, _ => .rfl
  | j + 1, h => (reachable_odd hm j (by omega)).trans (SimpleGraph.Adj.reachable
      ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inl (by simp only; omega)⟩))

private theorem stepTwoGraph_fin_connected_of_odd {m : ℕ} (hm : Odd m) :
    (stepTwoGraph (Fin m)).Connected := by
  obtain ⟨t, rfl⟩ := hm
  have h0 : 0 < 2 * t + 1 := by omega
  have : Nonempty (Fin (2 * t + 1)) := ⟨⟨0, h0⟩⟩
  refine SimpleGraph.Connected.mk fun x y => ?_
  suffices h : ∀ x : Fin (2 * t + 1), (stepTwoGraph _).Reachable ⟨0, h0⟩ x from
    (h x).symm.trans (h y)
  intro x
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' x.1
  · have := reachable_even h0 j (by omega)
    convert this using 1
    exact Fin.ext hj
  · have ht : 0 < t := by have := x.2; omega
    have h1 : 1 < 2 * t + 1 := by omega
    have h10 : (stepTwoGraph (Fin (2 * t + 1))).Reachable ⟨0, h0⟩ ⟨1, h1⟩ :=
      (reachable_even h0 t (by omega)).trans (SimpleGraph.Adj.reachable
        ((stepTwoGraph_adj_fin_iff _ _).2 ⟨by simp only; omega, .inr (.inl ⟨rfl, rfl⟩)⟩))
    refine h10.trans ?_
    have := reachable_odd h1 j (by omega)
    convert this using 1
    exact Fin.ext hj

private theorem not_stepTwoGraph_fin_connected_of_even {m : ℕ} (hm : Even m) :
    ¬ (stepTwoGraph (Fin m)).Connected := by
  intro hc
  obtain ⟨t, rfl⟩ := hm
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact hc.nonempty.elim fun x => x.elim0
  have hpar : ∀ x y : Fin (t + t), (stepTwoGraph _).Adj x y → (x : ℕ) % 2 = (y : ℕ) % 2 := by
    intro x y h
    rw [stepTwoGraph_adj_fin_iff] at h
    omega
  have h01 := hc.preconnected ⟨0, by omega⟩ ⟨1, by omega⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h01
  have key : ∀ y, Relation.ReflTransGen (stepTwoGraph (Fin (t + t))).Adj ⟨0, by omega⟩ y →
      (y : ℕ) % 2 = 0 := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hab ih => rw [← hpar _ _ hab, ih]
  exact absurd (key _ h01) (by simp)

/-- The step-two graph on `Fin m` is connected exactly when `m` is odd. -/
theorem stepTwoGraph_fin_connected_iff {m : ℕ} : (stepTwoGraph (Fin m)).Connected ↔ Odd m := by
  rcases Nat.even_or_odd m with h | h
  · exact ⟨fun hc => absurd hc (not_stepTwoGraph_fin_connected_of_even h),
      fun ho => absurd h (Nat.not_even_iff_odd.2 ho)⟩
  · exact ⟨fun _ => h, fun _ => stepTwoGraph_fin_connected_of_odd h⟩

/-! ### Transport along order isomorphisms -/

/-- Order isomorphisms preserve `StepTwoArc`. -/
theorem stepTwoArc_orderIso {N : Type*} [LinearOrder N] (e : M ≃o N) (x y : M) :
    StepTwoArc N (e x) (e y) ↔ StepTwoArc M x y := by
  simp only [stepTwoArc_iff, e.surjective.exists, e.surjective.forall, apply_covBy_apply_iff e,
    e.le_iff_le]

/-- An order isomorphism is an isomorphism of step-two graphs. -/
def stepTwoGraphIso {N : Type*} [LinearOrder N] (e : M ≃o N) :
    stepTwoGraph M ≃g stepTwoGraph N where
  toEquiv := e.toEquiv
  map_rel_iff' {x y} := by
    simp only [stepTwoGraph_adj, RelIso.coe_fn_toEquiv, stepTwoArc_orderIso, ne_eq,
      EmbeddingLike.apply_eq_iff_eq]

/-- The step-two graph of a finite linear order is connected exactly when the order has an odd
number of elements. -/
theorem stepTwoGraph_connected_iff_odd [Finite M] :
    (stepTwoGraph M).Connected ↔ Odd (Nat.card M) := by
  have := Fintype.ofFinite M
  rw [← (stepTwoGraphIso
      (Fintype.orderIsoFinOfCardEq M Nat.card_eq_fintype_card.symm)).connected_iff,
    stepTwoGraph_fin_connected_iff]

/-! ### The interpretation -/

/-- The one-dimensional first-order interpretation of the language of graphs in the language of
orders whose interpreted graph is the step-two graph: every element is in the domain, and adjacency
is defined by `stepTwoAdjFormula`. -/
noncomputable def stepTwoInterp : Interpretation Language.order Language.graph Unit where
  domain := ⊤
  rel := fun {n} R => match n, R with
    | 2, .adj => stepTwoAdjFormula ((0 : Fin 2), ()) ((1 : Fin 2), ())

variable [Language.order.Structure M] [Language.order.OrderedStructure M]

variable (M) in
/-- The graph interpreted by `stepTwoInterp` in a linear order is its step-two graph. -/
noncomputable def stepTwoModelEquiv :
    letI := (stepTwoGraph M).structure
    stepTwoInterp.Model M ≃[Language.graph] M :=
  letI := (stepTwoGraph M).structure
  { toFun x := x.1 ()
    invFun y := Interpretation.Model.mk (fun _ => y) (Formula.realize_top.2 trivial)
    left_inv _ := Interpretation.Model.ext rfl
    right_inv _ := rfl
    map_fun' f := isEmptyElim f
    map_rel' {n} R x := by
      match n, R with
      | 2, .adj => exact (realize_stepTwoAdjFormula (fun p => (x p.1).1 p.2) ((0 : Fin 2), ())
          ((1 : Fin 2), ())).symm }

variable (M) in
/-- A linear order satisfies the pullback along `stepTwoInterp` of a sentence of the language of
graphs exactly when its step-two graph satisfies the sentence. -/
theorem realize_onSentence_stepTwoInterp (φ : Language.graph.Sentence) :
    M ⊨ stepTwoInterp.onSentence φ ↔ (letI := (stepTwoGraph M).structure; M ⊨ φ) := by
  let := (stepTwoGraph M).structure
  rw [Interpretation.realize_onSentence]
  exact StrongHomClass.realize_sentence (stepTwoModelEquiv M) φ

/-! ### Nondefinability of connectivity -/

/-- **Connectivity is not first-order definable** on finite graphs, even on graphs with at least
`t` vertices: no sentence of the language of graphs holds in exactly the connected ones among the
finite simple graphs with at least `t` vertices [Libkin, Chapter 3][Libkin2004]. -/
theorem not_exists_sentence_connected_of_le_card (t : ℕ) :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      t ≤ Nat.card V → ((letI := G.structure; V ⊨ φ) ↔ G.Connected) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨n, hn, htn⟩ : ∃ n, quantifierRank (stepTwoInterp.onSentence φ) ≤ n ∧ t ≤ n :=
    ⟨max (quantifierRank (stepTwoInterp.onSentence φ)) t, le_max_left _ _, le_max_right _ _⟩
  have ht : t ≤ 2 ^ n := htn.trans Nat.lt_two_pow_self.le
  have key : ∀ (M : Type u) [LinearOrder M] [Finite M] [Language.order.Structure M]
      [Language.order.OrderedStructure M], t ≤ Nat.card M →
      (M ⊨ stepTwoInterp.onSentence φ ↔ Odd (Nat.card M)) := by
    intro M _ _ _ _ hM
    rw [realize_onSentence_stepTwoInterp, hφ _ _ hM, stepTwoGraph_connected_iff_odd]
  let := orderStructure (ULift.{u} (Fin (2 ^ n)))
  let := orderStructure (ULift.{u} (Fin (2 ^ n + 1)))
  have : Language.order.OrderedStructure (ULift.{u} (Fin (2 ^ n))) := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure (ULift.{u} (Fin (2 ^ n + 1))) := ⟨fun _ => Iff.rfl⟩
  have h := FiniteLinearOrder.realize_iff_of_two_pow_le_card (M := ULift.{u} (Fin (2 ^ n)))
    (N := ULift.{u} (Fin (2 ^ n + 1))) (by rw [Nat.card_ulift, Nat.card_fin]; omega)
    (by rw [Nat.card_ulift, Nat.card_fin]; omega) hn
  rw [key _ (by rw [Nat.card_ulift, Nat.card_fin]; omega),
    key _ (by rw [Nat.card_ulift, Nat.card_fin]; omega), Nat.card_ulift, Nat.card_ulift,
    Nat.card_fin, Nat.card_fin, Nat.odd_add_one] at h
  exact iff_not_self h

/-- **Connectivity is not first-order definable** on finite graphs: no sentence of the language of
graphs holds in exactly the connected finite simple graphs [Libkin, Chapter 3][Libkin2004]. -/
theorem not_exists_sentence_connected :
    ¬ ∃ φ : Language.graph.Sentence, ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (letI := G.structure; V ⊨ φ) ↔ G.Connected := fun ⟨φ, hφ⟩ =>
  not_exists_sentence_connected_of_le_card 0 ⟨φ, fun V _ G _ => hφ V G⟩

end Cslib.Logic.FO.Connectivity
