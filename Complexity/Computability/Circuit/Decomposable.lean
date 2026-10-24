/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Rectangle
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Threshold counting for decomposable DAGs

A *smooth decomposable DAG* (`DecomposableDAG`) represents a set of inputs `ι → U` by nodes of
three kinds, each about a set of coordinates, its *scope*, and accepting a set of assignments of
its scope:

* a *leaf* accepts at most one assignment, as a literal or a constant does;
* a *union* accepts what one of its children accepts, and each child has its scope (smoothness);
* a *product* of two children accepts what both accept, and their scopes split its scope into
  two disjoint parts (decomposability).

The root has every coordinate in its scope, and a rank decreasing from each node to its children
makes the DAG acyclic. Nodes may be shared, unions need not be disjoint (the DAG need not be
deterministic), and different branches may split the coordinates in different ways. Over the
alphabet `Bool` with literal leaves, these are the smooth DNNFs of knowledge compilation
[Darwiche2001].

**Certificates and rectangles.** A node *occurs* on an accepting certificate of an input `x`
(`DecomposableDAG.Occurs`) when it is the root and accepts `x`, a child of an occurring union that
accepts `x`, or a child of an occurring product. If a node occurs for `x`, then replacing the part
of `x` on its scope by any assignment that the node accepts keeps the input accepted
(`DecomposableDAG.Occurs.mem_accepted`). So the assignments accepted by a node and its
*contexts*, the parts outside its scope of the inputs for which it occurs, form a rectangle inside
the accepted set (`DecomposableDAG.rectangle_subset`) [BovaCapelliMengelSlivovsky2016].

**Threshold counting.** Let the accepted set be `K`-rectangle-free with at least `K` elements.
Descend along a certificate of an accepted input `x`, from the root, to the lowest node `v` that
accepts at least `K` assignments, so that the children of `v` on the certificate accept fewer.
By rectangle-freeness `v` has fewer than `K` contexts. If `v` is a union, then `x` is determined
by a child accepting it, its part on that child, and its context; if `v` is a product, by its
parts on both children and its context. So each union edge is charged at most `(K - 1) ^ 2`
inputs and each product at most `(K - 1) ^ 3` (`DecomposableDAG.ncard_accepted_le`):

`|accepted| ≤ (K - 1) ^ 2 · #(union edges) + (K - 1) ^ 3 · #(products)`.

For dense rectangle-free sets with small thresholds, every smooth decomposable DAG is therefore
exponentially large.

## Main definitions

* `Cslib.Circuits.DecomposableDAG.Gate`, `Cslib.Circuits.DecomposableDAG`: a smooth
  decomposable DAG and its node gates.
* `Cslib.Circuits.DecomposableDAG.accepts`, `Cslib.Circuits.DecomposableDAG.accepted`: the
  inputs accepted by a node and the set represented by the DAG.
* `Cslib.Circuits.DecomposableDAG.Occurs`, `Cslib.Circuits.DecomposableDAG.contexts`,
  `Cslib.Circuits.DecomposableDAG.stops`: nodes on accepting certificates, node contexts,
  and threshold stopping nodes.
* `Cslib.Circuits.DecomposableDAG.unionEdges`, `DecomposableDAG.products`,
  `DecomposableDAG.size`: the size of a DAG.

## Main results

* `Cslib.Circuits.DecomposableDAG.rectangle_subset`: a node and its contexts form a
  rectangle inside the accepted set.
* `Cslib.Circuits.DecomposableDAG.ncard_accepted_le`: threshold counting.
* `Cslib.Circuits.DecomposableDAG.ncard_accepted_le_size`: threshold counting, charging
  `(K - 1) ^ 3` to every union edge and every product.

## References

* [A. Darwiche, *Decomposable negation normal form*][Darwiche2001]
* [S. Bova, F. Capelli, S. Mengel, F. Slivovsky, *Knowledge compilation meets communication
  complexity*][BovaCapelliMengelSlivovsky2016]
-/

@[expose] public section

namespace Cslib.Circuits

open Set Frontier

variable {ι U : Type*} {K : ℕ}

/-- The gate at a node of a decomposable DAG on the nodes `N`. -/
inductive DecomposableDAG.Gate (N : Type*) where
  /-- A leaf, accepting at most one assignment of its scope. -/
  | leaf
  /-- A union of finitely many children. -/
  | union (children : Finset N)
  /-- A product of two children. -/
  | product (left right : N)

/-- A *smooth decomposable DAG* on the nodes `N`, representing a set of inputs `ι → U`. Each node
has a *scope*, a set of coordinates, and accepts a set of assignments of its scope. The gate at a
node is a leaf, accepting at most one assignment; a union of children, each with the scope of the
node, accepting what one of them accepts; or a product of two children whose scopes split the
scope of the node into two disjoint parts, accepting what both accept. The root has every
coordinate in its scope, and a rank decreasing from each node to its children makes the DAG
acyclic. -/
structure DecomposableDAG (ι U N : Type*) where
  /-- The coordinates that a node is about. -/
  scope : N → Set ι
  /-- The root. -/
  root : N
  /-- The root is about every coordinate. -/
  scope_root : scope root = univ
  /-- The gate at a node. -/
  gate : N → DecomposableDAG.Gate N
  /-- A rank that decreases from each node to its children. -/
  rank : N → ℕ
  /-- The assignments of its scope that a node accepts. -/
  values : (v : N) → Set (scope v → U)
  /-- A leaf accepts at most one assignment. -/
  values_subsingleton : ∀ v, gate v = .leaf → (values v).Subsingleton
  /-- The children of a union have its scope (smoothness). -/
  scope_union : ∀ v c, gate v = .union c → ∀ u ∈ c, scope u = scope v
  /-- The children of a union have lower rank. -/
  rank_union : ∀ v c, gate v = .union c → ∀ u ∈ c, rank u < rank v
  /-- A union accepts what one of its children accepts. -/
  values_union : ∀ v c, gate v = .union c → ∀ x : ι → U,
    (scope v).domRestrict x ∈ values v ↔ ∃ u ∈ c, (scope u).domRestrict x ∈ values u
  /-- The scope of a product is the union of the scopes of its children. -/
  scope_product : ∀ v l r, gate v = .product l r → scope v = scope l ∪ scope r
  /-- The scopes of the children of a product are disjoint (decomposability). -/
  disjoint_product : ∀ v l r, gate v = .product l r → Disjoint (scope l) (scope r)
  /-- The children of a product have lower rank. -/
  rank_product : ∀ v l r, gate v = .product l r → rank l < rank v ∧ rank r < rank v
  /-- A product accepts what both of its children accept. -/
  values_product : ∀ v l r, gate v = .product l r → ∀ x : ι → U,
    (scope v).domRestrict x ∈ values v ↔
      (scope l).domRestrict x ∈ values l ∧ (scope r).domRestrict x ∈ values r

namespace DecomposableDAG

variable {N : Type*} (P : DecomposableDAG ι U N)

/-- The inputs accepted by a node: those whose part on its scope it accepts. -/
def accepts (v : N) : Set (ι → U) :=
  {x | (P.scope v).domRestrict x ∈ P.values v}

/-- The set represented by the DAG: the inputs accepted by the root. -/
def accepted : Set (ι → U) :=
  P.accepts P.root

/-- Acceptance at a node `v` depends only on the coordinates in `P.scope v`. -/
theorem accepts_congr {v : N} {x y : ι → U} (h : EqOn x y (P.scope v)) :
    x ∈ P.accepts v ↔ y ∈ P.accepts v := by
  change _ ∈ P.values v ↔ _ ∈ P.values v
  rw [domRestrict_eq_domRestrict_iff.mpr h]

/-! ### Certificates and rectangles -/

/-- A node *occurs* on an accepting certificate of the input `x`. -/
inductive Occurs (x : ι → U) : N → Prop
  /-- The root occurs when it accepts `x`. -/
  | root : x ∈ P.accepted → Occurs x P.root
  /-- A child of an occurring union occurs when it accepts `x`. -/
  | union {v u : N} {c : Finset N} : Occurs x v → P.gate v = .union c → u ∈ c →
      x ∈ P.accepts u → Occurs x u
  /-- The left child of an occurring product occurs. -/
  | left {v l r : N} : Occurs x v → P.gate v = .product l r → Occurs x l
  /-- The right child of an occurring product occurs. -/
  | right {v l r : N} : Occurs x v → P.gate v = .product l r → Occurs x r

variable {P}

/-- A node occurring for `x` accepts `x`. -/
theorem Occurs.accepts {x : ι → U} {v : N} (h : P.Occurs x v) : x ∈ P.accepts v := by
  induction h with
  | root h => exact h
  | union _ _ _ h _ => exact h
  | left _ hg ih => exact ((P.values_product _ _ _ hg x).mp ih).1
  | right _ hg ih => exact ((P.values_product _ _ _ hg x).mp ih).2

/-- **Substitution.** If a node occurs for `x`, then any input that the node accepts and that
agrees with `x` outside the scope of the node is accepted. -/
theorem Occurs.mem_accepted {x : ι → U} {v : N} (h : P.Occurs x v) {y : ι → U}
    (hy : y ∈ P.accepts v) (hout : EqOn y x (P.scope v)ᶜ) : y ∈ P.accepted := by
  induction h with
  | root _ => exact hy
  | @union v u c _ hg hu _ ih =>
    refine ih ((P.values_union v c hg y).mpr ⟨u, hu, hy⟩) ?_
    simpa only [P.scope_union v c hg u hu] using hout
  | @left v l r hv hg ih =>
    -- The right part of `y` is that of `x`, which the right child accepts.
    have hr : y ∈ P.accepts r :=
      (P.accepts_congr fun i hi =>
        hout ((P.disjoint_product v l r hg).symm.notMem_of_mem_left hi)).mpr
        ((P.values_product v l r hg x).mp hv.accepts).2
    refine ih ((P.values_product v l r hg y).mpr ⟨hy, hr⟩) fun i hi => hout fun hil => hi ?_
    rw [P.scope_product v l r hg]
    exact Or.inl hil
  | @right v l r hv hg ih =>
    have hl : y ∈ P.accepts l :=
      (P.accepts_congr fun i hi =>
        hout ((P.disjoint_product v l r hg).notMem_of_mem_left hi)).mpr
        ((P.values_product v l r hg x).mp hv.accepts).1
    refine ih ((P.values_product v l r hg y).mpr ⟨hl, hy⟩) fun i hi => hout fun hir => hi ?_
    rw [P.scope_product v l r hg]
    exact Or.inr hir

variable (P)

/-- The *contexts* of a node: the parts outside its scope of the inputs for which it occurs. -/
def contexts (v : N) : Set (↥(P.scope v)ᶜ → U) :=
  (P.scope v)ᶜ.domRestrict '' {x | P.Occurs x v}

/-- **A node and its contexts form a rectangle** inside the accepted set. -/
theorem rectangle_subset (v : N) :
    rectangle (P.scope v) (P.values v) (P.contexts v) ⊆ P.accepted := by
  rintro y ⟨hy, x, hx, hxy⟩
  exact hx.mem_accepted hy (domRestrict_eq_domRestrict_iff.mp hxy).symm

/-- A node accepting at least `K` assignments has fewer than `K` contexts, when the accepted set
is `K`-rectangle-free. -/
private theorem ncard_contexts_le (hS : RectangleFree P.accepted K) {v : N}
    (hv : K ≤ (P.values v).ncard) : (P.contexts v).ncard ≤ K - 1 := by
  rcases hS.ncard_lt_or _ _ _ (P.rectangle_subset v) with h | h <;> omega

/-! ### Threshold counting -/

/-- The inputs for which the descent to the threshold `K` stops at the node `v`: the node occurs
for the input and accepts at least `K` assignments, while the children of `v` through which the
input is accepted accept fewer. -/
def stops (K : ℕ) (v : N) : Set (ι → U) :=
  {x | P.Occurs x v ∧ K ≤ (P.values v).ncard ∧
    match P.gate v with
    | .leaf => False
    | .union c => ∃ u ∈ c, x ∈ P.accepts u ∧ (P.values u).ncard < K
    | .product l r => (P.values l).ncard < K ∧ (P.values r).ncard < K}

/-- The threshold budget of a node: `(K - 1) ^ 2` for each child of a union and `(K - 1) ^ 3` for
a product. -/
private def budget (K : ℕ) (v : N) : ℕ :=
  match P.gate v with
  | .leaf => 0
  | .union c => (K - 1) ^ 2 * c.card
  | .product _ _ => (K - 1) ^ 3

section Finite

variable [Finite ι] [Finite U]

/-- **The descent stops.** If the accepted set has at least `K > 1` elements, the descent from
the root along a certificate of an accepted input stops at some node. The rank makes the descent
finite, even with shared nodes. -/
theorem exists_mem_stops (hK : 1 < K) (hS : K ≤ P.accepted.ncard) {x : ι → U}
    (hx : x ∈ P.accepted) : ∃ v, x ∈ P.stops K v := by
  classical
  have hroot : K ≤ (P.values P.root).ncard := hS.trans
    (ncard_le_ncard_of_injOn (P.scope P.root).domRestrict (fun _ hy => hy)
      (fun _ _ _ _ h => funext fun i =>
        domRestrict_eq_domRestrict_iff.mp h (P.scope_root ▸ mem_univ i)))
  -- Take an occurring node of least rank among those accepting at least `K` assignments.
  have hex : ∃ k, ∃ v, P.rank v = k ∧ P.Occurs x v ∧ K ≤ (P.values v).ncard :=
    ⟨_, P.root, rfl, .root hx, hroot⟩
  obtain ⟨v, hv, hxv, hlarge⟩ := Nat.find_spec hex
  have hsmall {u : N} (hu : P.rank u < P.rank v) (hxu : P.Occurs x u) :
      (P.values u).ncard < K := by
    by_contra! h
    exact Nat.find_min hex (hv ▸ hu) ⟨u, rfl, hxu, h⟩
  refine ⟨v, hxv, hlarge, ?_⟩
  cases hg : P.gate v with
  | leaf =>
    have := ncard_le_one_iff_subsingleton.mpr (P.values_subsingleton v hg)
    omega
  | union c =>
    obtain ⟨u, hu, hxu⟩ := (P.values_union v c hg x).mp hxv.accepts
    exact ⟨u, hu, hxu, hsmall (P.rank_union v c hg u hu) (.union hxv hg hu hxu)⟩
  | product l r =>
    exact ⟨hsmall (P.rank_product v l r hg).1 (.left hxv hg),
      hsmall (P.rank_product v l r hg).2 (.right hxv hg)⟩

/-- **The charge at a node.** If the accepted set is `K`-rectangle-free, the descent stops at a
node `v` for at most the budget of `v` inputs. -/
private theorem ncard_stops_le (hS : RectangleFree P.accepted K) (v : N) :
    (P.stops K v).ncard ≤ P.budget K v := by
  by_cases hlarge : K ≤ (P.values v).ncard
  swap
  · simp [stops, hlarge]
  have hout := P.ncard_contexts_le hS hlarge
  cases hg : P.gate v with
  | leaf => simp [stops, hg]
  | union c =>
    -- An input is determined by the child through which it stops, its part on the scope of that
    -- child, and its context.
    let T (u : N) := {x | P.Occurs x v ∧ x ∈ P.accepts u ∧ (P.values u).ncard < K}
    have hcover : P.stops K v ⊆ ⋃ u ∈ c, T u := by
      rintro x ⟨hx, -, hs⟩
      simp only [hg] at hs
      obtain ⟨u, hu, hxu, hsmall⟩ := hs
      exact mem_iUnion₂.mpr ⟨u, hu, hx, hxu, hsmall⟩
    have hT (u : N) (hu : u ∈ c) : (T u).ncard ≤ (K - 1) ^ 2 := by
      by_cases hsmall : (P.values u).ncard < K
      swap
      · simp [T, hsmall]
      calc (T u).ncard
          ≤ (P.values u ×ˢ P.contexts v).ncard := by
            refine ncard_le_ncard_of_injOn
              (fun x => ((P.scope u).domRestrict x, (P.scope v)ᶜ.domRestrict x)) ?_ ?_
              (toFinite _)
            · rintro x ⟨hx, hxu, -⟩
              exact ⟨hxu, x, hx, rfl⟩
            · intro x _ y _ h
              rw [P.scope_union v c hg u hu] at h
              exact domRestrict_prodMk_injective _ h
        _ ≤ (K - 1) ^ 2 := by
            rw [ncard_prod, sq]
            exact Nat.mul_le_mul (by omega) hout
    calc (P.stops K v).ncard
        ≤ (⋃ u ∈ c, T u).ncard := ncard_le_ncard hcover (toFinite _)
      _ ≤ ∑ u ∈ c, (T u).ncard := Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ _u ∈ c, (K - 1) ^ 2 := Finset.sum_le_sum hT
      _ = P.budget K v := by simp [budget, hg, mul_comm]
  | product l r =>
    -- An input is determined by its parts on the scopes of both children and its context.
    by_cases hsmall : (P.values l).ncard < K ∧ (P.values r).ncard < K
    swap
    · simp [stops, hg, hsmall]
    calc (P.stops K v).ncard
        ≤ (P.values l ×ˢ P.values r ×ˢ P.contexts v).ncard := by
          refine ncard_le_ncard_of_injOn
            (fun x => ((P.scope l).domRestrict x, (P.scope r).domRestrict x,
              (P.scope v)ᶜ.domRestrict x)) ?_ ?_ (toFinite _)
          · rintro x ⟨hx, -, -⟩
            have h := (P.values_product v l r hg x).mp hx.accepts
            exact ⟨h.1, h.2, x, hx, rfl⟩
          · intro x _ y _ h
            simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
            refine domRestrict_prodMk_injective (P.scope v) (Prod.ext ?_ ?_)
            · refine domRestrict_eq_domRestrict_iff.mpr fun i hi => ?_
              rw [P.scope_product v l r hg] at hi
              exact hi.elim (fun hil => h.1 hil) fun hir => h.2.1 hir
            · exact domRestrict_eq_domRestrict_iff.mpr h.2.2
      _ ≤ (K - 1) ^ 3 := by
          rw [ncard_prod, ncard_prod, pow_succ', sq]
          exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hout)
      _ = P.budget K v := by simp [budget, hg]

variable [Fintype N]

/-- The number of union edges: the children of each union, a shared child being counted once
for each of its parents. -/
def unionEdges : ℕ :=
  ∑ v, match P.gate v with
    | .union c => c.card
    | _ => 0

/-- The number of products. -/
def products : ℕ :=
  ∑ v, match P.gate v with
    | .product _ _ => 1
    | _ => 0

/-- The size of the DAG: its union edges and its products. Leaves are free. -/
def size : ℕ :=
  P.unionEdges + P.products

/-- **Threshold counting for decomposable DAGs.** If the set represented by a smooth
decomposable DAG is `K`-rectangle-free and has at least `K` elements, then

`|accepted| ≤ (K - 1) ^ 2 · #(union edges) + (K - 1) ^ 3 · #(products)`.

Unions need not be disjoint, and different branches may split the coordinates differently. -/
theorem ncard_accepted_le (hrect : RectangleFree P.accepted K) (hS : K ≤ P.accepted.ncard) :
    P.accepted.ncard ≤ (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products := by
  have hK : 1 < K := hrect.one_lt <| nonempty_of_ncard_ne_zero (by have := hrect.pos; omega)
  calc P.accepted.ncard
      ≤ (⋃ v ∈ (Finset.univ : Finset N), P.stops K v).ncard :=
        ncard_le_ncard (fun x hx => by
          obtain ⟨v, hv⟩ := P.exists_mem_stops hK hS hx
          exact mem_iUnion₂.mpr ⟨v, Finset.mem_univ v, hv⟩) (toFinite _)
    _ ≤ ∑ v, (P.stops K v).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ v, P.budget K v := Finset.sum_le_sum fun v _ => P.ncard_stops_le hrect v
    _ = (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products := by
      simp only [unionEdges, products, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      cases hg : P.gate v <;> simp [budget, hg]

/-- **Threshold counting by size.** If the set represented by a smooth decomposable DAG is
`K`-rectangle-free and has at least `K` elements, then `|accepted| ≤ (K - 1) ^ 3 · size`. -/
theorem ncard_accepted_le_size (hrect : RectangleFree P.accepted K)
    (hS : K ≤ P.accepted.ncard) : P.accepted.ncard ≤ (K - 1) ^ 3 * P.size := by
  have hpow : (K - 1) ^ 2 ≤ (K - 1) ^ 3 := by
    rcases Nat.eq_zero_or_pos (K - 1) with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by omega)
  calc P.accepted.ncard ≤ (K - 1) ^ 2 * P.unionEdges + (K - 1) ^ 3 * P.products :=
        P.ncard_accepted_le hrect hS
    _ ≤ (K - 1) ^ 3 * P.unionEdges + (K - 1) ^ 3 * P.products := by gcongr
    _ = (K - 1) ^ 3 * P.size := by rw [size, mul_add]

end Finite

end DecomposableDAG

end Cslib.Circuits
