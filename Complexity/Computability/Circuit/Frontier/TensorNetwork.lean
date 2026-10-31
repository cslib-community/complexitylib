/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Multigraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Tensor networks and their contraction

A *tensor network* over a commutative semiring `R` and an alphabet `U` is a multigraph whose
edges carry values in `U`, with a *tensor* at each vertex `v`: a value `N.tensor v x ∈ R` for each
assignment `x : E → U` of values to the edges, which depends only on the values on the edges at
`v`. Its *contraction* sums, over all assignments, the product of the tensors:

  `Z(N) = ∑ x : E → U, ∏ v, N.tensor v x`.

A *Boolean* tensor network has `U = Bool`, one bit per edge. The usual presentation gives the
tensor at `v` as a function `F_v` of the bits on the ordered list `δ(v)` of edges at `v`, with
`Z = ∑ x ∏ v F_v (x|δ(v))`. Here the tensor is a function of the whole assignment, constrained to
read only the edges at `v` (`TensorNetwork.tensor_congr`); the ordered presentation, with
explicit tables, is `Cslib.Circuits.Frontier.ExplicitTensorNetwork`, and
`Cslib.Circuits.Frontier.TensorNetwork.contraction_toExplicit` shows that the two contractions
agree. Parallel edges are distinct elements of `E` and so give distinct ports.

A tensor network is the weighted form of a constraint network
(`Cslib.Circuits.Frontier.Network`) on a fixed input: the two share the multigraph and the
locality condition, and a constraint becomes its `0`–`1` indicator tensor, whose contraction
counts the satisfying assignments
(`Cslib.Circuits.Frontier.Network.contraction_toTensorNetwork`).

**Subdivision** (`TensorNetwork.subdivide`). Splitting every edge `e` into two edges joined at a
new vertex that carries the *equality tensor* `[y₁ = y₂]` preserves the contraction
(`TensorNetwork.contraction_subdivide`): each assignment of the old network extends in exactly one
way to an assignment of the new one with nonzero weight. The subdivided network is bipartite
(`TensorNetwork.isBipartite_subdivide`), with the old vertices on one side and the new ones on the
other, and it keeps the degree bound of a loopless network (`TensorNetwork.maxDegreeLE_subdivide`).
It has twice as many edges and one new vertex per old edge.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.IsBipartite`: the vertices split into two sides and every
  edge joins the two sides.
* `Cslib.Circuits.Frontier.TensorNetwork`: a tensor network.
* `Cslib.Circuits.Frontier.TensorNetwork.contraction`: its contraction `Z`.
* `Cslib.Circuits.Frontier.TensorNetwork.subdivide`: subdivision of every edge by an equality
  tensor.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.isBipartite_iff`: a multigraph is bipartite iff it has no
  loops and its underlying simple graph is bipartite (`SimpleGraph.IsBipartite`).
* `Cslib.Circuits.Frontier.TensorNetwork.contraction_subdivide`: subdivision preserves the
  contraction.
* `Cslib.Circuits.Frontier.TensorNetwork.isBipartite_subdivide`: a subdivided network is
  bipartite.
* `Cslib.Circuits.Frontier.TensorNetwork.maxDegreeLE_subdivide`: subdividing a loopless network of
  maximum degree at most `d ≥ 2` gives maximum degree at most `d`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53) and
  the subdivision step of Appendix D.2 (p. 54).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-! ### Bipartite multigraphs -/

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- A multigraph is *bipartite* when its vertices split into two sides, `side v = true` and
`side v = false`, and every edge joins the two sides. A bipartite multigraph has no loops
(`Multigraph.IsBipartite.loopless`). -/
def IsBipartite : Prop :=
  ∃ side : V → Bool, ∀ e, side (G.src e) ≠ side (G.tgt e)

variable {G}

/-- A bipartite multigraph has no loops. -/
theorem IsBipartite.loopless (h : G.IsBipartite) : G.Loopless := by
  obtain ⟨side, hside⟩ := h
  exact fun e he => hside e (congrArg side he)

/-- A multigraph is bipartite exactly when it has no loops and its underlying simple graph is
bipartite in the sense of Mathlib (`SimpleGraph.IsBipartite`, a `2`-colouring). -/
theorem isBipartite_iff : G.IsBipartite ↔ G.Loopless ∧ G.toSimpleGraph.IsBipartite := by
  constructor
  · intro h
    refine ⟨h.loopless, ?_⟩
    obtain ⟨side, hside⟩ := h
    have hcol : G.toSimpleGraph.Coloring Bool := SimpleGraph.Coloring.mk side fun {u v} huv => by
      obtain ⟨-, e, he⟩ := toSimpleGraph_adj.mp huv
      rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact hu ▸ hv ▸ hside e
      · exact hu ▸ hv ▸ (hside e).symm
    simpa using hcol.colorable
  · rintro ⟨hloop, ⟨c⟩⟩
    refine ⟨fun v => decide (c v = 0), fun e he => ?_⟩
    have hadj : G.toSimpleGraph.Adj (G.src e) (G.tgt e) := toSimpleGraph_adj.mpr ⟨hloop e, e, rfl⟩
    have key : ∀ a b : Fin 2, a ≠ b → decide (a = 0) ≠ decide (b = 0) := by decide
    exact key _ _ (c.valid hadj) he

end Multigraph

/-! ### Tensor networks -/

/-- A *tensor network* over the commutative semiring `R` with alphabet `U`: a multigraph on the
vertices `V` and edges `E`, whose edges carry values in `U`, and at each vertex a *tensor*, a value
in `R` for each assignment of values to the edges, that sees only the values on the edges at that
vertex. A *Boolean* tensor network has `U = Bool`. -/
structure TensorNetwork (R U V E : Type*) extends Multigraph V E where
  /-- The tensor at a vertex: its value on an assignment of values to the edges. -/
  tensor : V → (E → U) → R
  /-- Tensors are local: the tensor at `v` sees only the values on the edges incident to `v`. -/
  tensor_congr : ∀ v x y, (∀ e, src e = v ∨ tgt e = v → x e = y e) → tensor v x = tensor v y

namespace TensorNetwork

variable {R U V E : Type*}

section Contraction

variable [CommSemiring R] [Fintype U] [Fintype V] [Fintype E] [DecidableEq E]

/-- The *contraction* of a tensor network: the sum over all assignments of values to the edges of
the product of the tensors at all vertices. -/
def contraction (N : TensorNetwork R U V E) : R :=
  ∑ x : E → U, ∏ v, N.tensor v x

end Contraction

/-! ### Subdivision by equality tensors -/

section Subdivide

variable [DecidableEq U] [DecidableEq V] [Zero R] [One R] (N : TensorNetwork R U V E)

/-- The *subdivision* of a tensor network by equality tensors. Each edge `e` becomes a new vertex
`Sum.inr e` and two edges: `Sum.inl e`, from the source of `e`, and `Sum.inr e`, from its target,
both ending at `Sum.inr e`. The new vertex carries the *equality tensor*, one when its two edges
carry the same value and zero otherwise. An old vertex reads the value of `e` on the half of `e`
at its end. -/
def subdivide : TensorNetwork R U (V ⊕ E) (E ⊕ E) where
  src := Sum.elim (fun e => .inl (N.src e)) (fun e => .inl (N.tgt e))
  tgt := Sum.elim .inr .inr
  tensor
    | .inl v, y => N.tensor v fun e => if N.src e = v then y (.inl e) else y (.inr e)
    | .inr e, y => if y (.inl e) = y (.inr e) then 1 else 0
  tensor_congr := by
    rintro (v | e) y y' h
    · refine N.tensor_congr v _ _ fun e he => ?_
      by_cases hs : N.src e = v
      · simp only [hs, ite_true]
        exact h (.inl e) (Or.inl (by simp [hs]))
      · simp only [hs, ite_false]
        exact h (.inr e) (Or.inl (by simp [he.resolve_left hs]))
    · simp only
      rw [h (.inl e) (Or.inr rfl), h (.inr e) (Or.inr rfl)]

@[simp] theorem subdivide_src_inl (e : E) : N.subdivide.src (.inl e) = .inl (N.src e) := rfl

@[simp] theorem subdivide_src_inr (e : E) : N.subdivide.src (.inr e) = .inl (N.tgt e) := rfl

@[simp] theorem subdivide_tgt_inl (e : E) : N.subdivide.tgt (.inl e) = .inr e := rfl

@[simp] theorem subdivide_tgt_inr (e : E) : N.subdivide.tgt (.inr e) = .inr e := rfl

/-- The tensor at an old vertex of the subdivision. -/
theorem subdivide_tensor_inl (v : V) (y : E ⊕ E → U) :
    N.subdivide.tensor (.inl v) y =
      N.tensor v fun e => if N.src e = v then y (.inl e) else y (.inr e) := rfl

/-- The equality tensor at a new vertex of the subdivision. -/
theorem subdivide_tensor_inr (e : E) (y : E ⊕ E → U) :
    N.subdivide.tensor (.inr e) y = if y (.inl e) = y (.inr e) then 1 else 0 := rfl

/-- **Subdivision is bipartite.** Every edge of the subdivision joins an old vertex to a new one. -/
theorem isBipartite_subdivide : N.subdivide.IsBipartite :=
  ⟨Sum.isLeft, fun e => by cases e <;> simp⟩

/-- **Subdivision preserves the contraction.** An assignment of the subdivision has nonzero
weight only when the two halves of every edge carry the same value, and such assignments are
exactly the assignments of the original network. -/
theorem contraction_subdivide {R : Type*} [CommSemiring R] [Fintype U] [Fintype V] [Fintype E]
    [DecidableEq E] (N : TensorNetwork R U V E) : N.subdivide.contraction = N.contraction := by
  classical
  -- Split an assignment of the subdivision into its values `a` on the source halves and `b` on
  -- the target halves.
  rw [contraction, contraction, ← (Equiv.sumArrowEquivProdArrow E E U).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fintype.prod_sum_type, subdivide_tensor_inl, subdivide_tensor_inr,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  rw [Finset.sum_eq_single a]
  · -- Equal halves: every equality tensor is one, and the old vertices read `a`.
    simp only [ite_self, ite_true, Finset.prod_const_one, mul_one]
  · -- Unequal halves on some edge `e`: the equality tensor at `e` vanishes.
    intro b _ hb
    obtain ⟨e, he⟩ := Function.ne_iff.mp hb
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right fun h => he h.symm))
  · exact fun h => absurd (Finset.mem_univ a) h

/-- The edges at an old vertex of the subdivision are the halves of its old edges at it. -/
theorem incidenceSet_subdivide_inl (v : V) :
    N.subdivide.incidenceSet (.inl v) =
      Sum.inl '' {e | N.src e = v} ∪ Sum.inr '' {e | N.tgt e = v} := by
  ext (e | e) <;> simp [Multigraph.mem_incidenceSet]

/-- The edges at a new vertex of the subdivision are the two halves of its edge. -/
theorem incidenceSet_subdivide_inr (e : E) :
    N.subdivide.incidenceSet (.inr e) = {.inl e, .inr e} := by
  ext (e' | e') <;> simp [Multigraph.mem_incidenceSet, eq_comm]

/-- **Subdivision keeps the degree bound.** In a loopless network, the edges at a vertex are those
with it as source and those with it as target, and they are the halves at its old vertex in the
subdivision; a new vertex has degree two. -/
theorem maxDegreeLE_subdivide [Finite E] {d : ℕ} (hloop : N.Loopless)
    (hd : N.MaxDegreeLE d) (h2 : 2 ≤ d) : N.subdivide.MaxDegreeLE d := by
  rintro (v | e)
  · rw [incidenceSet_subdivide_inl, ncard_union_eq _ (toFinite _) (toFinite _),
      ncard_image_of_injective _ Sum.inl_injective, ncard_image_of_injective _ Sum.inr_injective,
      ← ncard_union_eq _ (toFinite _) (toFinite _)]
    · exact hd v
    · exact disjoint_left.mpr fun e hs ht => hloop e (hs.trans ht.symm)
    · exact disjoint_left.mpr fun _ ⟨_, _, h⟩ ⟨_, _, h'⟩ => Sum.inl_ne_inr (h.trans h'.symm)
  · rw [incidenceSet_subdivide_inr, ncard_pair Sum.inl_ne_inr]
    exact h2

end Subdivide

end TensorNetwork

end Cslib.Circuits.Frontier
