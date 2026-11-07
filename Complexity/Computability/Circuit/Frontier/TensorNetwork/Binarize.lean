/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork
public import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Card

/-!
# Binarizing a tensor network

A tensor network whose edges carry letters of a finite alphabet `U` becomes a Boolean tensor
network once every letter is written in `m` bits. Fix an injective *code*
`code : U → (Fin m → Bool)`. The *binarization* `TensorNetwork.binarize` replaces every edge `e`
by the `m` parallel Boolean edges `(e, 0), …, (e, m - 1)` between the same two vertices. A vertex
decodes the `m` bits on each of its edges and evaluates its old tensor on the decoded letters; if
the bits on one of its edges are not the code of any letter, its tensor is zero.

The contraction is unchanged (`TensorNetwork.contraction_binarize`): assignments of bits in which
every edge carries a code word correspond exactly to assignments of letters, and every other
assignment of bits has an edge with an invalid code word, whose source tensor vanishes. Every edge
becomes `m` edges, so vertex degrees are multiplied by `m`
(`TensorNetwork.maxDegreeLE_binarize`). Every tensor entry of the binarization is zero or an entry
of the original network (`TensorNetwork.tensor_binarize_eq_zero_or`). Loops and bipartiteness are
preserved.

This lets a construction use a structured alphabet, such as words over a machine's tape alphabet,
and then pass to the Boolean networks of [OpenAI2026ETH], Appendix D.

## Main definitions

* `Cslib.Circuits.Frontier.TensorNetwork.binarize`: the binarization by a code.
* `Cslib.Circuits.Frontier.TensorNetwork.bitsOn`: the bits on the copies of an edge.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.contraction_binarize`: binarization by an injective code
  preserves the contraction.
* `Cslib.Circuits.Frontier.TensorNetwork.maxDegreeLE_binarize`: degrees are multiplied by the
  code length.
* `Cslib.Circuits.Frontier.TensorNetwork.loopless_binarize`,
  `Cslib.Circuits.Frontier.TensorNetwork.isBipartite_binarize`: loops and bipartiteness are
  preserved.
* `Cslib.Circuits.Frontier.TensorNetwork.tensor_binarize_eq_zero_or`: binarized entries are zero
  or original entries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier.TensorNetwork

open Function

variable {R U V E : Type*} {m : ℕ}

/-- The bits on the `m` copies of the edge `e`. -/
@[expose] def bitsOn (y : E × Fin m → Bool) (e : E) : Fin m → Bool :=
  fun j => y (e, j)

@[simp] theorem bitsOn_apply (y : E × Fin m → Bool) (e : E) (j : Fin m) :
    bitsOn y e j = y (e, j) := rfl

variable [Zero R] [Nonempty U] (N : TensorNetwork R U V E) (code : U → Fin m → Bool)

open Classical in
/-- The *binarization* of a tensor network by a code `code : U → (Fin m → Bool)`. Every edge `e`
becomes the `m` Boolean edges `(e, j)` between the same two vertices. A vertex whose edges all
carry code words evaluates its old tensor on the decoded letters (`Function.invFun code`); a
vertex with an edge carrying a word that is not a code word has tensor zero. -/
@[expose] noncomputable def binarize : TensorNetwork R Bool V (E × Fin m) where
  src p := N.src p.1
  tgt p := N.tgt p.1
  tensor v y :=
    if ∀ e, N.src e = v ∨ N.tgt e = v → bitsOn y e ∈ Set.range code then
      N.tensor v fun e => invFun code (bitsOn y e)
    else 0
  tensor_congr v y y' h := by
    have hrow : ∀ e, N.src e = v ∨ N.tgt e = v → bitsOn y e = bitsOn y' e :=
      fun e he => funext fun j => h (e, j) he
    have hcond : (∀ e, N.src e = v ∨ N.tgt e = v → bitsOn y e ∈ Set.range code) ↔
        ∀ e, N.src e = v ∨ N.tgt e = v → bitsOn y' e ∈ Set.range code :=
      forall_congr' fun e => imp_congr_right fun he => by rw [hrow e he]
    simp only [hcond]
    split_ifs
    · exact N.tensor_congr v _ _ fun e he => by rw [hrow e he]
    · rfl

@[simp] theorem binarize_src (p : E × Fin m) : (N.binarize code).src p = N.src p.1 := rfl

@[simp] theorem binarize_tgt (p : E × Fin m) : (N.binarize code).tgt p = N.tgt p.1 := rfl

/-- Every tensor entry of the binarization is zero or an entry of the original network at some
assignment of letters. -/
theorem tensor_binarize_eq_zero_or (v : V) (y : E × Fin m → Bool) :
    (N.binarize code).tensor v y = 0 ∨ ∃ x, (N.binarize code).tensor v y = N.tensor v x := by
  classical
  simp only [binarize]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- Binarization keeps a network without loops loopless. -/
theorem loopless_binarize (h : N.Loopless) : (N.binarize code).Loopless :=
  fun p => h p.1

/-- Binarization keeps a network bipartite, with the same sides. -/
theorem isBipartite_binarize (h : N.IsBipartite) : (N.binarize code).IsBipartite := by
  obtain ⟨side, hside⟩ := h
  exact ⟨side, fun p => hside p.1⟩

/-- The edges at a vertex of the binarization are the copies of its old edges. -/
theorem incidenceSet_binarize (v : V) :
    (N.binarize code).incidenceSet v = N.incidenceSet v ×ˢ Set.univ := by
  ext p
  simp [Multigraph.mem_incidenceSet]

/-- **Binarization multiplies degrees by the code length.** -/
theorem maxDegreeLE_binarize [Finite E] {d : ℕ} (hd : N.MaxDegreeLE d) :
    (N.binarize code).MaxDegreeLE (d * m) := by
  intro v
  rw [incidenceSet_binarize, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  exact Nat.mul_le_mul_right m (hd v)

/-- **Binarization preserves the contraction.** Assignments of bits in which every edge carries a
code word are the codes of the assignments of letters, and every other assignment of bits has an
edge with an invalid word, at whose source the tensor vanishes. -/
theorem contraction_binarize {R : Type*} [CommSemiring R] [Fintype U] [Fintype V] [Fintype E]
    [DecidableEq E] (N : TensorNetwork R U V E) {code : U → Fin m → Bool}
    (hcode : Injective code) : (N.binarize code).contraction = N.contraction := by
  classical
  symm
  refine Fintype.sum_of_injective (fun x p => code (x p.1) p.2) ?_ _ _ ?_ fun x => ?_
  · -- Distinct assignments of letters differ at some edge, so their codes differ there.
    intro x x' hxx'
    funext e
    exact hcode (funext fun j => congrFun hxx' (e, j))
  · -- A word on some edge is not a code word, so the tensor at its source vanishes.
    intro y hy
    have : ∃ e, bitsOn y e ∉ Set.range code := by
      by_contra! hall
      exact hy ⟨fun e => invFun code (bitsOn y e), funext fun p =>
        congrFun (invFun_eq (hall p.1)) p.2⟩
    obtain ⟨e, he⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ (N.src e)) ?_
    simp only [binarize]
    rw [ite_eq_right fun hall => he (hall e (Or.inl rfl))]
  · -- On a code word everywhere, every vertex decodes the original assignment.
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [binarize]
    rw [ite_eq_left fun e _ => ⟨x e, rfl⟩]
    congr 1
    funext e
    exact (leftInverse_invFun hcode (x e)).symm

end Cslib.Circuits.Frontier.TensorNetwork
