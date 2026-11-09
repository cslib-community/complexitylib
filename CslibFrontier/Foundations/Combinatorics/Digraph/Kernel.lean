/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, directed graph kernels)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Absorbing kernels of directed graphs

A kernel contains no arc between selected vertices and absorbs each outside vertex through an
outgoing arc into the selected set. Reversing arcs gives the other convention. No symmetry is
assumed. The definition also makes sense for graphs with loops, although [ChenJiangZhu2027],
Proposition D.5 (PDF p. 37), applies it to loopless digraphs.

## Main definitions

* `Digraph.IsKernel`: an independent outgoing-absorbing vertex set.

## Main results

* `Digraph.isKernel_selection_iff`: exact Boolean selection semantics of arc exclusions and
  outgoing closed-neighborhood coverage.
* `Digraph.card_kernel_selections_eq`: selection codes and original vertex sets have equal counts.
-/

public section

namespace Digraph

/-- An independent set absorbing every outside vertex via an outgoing arc into the set. -/
@[expose] def IsKernel {V : Type*} (G : Digraph V) (S : Set V) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v) ∧ ∀ u, u ∉ S → ∃ v ∈ S, G.Adj u v

/-- No undirected closure is used: the selected neighbor is reached by an outgoing arc. -/
theorem isKernel_selection_iff {V : Type*} (G : Digraph V) (σ : V → Bool) :
    G.IsKernel {u | σ u = true} ↔
      (∀ u v, G.Adj u v → σ u = false ∨ σ v = false) ∧
        ∀ u, σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true := by
  constructor
  · rintro ⟨hi, ha⟩
    constructor
    · intro u v huv
      by_cases hu : σ u = true
      · by_cases hv : σ v = true
        · exact False.elim (hi u hu v hv huv)
        · exact Or.inr (Bool.eq_false_iff.mpr hv)
      · exact Or.inl (Bool.eq_false_iff.mpr hu)
    · intro u
      by_cases hu : σ u = true
      · exact Or.inl hu
      · obtain ⟨v, hv, huv⟩ := ha u hu
        exact Or.inr ⟨v, huv, hv⟩
  · rintro ⟨hi, ha⟩
    constructor
    · intro u hu v hv huv
      rcases hi u v huv with h | h <;> simp_all
    · intro u hu
      rcases ha u with h | ⟨v, huv, hv⟩
      · exact False.elim (hu h)
      · exact ⟨v, hv, huv⟩

open Classical in
/-- Boolean selection codes count vertex sets exactly, without multiple representations. -/
theorem card_kernel_selections_eq {V : Type*} [Fintype V] (G : Digraph V) :
    Fintype.card {σ : V → Bool // G.IsKernel {u | σ u = true}} =
      Fintype.card {S : Set V // G.IsKernel S} := by
  let f : {σ : V → Bool // G.IsKernel {u | σ u = true}} →
      {S : Set V // G.IsKernel S} := fun σ => ⟨{u | σ.val u = true}, σ.property⟩
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro x y h
    apply Subtype.ext
    funext u
    have he := Set.ext_iff.mp (congrArg Subtype.val h) u
    change (x.val u = true) ↔ (y.val u = true) at he
    cases hx : x.val u <;> cases hy : y.val u <;> simp_all
  · intro S
    have he : {u | decide (u ∈ S.val) = true} = S.val := by ext u; simp
    refine ⟨⟨fun u => decide (u ∈ S.val), ?_⟩, ?_⟩
    · rw [he]
      exact S.property
    · exact Subtype.ext he

end Digraph
